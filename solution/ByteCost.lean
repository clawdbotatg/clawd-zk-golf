import Clean.Utils.Bits
import Clean.Circuit.Loops
import Challenge.Utils.CostR1CS
import Solution.AssertBytes.ByteCheck
import Challenge.Instances.AssertBytes.Interface

/-!
# Compositional cost (`CostIs`) and R1CS (`IsR1CSCirc`) facts for `ByteCheck`

Bottom-up `operationCount` / `operationsIsR1CS` certificates for the per-element
`ByteCheck` byte range check (7 low-bit allocations, 7 booleanity rows, and one
`(x−s)·(x−s−128)` product row), proved with the compositional lemmas in
`Challenge.CostR1CS` (no `native_decide`, no large `decide`).
-/

namespace Solution.AssertBytes
namespace ByteCost

open Challenge.Instances.AssertBytes.Interface
open Challenge.CostR1CS
open Utils.Bits

/-- A `forEach` is single-row R1CS when each *indexed* body is, so the certificate
can use that `xs[i]` is affine (the generic `IsR1CSCirc.forEach` quantifies over
all element values, too weak for booleanity rows). -/
theorem IsR1CSCirc.forEach_mem {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

/-- `ByteCheck.main x` witnesses 7 bits (`⟨7, 0⟩`), boolean-constrains each
(`⟨0, 7⟩`), and asserts the product row (`⟨0, 1⟩`): total `⟨7, 8⟩`. -/
theorem costIs_byteCheck (x : Expression (F circomPrime)) :
    CostIs (ByteCheck.main x) ⟨7, 8⟩ := by
  unfold ByteCheck.main
  have hcount : (⟨7, 0⟩ + (⟨7 * 0, 7 * 1⟩ + ⟨0, 1⟩) : Count) = ⟨7, 8⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) 7 _) fun bits => ?_
  refine CostIs.bind (CostIs.forEach fun b m => CostIs.assertZero (b * (b - 1)) m) fun _ => ?_
  exact CostIs.assertZero _

/-- `fieldFromBitsExpr` over an affine bit-vector is affine. -/
theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (fieldFromBitsExpr bits) := by
  unfold fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- `ByteCheck.main x` is single-row R1CS when `x` is affine: each booleanity row
`bit·(bit−1)` and the product row `(x−s)·(x−s−128)` are rank-1 rows, since the
recomposition `s` is affine in the witnessed bits. -/
theorem isR1CS_byteCheck (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (ByteCheck.main x) := by
  unfold ByteCheck.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 7 _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- booleanity loop: each `bit · (bit - 1)` is a single rank-1 row
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output 7 _ w i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output 7 _ w i.val i.isLt) (Affine.const 1))
  · -- product row: both factors are affine
    refine IsR1CSCirc.assertZero ?_
    exact isR1CSRow_mul
      (Affine.sub hx (affine_fieldFromBitsExpr ((Circuit.witnessVector 7 _).output w)
        (affineW_witnessVector_output 7 _ w)))
      (Affine.sub (Affine.sub hx (affine_fieldFromBitsExpr ((Circuit.witnessVector 7 _).output w)
        (affineW_witnessVector_output 7 _ w))) (Affine.const 128))

/-- The `ByteCheck` assertion invoked on `x` costs `⟨7, 8⟩`. -/
theorem costIs_assertion_byteCheck (x : Expression (F circomPrime)) :
    CostIs (assertion ByteCheck.circuit x) ⟨7, 8⟩ :=
  CostIs.assertion (fun m => costIs_byteCheck x m)

theorem isR1CS_assertion_byteCheck (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion ByteCheck.circuit x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_byteCheck x hx m)

end ByteCost
end Solution.AssertBytes
