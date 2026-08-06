import Clean.Circuit
import Clean.Utils.Bits
import Mathlib.Tactic.LinearCombination
import Challenge.Utils.ComputableWitnessLemmas
import Challenge.Instances.AssertBytes.Interface

/-!
# `ByteCheck` gadget — 7-bit decomposition byte range check

`ByteCheck` is a `FormalAssertion` on a single field element `x`: it witnesses
the 7 *low* bits of `x`, boolean-constrains each of them, and asserts
`(x - s) * (x - s - 128) = 0` where `s = Σ bitᵢ · 2ⁱ` is the (affine) low-bit
recomposition. The final constraint forces `x = s` or `x = s + 128`; since the
booleanity constraints force `s.val < 128`, either case gives `x.val < 256`.

Compared to the classic `Num2Bits 8` (8 allocations, 9 constraints), this saves
one allocation and one constraint per element: the top bit is never allocated —
it is implicitly `(x - s) / 128` — and the product constraint is exactly its
booleanity check, which also subsumes the recomposition row.
-/

namespace Solution.AssertBytes
namespace ByteCheck

open Challenge.Instances.AssertBytes.Interface
open Utils.Bits

/-- The `main` circuit: witness the 7 low bits of `x`, boolean-constrain each
(`bit · (bit − 1) = 0`), and assert `(x − s)·(x − s − 128) = 0` for the
recomposition `s` of the low bits. No output (it is an assertion). -/
def main (x : Expression (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let bits ← witnessVector 7 (fun env => fieldToBits 7 (x.eval env))
  Circuit.forEach bits (fun b => assertZero (b * (b - 1)))
  assertZero ((x - fieldFromBitsExpr bits) * (x - fieldFromBitsExpr bits - 128))

instance elaborated : ElaboratedCircuit (F circomPrime) field unit main := by
  elaborate_circuit

/-- No preconditions: the assertion is sound on arbitrary `x`. -/
def Assumptions (_x : F circomPrime) : Prop := True

/-- Postcondition: `x` is a byte (`x.val < 256`). -/
def Spec (x : F circomPrime) : Prop := x.val < 256

private lemma val_128 : (128 : F circomPrime).val = 128 := by
  rw [show (128 : F circomPrime) = ((128 : ℕ) : F circomPrime) by norm_cast,
    ZMod.val_natCast_of_lt (by unfold circomPrime; norm_num)]

private lemma p_large : (256 : ℕ) < circomPrime := by unfold circomPrime; norm_num

theorem soundness :
    FormalAssertion.Soundness (Input := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  obtain ⟨h_bool, h_eq⟩ := h_holds
  set bit_vars : Vector (Expression (F circomPrime)) 7 :=
    Vector.mapRange 7 (fun i => var ⟨i₀ + i⟩) with hbv
  -- each evaluated bit reads back the witness cell at `i₀ + i`
  have hval : ∀ (i : ℕ) (hi : i < 7), (bit_vars.map env)[i] = env.get (i₀ + i) := by
    intro i hi
    simp only [hbv, Vector.getElem_map, Vector.getElem_mapRange]
    rfl
  -- the booleanity constraints force each evaluated bit to be 0 or 1
  have h_bits : ∀ (i : ℕ) (hi : i < 7),
      (bit_vars.map env)[i] = 0 ∨ (bit_vars.map env)[i] = 1 := by
    intro i hi
    rw [hval i hi]
    rcases mul_eq_zero.mp (h_bool ⟨i, hi⟩) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (add_neg_eq_zero.mp h1)
  -- rewrite the product constraint in terms of the recomposed field element
  have h_eval : Expression.eval env (fieldFromBitsExpr bit_vars)
      = fieldFromBits (bit_vars.map env) := fieldFromBits_eval bit_vars
  rw [h_eval] at h_eq
  -- the recomposition of 7 boolean bits is < 128
  have hs_lt : (fieldFromBits (bit_vars.map env)).val < 128 :=
    lt_of_lt_of_le (fieldFromBits_lt (bit_vars.map env) h_bits) (by norm_num)
  set s : F circomPrime := fieldFromBits (bit_vars.map env) with hs
  have h256 := p_large
  -- the product constraint pins `input` to `s` or `s + 128`
  rcases mul_eq_zero.mp h_eq with h | h
  · -- `input = s`, so `input.val < 128 < 256`
    rw [add_neg_eq_zero.mp h]
    omega
  · -- `input = s + 128`, so `input.val = s.val + 128 < 256`
    have hi : (input : F circomPrime) = s + 128 := by linear_combination h
    have hb := val_128
    have hadd : (s + 128 : F circomPrime).val = s.val + 128 := by
      have := ZMod.val_add_of_lt (a := s) (b := (128 : F circomPrime)) (by omega)
      omega
    rw [hi, hadd]
    omega

theorem completeness :
    FormalAssertion.Completeness (Input := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  set bit_vars : Vector (Expression (F circomPrime)) 7 :=
    Vector.mapRange 7 (fun i => var ⟨i₀ + i⟩) with hbv
  refine ⟨?_, ?_⟩
  · -- booleanity: every witnessed bit is one of `fieldToBits`'s 0/1 entries
    intro i
    rw [h_env i]
    rcases @fieldToBits_bits circomPrime _ 7 input i.val i.isLt with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring
  · -- product constraint: the witnessed low bits recompose to `input.val % 128`,
    -- so one of the two factors vanishes
    have he : Expression.eval env.toEnvironment (fieldFromBitsExpr bit_vars)
        = fieldFromBits (bit_vars.map env.toEnvironment) := fieldFromBits_eval bit_vars
    have hmap : bit_vars.map env.toEnvironment = fieldToBits 7 input := by
      apply Vector.ext
      intro i hi
      rw [hbv, Vector.getElem_map, Vector.getElem_mapRange]
      simpa using h_env ⟨i, hi⟩
    by_cases hcase : @ZMod.val circomPrime input < 128
    · -- low half: the recomposition is `input` itself, the first factor vanishes
      have h7 : @ZMod.val circomPrime input < 2 ^ 7 :=
        lt_of_lt_of_le hcase (by norm_num)
      rw [he, hmap, @fieldFromBits_fieldToBits circomPrime _ 7 input h7]
      ring
    · -- high half: the recomposition is `input - 128`, the second factor vanishes
      push_neg at hcase
      have hmodeq : @ZMod.val circomPrime input % 2 ^ 7
          = @ZMod.val circomPrime input - 128 := by
        rw [show (2 : ℕ) ^ 7 = 128 from by norm_num]
        omega
      rw [he, hmap, @fieldFromBits_fieldToBits_mod circomPrime _ 7 input, hmodeq,
        Nat.cast_sub hcase, ZMod.natCast_zmod_val]
      push_cast
      ring

def circuit : FormalAssertion (F circomPrime) field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

/-- The only witness generator is `fieldToBits 7` applied to the evaluated
input, so every witness cell is computable from cells below the input's
accessed range. Same structural argument as the baseline `Num2Bits`. -/
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset x env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition x env env')
    ((main x).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    and_true, implies_true]
  -- only the witness-generator obligation survives; it reads only `x`
  intro _ h_input
  have h_eval : Expression.eval env.toEnvironment x =
      Expression.eval env'.toEnvironment x := by
    rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at h_input
    exact h_input
  simpa using congrArg (fieldToBits 7) h_eval

end ByteCheck
end Solution.AssertBytes
