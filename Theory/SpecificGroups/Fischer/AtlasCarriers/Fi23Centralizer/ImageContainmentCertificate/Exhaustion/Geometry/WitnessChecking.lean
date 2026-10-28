module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Checking
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions.Checker
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleListDecoding

/-!
# Exact cycle comparison for the eight centralizer witnesses

Disjoint support masks and inverse-cycle checks identify each proposed action
with the original string-decoded permutation. Checks on all letters certify
its fixed complement and commutation with the already identified candidate.
The adapters keep permutation application abstract to avoid unfolding the
large original cycle tables during the algebraic proof.
Source: the unchanged `ImageContainmentCertificate/source/centralizer-data.g`,
for the centralizer in GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry
open AtlasCarriers
open KernelCertificate KernelCertificate.FixedLetterCheck
open Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
open GeneratorLiftCertificate

theorem decode_of_blocks
    {blocks : List String} {parts : List (List (List (Fin 31671)))}
    (h : List.Forall₂ (fun b p => decodeCycleBlocks 31671 [b] = p) blocks parts) :
    decodeCycleBlocks 31671 blocks = parts.flatten := by
  induction h with
  | nil => rfl
  | @cons b p bs ps hb _ ih =>
    change _ = p ++ ps.flatten
    rw [← hb, ← ih]
    simp only [decodeCycleBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]

def WitnessCheck (f : Fin 31671 → Fin 31671) (m : Nat) (x : Fin 31671) : Prop :=
  (m.testBit x.val = true ∨ f x = x) ∧
  f (candidateMap x) = candidateMap (f x)

instance (f : Fin 31671 → Fin 31671) (m : Nat) (x : Fin 31671) :
    Decidable (WitnessCheck f m x) := inferInstanceAs (Decidable (_ ∧ _))

theorem witness_action_of_checks (blocks : List String)
    (parts : List (List (List (Fin 31671)))) (ms : List Nat)
    (f : Fin 31671 → Fin 31671)
    (hdecode : List.Forall₂ (fun b p => decodeCycleBlocks 31671 [b] = p) blocks parts)
    (hsupport : List.Forall₂ (fun cs m => Certificate cs.flatten m) parts ms)
    (hdisjoint : disjointMasks ms = true)
    (hcycles : parts.all (cycleTest f) = true)
    (hpoints : ∀ x, WitnessCheck f (unionMasks ms) x) (x : Fin 31671) :
    permutationFromCycleBlocks 31671 blocks x = f x := by
  rw [permutationFromCycleBlocks, decode_of_blocks hdecode, ← cyclesInv_eq]
  apply cyclesInv_eq_of_tests f _ _ (certify_blocks parts ms hsupport hdisjoint)
    (blockTests_sound f parts hcycles)
  intro y hy
  exact ((hpoints y).1).resolve_left (by simp [hy])

theorem commute_of_actions (p q : Equiv.Perm (Fin 31671))
    (f g : Fin 31671 → Fin 31671) (hp : ∀ x, p x = f x) (hq : ∀ x, q x = g x)
    (h : ∀ x, f (g x) = g (f x)) : p * q = q * p := by
  apply Equiv.ext
  intro x
  simpa only [Equiv.Perm.mul_apply, hp, hq] using h x

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry
