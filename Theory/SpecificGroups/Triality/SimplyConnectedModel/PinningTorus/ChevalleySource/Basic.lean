module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.Weyl
public import Theory.AlgebraicGroup.RootData.Chevalley

/-!
# The literal Chevalley root, normalizer and coroot maps for Spin D4

The data uses the existing root points and original defining words. Their
parametrization, additive, multiplicative and reflection laws are checked
against the actual root datum. Torus conjugation follows from the proved
root-character and cocharacter realization. No Chevalley existence theorem
is used. Source: GLS3 1.12.1.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.SimplyConnected.Pinning.ChevalleySource
@[expose] public noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def data : ChevalleyData (groupVariety k) (pinnedRootData k) where
  x r := rootPoint k r.down
  n r := normalizerWord k r.down
  h r := corootWord k r.down

theorem parametrizes (r : (pinnedRootData k).Root) :
    Function.Injective ((data k).x r) ∧ Set.range ((data k).x r) =
      (pinnedRootData k).rootSubgroup r := by
  refine ⟨rootPoint_injective k r.down, ?_⟩
  ext x
  exact (mem_rootClosedSubgroup_iff k r.down x).symm

theorem normalizer_word (r : (pinnedRootData k).Root) (t : kˣ) :
    (data k).n r t = (data k).x r t * (data k).x ((pinnedRootData k).neg r)
      (-((t:k)⁻¹)) * (data k).x r t := by
  change normalizerWord k r.down t = rootPoint k r.down t *
    rootPoint k (((pinnedRootData k).neg r).down) (-((t:k)⁻¹)) * rootPoint k r.down t
  have h := pinnedRootData_neg k r.down
  change (pinnedRootData k).neg r = ULift.up (negativeRoot r.down) at h
  rw [h]
  rfl

theorem coroot_word (r : (pinnedRootData k).Root) (t : kˣ) :
    (data k).h r t = ((data k).n r 1)⁻¹ * (data k).n r t := rfl

theorem root_addition (r : (pinnedRootData k).Root) (a b : k) :
    (data k).x r a * (data k).x r b = (data k).x r (a+b) :=
  (rootPoint_add k r.down a b).symm

theorem coroots_commute (r s : (pinnedRootData k).Root) (t u : kˣ) :
    (data k).h r t * (data k).h s u = (data k).h s u * (data k).h r t :=
  (corootWord_commute k r.down s.down t u).eq

theorem coroot_multiplication (r : (pinnedRootData k).Root) (t u : kˣ) :
    (data k).h r t * (data k).h r u = (data k).h r (t*u) :=
  (corootWord_mul k r.down t u).symm

theorem reflection_root (r s : (pinnedRootData k).Root) (a : k) :
    ((data k).n s 1)⁻¹ * (data k).x r a * (data k).n s 1 =
      (data k).x ((pinnedRootData k).reflect s r) a :=
  normalizer_root_conjugation k r.down s.down a

theorem reflection_normalizer (r s : (pinnedRootData k).Root) (t : kˣ) :
    ((data k).n s 1)⁻¹ * (data k).n r t * (data k).n s 1 =
      (data k).n ((pinnedRootData k).reflect s r) t :=
  normalizer_normalizer_conjugation k r.down s.down t

theorem reflection_coroot (r s : (pinnedRootData k).Root) (t : kˣ) :
    ((data k).n s 1)⁻¹ * (data k).h r t * (data k).n s 1 =
      (data k).h ((pinnedRootData k).reflect s r) t :=
  normalizer_coroot_conjugation k r.down s.down t

theorem normalizer_square (r : (pinnedRootData k).Root) :
    (data k).n r 1 * (data k).n r 1 = (data k).h r (-1) := by
  change normalizerWord k r.down 1 * normalizerWord k r.down 1 = corootWord k r.down (-1)
  have hneg : (-1:kˣ) = 1 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_one, CharTwo.neg_eq]
  rw [hneg, corootWord_one]
  simpa only [pow_two] using normalizerWord_sq k r.down 1

theorem torus_conjugation (r s : (pinnedRootData k).Root) (a : k) (u : kˣ) :
    ((data k).h s u)⁻¹ * (data k).x r a * (data k).h s u =
      (data k).x r ((u:k) ^ (pinnedRootData k).pairing r s * a) := by
  let z : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => u)
  have hz : dPointEquiv 1 z 0 = u := by simp [z]
  have h := ((pinnedRootData_isRealization k).2.2.1 r).2
    (pinnedRootParametrization k r) a (((pinnedRootData k).rootCocharacter s).onPoints z)
  have hχ := (pinnedRootData_isRealization k).rootWeight_rootCocharacter r s z
  rw [hz] at hχ
  simp only [pinnedRootParametrization_inclusion, pinnedRootData_rootCocharacter, hz, hχ] at h
  exact h

end
end Triality.SimplyConnected.Pinning.ChevalleySource
