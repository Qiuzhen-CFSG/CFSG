module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondRecognition
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PGroup.CriticalSubgroup

/-!
# Conjugation on the actual second Tits core

The common Sylow acts on the actual normal two-core of the second parabolic.
An equivalence of cores transports conjugation, preserving its centralizer
kernel. For a self-centralizing core this kernel is precisely its center;
thus the size of the action image is determined without assuming a splitting.

These are the action interfaces for reconstructing the cubic endpoint in
Aschbacher--Smith F.1.12 and14.2.21, pp.263 and988--989. The marked core is
the literal pullback from `SecondRecognition`, with Parrott's generators.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.SecondCoreAction
open Subgroup

abbrev Core := pCore 2 second

/-- Conjugation by the actual second parabolic, on its actual two-core. -/
def model : second →* MulAut Core := MulAut.conjNormal

/-- The restriction of that action to the specified common Sylow. -/
def sylow : S →* MulAut Core := model.comp (inclusion sylow_le_second)

/-- The pullback core retains its original inclusion in the second endpoint. -/
def sylowCoreEquiv : SecondRecognition.coreInSylow ≃* Core := by
  let j := inclusion sylow_le_second
  let K := SecondRecognition.coreInSylow
  let f : K →* Core := (j.comp K.subtype).codRestrict _ (fun x => x.property)
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext ((inclusion_injective sylow_le_second) (congrArg Subtype.val h))
  · intro q
    have hq : q.val.val ∈ S := by
      have h := pCore_isPGroup.le_sylow_of_normal
        RelativeSecondBlockLayers.secondSylowTwo q.property
      simpa only [RelativeSecondBlockLayers.secondSylowTwo_coe, mem_subgroupOf] using h
    exact ⟨⟨⟨q.val.val,hq⟩,q.property⟩,rfl⟩

theorem sylowCoreEquiv_val (q : SecondRecognition.coreInSylow) :
    (sylowCoreEquiv q : second) = inclusion sylow_le_second q.val := rfl

theorem sylowCoreEquiv_symm_val (q : Core) :
    inclusion sylow_le_second (sylowCoreEquiv.symm q).val = q.val :=
  (sylowCoreEquiv_val _).symm.trans
    (congrArg Subtype.val (sylowCoreEquiv.apply_symm_apply q))

theorem sylow_apply (s : S) (q : Core) :
    (sylowCoreEquiv.symm (sylow s q)).val =
      s * (sylowCoreEquiv.symm q).val * s⁻¹ := by
  apply inclusion_injective sylow_le_second
  rw [sylowCoreEquiv_symm_val, map_mul, map_mul, map_inv, sylowCoreEquiv_symm_val]
  rfl

variable {P : Type*} [Group P] (N : Subgroup P) [N.Normal]

/-- Transport the original conjugation action, rather than choosing a new action. -/
def through (e : Core ≃* N) : P →* MulAut Core :=
  (MulAut.congr e.symm).toMonoidHom.comp MulAut.conjNormal

theorem through_apply (e : Core ≃* N) (g : P) (q : Core) :
    e (through N e g q) = MulAut.conjNormal g (e q) := by
  exact e.apply_symm_apply _

/-- A change of core coordinates conjugates the entire original action image. -/
theorem through_recoordinate (e : Core ≃* N) (α : MulAut Core) :
    through N (α.symm.trans e) =
      (MulAut.congr α).toMonoidHom.comp (through N e) := by
  ext g q
  rfl

theorem through_range_recoordinate (e : Core ≃* N) (α : MulAut Core) :
    (through N (α.symm.trans e)).range =
      (through N e).range.map (MulAut.congr α).toMonoidHom := by
  rw [through_recoordinate, MonoidHom.range_comp]

theorem through_ker (e : Core ≃* N) :
    (through N e).ker = centralizer (N : Set P) := by
  rw [through, MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e.symm).injective,
    MulAut.conjNormal_ker_eq_centralizer]

theorem through_ker_of_selfCentralizing (e : Core ≃* N)
    (hc : centralizer (N : Set P) ≤ N) :
    (through N e).ker = (center N).map N.subtype := by
  rw [through_ker, map_center_subtype_eq_inf_centralizer, inf_eq_right.mpr hc]

/-- The exact image count retains the central kernel of the original action. -/
theorem through_card [Finite P] (e : Core ≃* N)
    (hc : centralizer (N : Set P) ≤ N) :
    Nat.card (center Core) * Nat.card (through N e).range = Nat.card P := by
  have h := (through N e).ker.card_mul_index
  rw [index_ker, through_ker_of_selfCentralizing N e hc] at h
  rw [Nat.card_congr ((center N).equivMapOfInjective N.subtype
    N.subtype_injective).toEquiv.symm] at h
  rwa [Nat.card_congr (centerCongr e.symm).toEquiv] at h

end Tits.ExceptionalParabolics.SecondCoreAction
