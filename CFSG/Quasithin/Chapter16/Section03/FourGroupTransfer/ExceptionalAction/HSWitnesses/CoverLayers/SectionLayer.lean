module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.FixedImage
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Recovering the whole fixed-subgroup layer from a central section

A section over a perfect subgroup fixed in the quotient is fixed upstairs:
the original section and its automorphic image are two lifts from a perfect
group through a central kernel, hence equal. Conjugation gives the same
uniqueness argument for normality. Thus the section constructs a component.
Every other component projects to the unique quotient component, and
component calculus makes it equal to the constructed one. This identifies
the entire layer by an actual multiplicative equivalence.

No surjectivity of the map between fixed subgroups is required.
Source application: Aschbacher–Smith 16.3.5, printed p.1179.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
open Subgroup Theory.GroupTheory

private theorem section_normal {A C Q : Type*} [Group A] [Group.IsPerfect A]
    [Group C] [Group Q] (f : C →* Q) (hz : f.ker ≤ center C)
    (j : A →* Q) (hj : Function.Injective j) (hn : j.range.Normal)
    (s : A →* C) (hs : f.comp s = j) : s.range.Normal := by
  let := hn
  let e : A ≃* j.range := MonoidHom.ofInjective hj
  constructor
  rintro _ ⟨a, rfl⟩ g
  let α : MulAut A := (e.trans (MulAut.conjNormal (H := j.range) (f g))).trans e.symm
  have hα (x : A) : j (α x) = f g * j x * (f g)⁻¹ := by
    exact congrArg Subtype.val (e.apply_symm_apply (MulAut.conjNormal (H := j.range) (f g) (e x)))
  have he : (MulAut.conj g).toMonoidHom.comp s = s.comp α.toMonoidHom := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq f hz
    apply MonoidHom.ext
    intro x
    change f (g * s x * g⁻¹) = f (s (α x))
    simp only [map_mul, map_inv]
    rw [show f (s x) = j x from DFunLike.congr_fun hs x,
      show f (s (α x)) = j (α x) from DFunLike.congr_fun hs (α x), hα]
  exact ⟨α a, (DFunLike.congr_fun he a).symm⟩

/-- A section over the unique component of the quotient fixed subgroup
constructs and identifies the entire covering fixed-subgroup layer. -/
theorem layer_equiv_of_section {G A : Type*} [Group G] [Group A] [IsQuasisimple A]
    (I : Subgroup G) (hz : pCore 2 I ≤ center I)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) (r : MulAut I)
    (j : A →* (modelAction I e r).fixedSubgroup) (hj : Function.Injective j)
    (hn : j.range.Normal)
    (hunique : ∀ K : Subgroup (modelAction I e r).fixedSubgroup,
      IsComponent _ K → K = j.range)
    (s : A →* I)
    (hs : (modelProjection I e).comp s =
      (modelAction I e r).fixedSubgroup.subtype.comp j) :
    Nonempty (componentLayer r.fixedSubgroup ≃* A) := by
  have hpz : (modelProjection I e).ker ≤ center I := by
    intro x hx
    apply hz
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact hx.trans (map_one e).symm
  have hfix (x : A) : r (s x) = s x := by
    have he : r.toMonoidHom.comp s = s := by
      apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq (modelProjection I e) hpz
      apply MonoidHom.ext
      intro x
      change modelProjection I e (r (s x)) = modelProjection I e (s x)
      rw [← modelAction_projection,
        show modelProjection I e (s x) = (j x).val from DFunLike.congr_fun hs x]
      exact (MulAut.mem_fixedSubgroup _ _).mp (j x).property
    exact DFunLike.congr_fun he x
  let t : A →* r.fixedSubgroup := s.codRestrict _ (fun x =>
    (MulAut.mem_fixedSubgroup r _).mpr (hfix x))
  have ht : (fixedProjection I e r).comp t = j := by
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (DFunLike.congr_fun hs x)
  have hti : Function.Injective t := by
    intro x y h
    apply hj
    have h' := congrArg (fixedProjection I e r) h
    simpa only [← MonoidHom.comp_apply, ht] using h'
  have htn := section_normal (fixedProjection I e r)
    (fixedProjection_ker_le_center I hz e r) j hj hn t ht
  have htc : IsComponent r.fixedSubgroup t.range :=
    ⟨htn.isSubnormal, IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hti)⟩
  have htmap : t.range.map (fixedProjection I e r) = j.range := by
    rw [← MonoidHom.range_comp, ht]
  have hall (K : Subgroup r.fixedSubgroup) (hK : IsComponent _ K) : K = t.range := by
    have hmap := hunique _ (fixedProjection_component I hz e r K hK)
    apply hK.eq_of_map_eq htc (fixedProjection I e r) (hmap.trans htmap.symm)
    rw [hmap]
    let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
    let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
    let : Nontrivial j.range := (MonoidHom.ofInjective hj).symm.surjective.nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  have hlayer : componentLayer r.fixedSubgroup = t.range := by
    apply le_antisymm
    · exact sSup_le fun K hK => (hall K hK).le
    · exact le_sSup htc
  exact ⟨(MulEquiv.subgroupCongr hlayer).trans (MonoidHom.ofInjective hti).symm⟩

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
