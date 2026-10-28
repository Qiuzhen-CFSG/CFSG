module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.SymplecticFourMarking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.SolvableControl
public import Theory.SpecificGroups.SymplecticFour.ParabolicCubicClosure

/-!
# The original source excludes all nonbinary symplectic star fields

The original identity Y₊=θ(M∩I) makes its cubic-generated subgroup
solvable. The canonical perfect cover of the symplectic star image has
trivial kernel, so the full marked parabolic is an image of M∩L through
a two-group kernel. Cubic generation therefore passes to that parabolic,
contradicting the nonsolvable SL₂ quotient of either local factor.

This specializes the argument of Aschbacher–Smith 15.3.20 to the actual
source hypotheses and excludes the symplectic B.5 row before a separate
field-order restriction. No proper-overgroup induction or module marking
is needed by this branch.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- Transport the full marked parabolic to the literal core quotient map. -/
theorem symplectic_core_parabolic
    {I L R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    ∃ g : Theory.SpecificGroups.SymplecticFour.Sp F,
      ((M.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).map
        (MulAut.conj g).toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointParabolic ∨
      ((M.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).map
        (MulAut.conj g).toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeParabolic := by
  let f := symplecticFour_star_equiv h e
  have he : ((starM L R M).subgroupOf (starImage L R L)).map f.toMonoidHom =
      (M.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨k,hk,hky⟩ := hy
      let l : L := ⟨k,hk.2⟩
      have hy' : toStarImage L R l = y := Subtype.ext hky
      refine ⟨l,hk.1,?_⟩
      rw [←hy']
      exact (symplecticFour_star_equiv_mk h e l).symm
    · rintro ⟨l,hl,rfl⟩
      refine ⟨toStarImage L R l,?_,symplecticFour_star_equiv_mk h e l⟩
      exact ⟨inclusion (show L ≤ L ⊔ R from le_sup_left) l,⟨hl,l.property⟩,rfl⟩
  simpa only [he] using
    ChapterC.C27Source.star_symplectic_marked_parabolic_from_source h f (by omega)
/-- The original theta control survives the literal component core image. -/
theorem solvable_cubic_component_image
    {L M : Subgroup G} {H : Type*} [Group H]
    (hs : Group.IsSolvable (theta M)) (q : L →* H) (hk : IsPGroup 2 q.ker) :
    Group.IsSolvable (closure {x : (M.subgroupOf L).map q | orderOf x = 3}) := by
  let D := M.subgroupOf L
  let j : D →* G := L.subtype.comp D.subtype
  have hj : Function.Injective j := L.subtype_injective.comp D.subtype_injective
  have hle : closure {x : D | orderOf x = 3} ≤ (theta M).comap j := by
    apply (closure_le _).mpr
    intro x hx
    exact subset_closure ⟨x.property,(orderOf_injective j hj x).trans hx⟩
  let k : closure {x : D | orderOf x = 3} →* theta M :=
    (j.comp (closure {x : D | orderOf x = 3}).subtype).codRestrict _
      (fun x => hle x.property)
  let := hs
  have hsD : Group.IsSolvable (closure {x : D | orderOf x = 3}) :=
    Group.isSolvable_of_isSolvable_injective (f := k)
      (fun x y hh => Subtype.ext (hj (congrArg (fun z : theta M => (z : G)) hh)))
  let f := q.subgroupMap D
  have hker : f.ker = (q.comp D.subtype).ker := by
    ext x
    exact Subtype.ext_iff
  have hkf : IsPGroup 2 f.ker := by
    rw [hker]
    exact hk.comap_of_injective D.subtype D.subtype_injective
  exact solvable_cubic_closure_of_two_kernel f (q.subgroupMap_surjective D) hkf hsD

/-- The original source excludes every nonbinary symplectic star field. -/
theorem source_15_3_20_symplectic_star
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : starImage c.L d.R c.L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : False := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hsol : Group.IsSolvable (theta (d.MI I)) := by
    rw [←h11.theta_eq]
    let : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) :=
      d.join_isSolvable_of_three_quotient hI h11.theta_eq.symm
        (ComponentIntersection.cubic_quotient_facts d.Yplus htwo.1).1
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))
      (inclusion_injective _)
  have hne : starImage c.L d.R c.L ≠ ⊥ := by
    intro hh
    have hlt := (ChapterC.C27Source.star_thompson_intersection_from_source h).2
    rw [hh] at hlt
    exact not_lt_bot hlt
  let f := coreStarCover h.normalizes h.quasisimple hne
  let f' : PerfectCentralCovering.Cover (c.L ⧸ pCore 2 c.L)
      (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      surjective := e.surjective.comp f.surjective
      isPerfect := f.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact f.ker_le_center }
  let eCore := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.coverEquiv (by omega) f'
  let q := eCore.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))
  have hk : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ eCore.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hs := solvable_cubic_component_image hsol q hk
  obtain ⟨g,hg⟩ := symplectic_core_parabolic h hq eCore
  rcases hg with hp | hp
  · let b := ((MulAut.conj g).subgroupMap ((d.MI I).subgroupOf c.L |>.map q)).trans
      (MulEquiv.subgroupCongr hp)
    have hsp := solvable_cubic_closure_of_injective b.symm.toMonoidHom b.symm.injective hs
    exact Theory.SpecificGroups.SymplecticFour.pointParabolic_cubic_not_solvable (by omega) hsp
  · let b := ((MulAut.conj g).subgroupMap ((d.MI I).subgroupOf c.L |>.map q)).trans
      (MulEquiv.subgroupCongr hp)
    have hsp := solvable_cubic_closure_of_injective b.symm.toMonoidHom b.symm.injective hs
    exact Theory.SpecificGroups.SymplecticFour.planeParabolic_cubic_not_solvable (by omega) hsp
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
