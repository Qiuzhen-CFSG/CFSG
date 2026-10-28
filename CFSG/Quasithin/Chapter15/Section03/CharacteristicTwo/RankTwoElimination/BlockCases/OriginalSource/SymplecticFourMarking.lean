module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryTheta
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import Theory.SpecificGroups.BinaryComponentResidual.SymplecticFour
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# The literal symplectic marking of the original component

The centerless symplectic core is canonically identified with the actual star
quotient. The marked parabolic from C.2.7 therefore transports along the
original core quotient map, and the ordinary residual argument gives 15.3.17.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The Sp4(4) core marking supplies the ordinary part of source 15.3.17. -/
theorem component_eq_theta_of_symplecticFour
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hrI : primeRank 3 I ≤ 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    c.L = theta I :=
  RankTwoElimination.OriginalSource.component_eq_theta_of_ordinary_quotient d c hrI
    (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e
      (Theory.SpecificGroups.BinaryComponentResidual.symplecticFour hF))

/-- The given Sp4(4) core model is also the actual star model. The
comparison is the canonical central-cover map, so no compatibility choice
is added to the marked C.2.7 parabolic. -/
noncomputable def symplecticFour_star_equiv
    {I L R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    starImage L R L ≃* Theory.SpecificGroups.SymplecticFour.Sp F := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : e x ∈ center (Theory.SpecificGroups.SymplecticFour.Sp F) :=
      (centerCongr e ⟨x,hx⟩).property
    rw [Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot,mem_bot] at he
    exact mem_bot.mpr (e.map_eq_one_iff.mp he)
  have hne : starImage L R L ≠ ⊥ := by
    intro hh
    have hlt := (ChapterC.C27Source.star_thompson_intersection_from_source h).2
    rw [hh] at hlt
    exact not_lt_bot hlt
  exact (coreStarEquivOfCenterEqBot h.normalizes h.quasisimple hne hz).symm.trans e
/-- The canonical comparison evaluates to the given core marking. -/
theorem symplecticFour_star_equiv_mk
    {I L R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) (l : L) :
    symplecticFour_star_equiv h e (toStarImage L R l) =
      e (QuotientGroup.mk' (pCore 2 L) l) := by
  unfold symplecticFour_star_equiv
  apply congrArg e
  apply (coreStarEquivOfCenterEqBot h.normalizes h.quasisimple _ _).injective
  exact (coreStarEquivOfCenterEqBot h.normalizes h.quasisimple _ _).apply_symm_apply _

/-- Transport the full marked parabolic to the literal core quotient map. -/
theorem symplecticFour_core_parabolic
    {I L R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
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

/-- The symplectic multiplier vanishes, so the literal star marking already
identifies the whole component core quotient. -/
noncomputable def symplecticFour_core_equiv_of_star
    {I L R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : starImage L R L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    (L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp F := by
  have hne : starImage L R L ≠ ⊥ := by
    intro hh
    have hlt := (ChapterC.C27Source.star_thompson_intersection_from_source h).2
    rw [hh] at hlt
    exact not_lt_bot hlt
  let f := coreStarCover h.normalizes h.quasisimple hne
  let g : PerfectCentralCovering.Cover (L ⧸ pCore 2 L)
      (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      surjective := e.surjective.comp f.surjective
      isPerfect := f.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact f.ker_le_center }
  exact Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.coverEquiv (by omega) g

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
