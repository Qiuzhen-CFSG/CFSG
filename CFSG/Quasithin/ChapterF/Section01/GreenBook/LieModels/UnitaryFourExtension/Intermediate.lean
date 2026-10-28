module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Restricting the unitary-four degree-two extension

Let X be the actual projective unitary group inside its specified extension
by the Hermitian field involution. Any intermediate subgroup X ≤ Y is X
or the whole extension, by the literal C₂ quotient. Intersecting Y with
both extended flag stabilizers and their full overlap therefore yields
one of the two original marked amalgams.

For Y = X, all three equivalences are restrictions of the same semidirect
inclusion; both squares commute on the full overlap. This also keeps the
odd part of the overlap. The construction uses every positive field degree
and does not identify an arbitrary outer extension with this degree-two
extension. That reduction remains an earlier source obligation.

Source: Aschbacher–Smith F.1.12(I)(6), printed pp.263–264, and the
original-extension analysis in DGS85, Chapter 15, printed pp.225–231.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension.Intermediate
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
variable (m : ℕ) (hm : 1 ≤ m)

/-- The concrete projective extension by the specified field involution. -/
abbrev E := Extension.ProjectiveExtension m hm
/-- The ordinary projective group as a subgroup of its actual extension. -/
abbrev base : Subgroup (E m hm) :=
  (SemidirectProduct.inl : ProjectiveGroup m hm →* E m hm).range

/-- The outer C₂ quotient has no proper nontrivial intermediate subgroup. -/
theorem intermediate_eq_base_or_top (Y : Subgroup (E m hm)) (hY : base m hm ≤ Y) :
    Y = base m hm ∨ Y = ⊤ := by
  by_cases hle : Y ≤ base m hm
  · exact Or.inl (le_antisymm hle hY)
  · right
    obtain ⟨x,hx,hxb⟩ := SetLike.not_le_iff_exists.mp hle
    have hxr : x.right = UnitaryFourOuter.generator :=
      (UnitaryFourOuter.c2_cases x.right).resolve_left (by
        intro hr
        apply hxb
        exact ⟨x.left, SemidirectProduct.ext rfl hr.symm⟩)
    have hgen : SemidirectProduct.inr UnitaryFourOuter.generator ∈ Y := by
      have hl : SemidirectProduct.inl x.left ∈ Y := hY ⟨x.left,rfl⟩
      have hprod := SemidirectProduct.inl_left_mul_inr_right x
      rw [hxr] at hprod
      exact (Y.mul_mem_cancel_left hl).mp (hprod.symm ▸ hx)
    apply top_unique
    intro y _
    have hl : SemidirectProduct.inl y.left ∈ Y := hY ⟨y.left,rfl⟩
    have hr : SemidirectProduct.inr y.right ∈ Y := by
      rcases UnitaryFourOuter.c2_cases y.right with hy | hy
      · rw [hy,map_one]; exact Y.one_mem
      · rw [hy]; exact hgen
    simpa only [SemidirectProduct.inl_left_mul_inr_right] using Y.mul_mem hl hr

/-- Restrict both flag endpoints and their entire overlap to the same Y. -/
def amalgam (Y : Subgroup (E m hm)) : RankTwoAmalgam
    (Y ⊓ Extension.point m hm : Subgroup (E m hm))
    (Y ⊓ Extension.overlap m hm : Subgroup (E m hm))
    (Y ⊓ Extension.plane m hm : Subgroup (E m hm)) :=
  RankTwoAmalgam.ofSubgroups _ _ _
    (inf_le_inf_left _ ((Extension.exact_overlap m hm) ▸ inf_le_left))
    (inf_le_inf_left _ ((Extension.exact_overlap m hm) ▸ inf_le_right))

/-- The ordinary point endpoint is exactly the base intersection. -/
theorem base_inf_point : base m hm ⊓ Extension.point m hm =
    (pointParabolic m hm).map SemidirectProduct.inl := by
  ext x
  constructor
  · rintro ⟨⟨a,rfl⟩,ha⟩
    exact ⟨a,(Extension.mem_point m hm _).mp ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,rfl⟩,(Extension.mem_point m hm _).mpr ha⟩

/-- The ordinary plane endpoint is exactly the base intersection. -/
theorem base_inf_plane : base m hm ⊓ Extension.plane m hm =
    (planeParabolic m hm).map SemidirectProduct.inl := by
  ext x
  constructor
  · rintro ⟨⟨a,rfl⟩,ha⟩
    exact ⟨a,(Extension.mem_plane m hm _).mp ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,rfl⟩,(Extension.mem_plane m hm _).mpr ha⟩

/-- The base restriction preserves the full flag overlap. -/
theorem base_inf_overlap : base m hm ⊓ Extension.overlap m hm =
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.overlap m hm).map
      SemidirectProduct.inl := by
  rw [← Extension.exact_overlap, inf_inf_distrib_left,
    base_inf_point, base_inf_plane,← Subgroup.map_inf _ _ _ SemidirectProduct.inl_injective,
    CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.exact_overlap]

/-- The three base restrictions commute with both overlap inclusions. -/
def baseIso : RankTwoAmalgam.Iso (amalgam m hm (base m hm))
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.amalgam m hm) := by
  let a := RankTwoAmalgam.ofSubgroupsMapIso
    (SemidirectProduct.inl : ProjectiveGroup m hm →* E m hm)
    SemidirectProduct.inl_injective
    (pointParabolic m hm) (CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.overlap m hm)
    (planeParabolic m hm)
    (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
  have b : RankTwoAmalgam.Iso (amalgam m hm (base m hm))
      (RankTwoAmalgam.ofSubgroups
        ((pointParabolic m hm).map SemidirectProduct.inl)
        ((CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.overlap m hm).map SemidirectProduct.inl)
        ((planeParabolic m hm).map SemidirectProduct.inl)
        (Subgroup.map_mono (Subgroup.map_mono inf_le_left))
        (Subgroup.map_mono (Subgroup.map_mono inf_le_right))) :=
    { left := MulEquiv.subgroupCongr (base_inf_point m hm)
      middle := MulEquiv.subgroupCongr (base_inf_overlap m hm)
      right := MulEquiv.subgroupCongr (base_inf_plane m hm)
      left_commutes := fun _ => rfl
      right_commutes := fun _ => rfl }
  exact b.trans a.symm

/-- Restriction to the whole extension preserves its two inclusion squares. -/
def topIso : RankTwoAmalgam.Iso (amalgam m hm ⊤) (Extension.amalgam m hm) where
  left := MulEquiv.subgroupCongr (top_inf_eq _)
  middle := MulEquiv.subgroupCongr (top_inf_eq _)
  right := MulEquiv.subgroupCongr (top_inf_eq _)
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- Every intermediate extension gives one of the two compatible markings. -/
theorem marked_alternatives (Y : Subgroup (E m hm)) (hY : base m hm ≤ Y) :
    Nonempty (RankTwoAmalgam.Iso (amalgam m hm Y)
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso (amalgam m hm Y) (Extension.amalgam m hm)) := by
  rcases intermediate_eq_base_or_top m hm Y hY with rfl | rfl
  · exact Or.inl ⟨baseIso m hm⟩
  · exact Or.inr ⟨topIso m hm⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension.Intermediate
