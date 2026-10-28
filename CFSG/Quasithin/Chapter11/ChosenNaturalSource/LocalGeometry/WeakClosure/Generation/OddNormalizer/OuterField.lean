module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterUnitaryFour
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.RankOneSections.Profiles
public import Theory.GroupTheory.SylowOuterFrattiniSections

/-!
# Field bounds for the original natural outer section

The full component cover injects on outer automorphisms into its central
quotient. Every Theorem B model then has either solvable outer automorphisms
or a Sylow Frattini quotient with at most eight binary generators. The order
of the original simple section therefore divides |GL₈(2)|. Restoring the
original covering center, whose order divides three, leaves only SL₃(4)
and Sp₄(4) among the nonbinary natural models.

OuterSymplectic excludes the latter; Source applies the result to the actual
odd actor and Hall kernel. The remaining field-four linear branch stays with
qt-d-1222-natural-odd-kernel-normalizer.
Source: Aschbacher--Smith 4.4.10--12, pp.621--622, and Theorem B, p.33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem cover_outer_section_order {K Q : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (hQ : ¬ Group.IsSolvable Q)
    (U : Subgroup (MulAut.Outer K)) (f : U →* Q) (hf : Function.Surjective f) :
    Nat.card Q ∣ 5348063769211699200 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  rcases ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections.model_profile
    (Group.IsPerfect.not_isMulCommutative _) hm with hs | ⟨P,hP⟩
  · let := hs
    exact (hQ (Group.isSolvable_of_surjective hg)).elim
  · let : Group.IsSolvable
        (fixingSubgroup (MulAut (K ⧸ center K)) (P : Set (K ⧸ center K))) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    exact MulAut.simple_outer_section_card_dvd_GL_eight P hP hQ (U.map j) g hg

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The actual simple quotient order leaves just two full field-four covers. -/
theorem field_four_models_of_outer_order (hd : Nat.card (coreCentralQuotient L) ∣ 5348063769211699200) :
    S.field.degree = 2 ∧
      (Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)) := by
  have hfull : Nat.card (L ⧸ pCore 2 L) ∣ 16044191307635097600 := by
    have hh := Nat.mul_dvd_mul hd (quotient_center_card_dvd_three D S)
    rw [← card_eq_card_quotient_mul_card_subgroup (center (L ⧸ pCore 2 L))] at hh
    exact hh
  have hb := Nat.le_of_dvd (by decide : 0 < 16044191307635097600) hfull
  have hlo := S.nonbinary
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,linear_three_order] at hfull hb
    have hf : S.field.degree ≤ 8 := by
      by_contra! hf
      have hq : 512 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
      norm_num at hl
      omega
    have hf2 : S.field.degree = 2 := by
      interval_cases hh : S.field.degree <;>
        first | rfl | norm_num [S.field.card_eq,hh] at hfull
    exact ⟨hf2,Or.inl ⟨hm.some.groupEquiv⟩⟩
  | sp4 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hfull hb
    have hf : S.field.degree ≤ 6 := by
      by_contra! hf
      have hq : 128 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
      norm_num at hl
      omega
    have hf2 : S.field.degree = 2 := by
      interval_cases hh : S.field.degree <;>
        first | rfl | norm_num [S.field.card_eq,hh] at hfull
    exact ⟨hf2,Or.inr ⟨hm.some.groupEquiv⟩⟩
  | g2 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,Atlas.G2.card_Model] at hfull hb
    have hf : S.field.degree ≤ 4 := by
      by_contra! hf
      have hq : 32 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
      norm_num at hl
      omega
    interval_cases hh : S.field.degree <;>
      norm_num [S.field.card_eq,hh] at hfull


/-- The actual outer section forces field four in one of two natural rows. -/
theorem moved_outer_field_four {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) :
    S.field.degree = 2 ∧
      (Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)) := by
  let := S.source.toHypothesis1221.quasisimple
  let : IsSimpleGroup (coreCentralQuotient L) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient L) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center (L ⧸ pCore 2 L))) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple K := hK.2
  obtain ⟨U,f,hf⟩ := ho
  exact field_four_models_of_outer_order D S
    (cover_outer_section_order hm (Group.IsPerfect.not_isSolvable _) U f hf)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
