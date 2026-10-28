module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.CatalogueTransport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.SymplecticNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2Native
public import Theory.SpecificGroups.SymplecticFour.FlagPaths.Counts
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# Classical rows cannot have a quintic solvable first endpoint

The local SL₂ quotient of each linear, symplectic or G₂ endpoint is a
quotient of a subgroup of that endpoint. Solvability therefore forces the
field to have order two. The full linear Borel index is then three; the
binary symplectic endpoints and binary G₂ carrier have order prime to five.
Each contradicts the original index-five condition, in both orientations.
The quotient maps and concrete carrier orders are used throughout.

Source: Aschbacher–Smith F.1.12(I)(1)–(3), pp.262–264; DGS Theorem A,
pp.99–100. The source selection of a row is a separate input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
open DGS85.OriginalExtension
variable {G : Type*} [Group G] {K R S : Subgroup G}

/-- A solvable characteristic-two SL₂ has field order at most two. -/
theorem sl2_card_le_two_of_solvable {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hs : Group.IsSolvable SL(2,F)) : Nat.card F ≤ 2 := by
  by_contra hn
  have hF : 2 < Nat.card F := by omega
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable SL(2,F) hs

/-- The original quintic index forces five to divide the marked first endpoint order. -/
theorem model_left_five_dvd (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5)
    {X : Type*} [Group X]
    (e : parabolic ![K,R] (SuzukiContainment.reducedSylow ![K,R] S) 0 ≃* X) :
    5 ∣ Nat.card X := by
  rw [← Nat.card_congr e.toEquiv, reduced_left_card h hSK hi]
  exact dvd_mul_left _ _

open Matrix.PSL3 Matrix.PSL3.LinearThree in
/-- Neither orientation of a reduced linear comparison can occur at the quintic pair. -/
theorem not_linear (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5) (F : Type) [Field F] [Finite F] [CharP F 2]
    (b : Bool) (e : Iso (reducedAmalgam ![K,R] S) (LinearNative.amalgam F b)) : False := by
  have hs := model_left_solvable h hSK hi e.left
  have hF : Nat.card F ≤ 2 := by
    have hp : ∃ J : Subgroup PSL(3,F), J ≤ SmallCompletion.parabolic F b ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* SL(2,F)) := by
      cases b
      · exact ⟨pointLocal F, map_mono (pointLocalSL_le F), ⟨pointLocalCoreQuotientEquiv F⟩⟩
      · exact ⟨lineLocal F, map_mono (lineLocalSL_le F), ⟨lineLocalCoreQuotientEquiv F⟩⟩
    obtain ⟨J,hJ,⟨j⟩⟩ := hp
    let := hs
    let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective (inclusion_injective hJ)
    exact sl2_card_le_two_of_solvable
      (Group.isSolvable_of_surjective (f := j.toMonoidHom) j.surjective)
  have hh := model_left_index h hSK hi _ _ e.toParabolicEquiv
  rw [SmallCompletion.borel_relIndex] at hh
  omega

open Theory.SpecificGroups.SymplecticFour in
/-- Neither native symplectic orientation meets the quintic solvability and order constraints. -/
theorem not_symplectic (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5) (F : Type) [Field F] [Finite F] [CharP F 2]
    (b : Bool) (e : Iso (reducedAmalgam ![K,R] S) (SymplecticNative.amalgam F b)) : False := by
  have hs := model_left_solvable h hSK hi e.left
  have hF : Nat.card F ≤ 2 := by
    cases b
    · let : Group.IsSolvable (planeParabolic (F := F)) := hs
      let : Group.IsSolvable (planeLocal (F := F)) :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective planeLocal_le)
      exact sl2_card_le_two_of_solvable
        (Group.isSolvable_of_surjective (f := Plane.quotientMap) Plane.quotientMap_surjective)
    · let : Group.IsSolvable (pointParabolic (F := F)) := hs
      let : Group.IsSolvable (pointLocal (F := F)) :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective pointLocal_le)
      exact sl2_card_le_two_of_solvable
        (Group.isSolvable_of_surjective (f := pointQuotient) pointQuotient_surjective)
  have hF2 : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
  have hd := model_left_five_dvd h hSK hi e.left
  cases b
  · change 5 ∣ Nat.card (planeParabolic (F := F)) at hd
    rw [FlagPaths.card_planeParabolic, hF2] at hd
    norm_num at hd
  · change 5 ∣ Nat.card (pointParabolic (F := F)) at hd
    rw [FlagPaths.card_pointParabolic, hF2] at hd
    norm_num at hd

open Atlas.G2 Atlas.G2.LieParabolicSetup in
/-- The full G₂ carrier has order prime to five once the solvable endpoint forces the binary field. -/
theorem not_g2 (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5) (F : Type) [Field F] [Finite F] [CharP F 2]
    (b : Bool) (e : Iso (reducedAmalgam ![K,R] S) (G2Native.amalgam F b)) : False := by
  have hs := model_left_solvable h hSK hi e.left
  have hF : Nat.card F ≤ 2 := by
    cases b
    · let : Group.IsSolvable (parabolic₂ (F := F)) := hs
      let : Group.IsSolvable (local₂ (F := F)) :=
        Group.isSolvable_of_isSolvable_injective
          (inclusion_injective (show local₂ (F := F) ≤ parabolic₂ from by
            rw [← local₂_sup_borel]; exact le_sup_left))
      exact sl2_card_le_two_of_solvable
        (Group.isSolvable_of_surjective (f := longSLHom) longSLHom_surjective)
    · let : Group.IsSolvable (parabolic₁ (F := F)) := hs
      let : Group.IsSolvable (local₁ (F := F)) :=
        Group.isSolvable_of_isSolvable_injective
          (inclusion_injective (show local₁ (F := F) ≤ parabolic₁ from by
            rw [← local₁_sup_borel]; exact le_sup_left))
      exact sl2_card_le_two_of_solvable
        (Group.isSolvable_of_surjective (f := shortSLHom) shortSLHom_surjective)
  have hF2 : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
  have hd := (model_left_five_dvd h hSK hi e.left).trans
    (G2Native.endpoint F b).card_subgroup_dvd_card
  rw [card_Model, hF2] at hd
  norm_num at hd

end CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
