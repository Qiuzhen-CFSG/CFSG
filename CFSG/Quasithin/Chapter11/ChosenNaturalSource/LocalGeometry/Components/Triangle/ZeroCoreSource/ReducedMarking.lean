module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.Amalgam
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Twisted
public import Theory.SpecificGroups.SymplecticFour.FlagPaths.Counts
public import Theory.SpecificGroups.PSL3.SmallCompletion.Orders
public import Theory.AtlasPort.LinearGroups.G2.Parabolic

/-!
# The original diagram and the field-four DGS sieve

The original overlap S₀X normalizes S₀, so the DGS reduction fixes S₀
and all ambient elements of the original inclusion diagram. The two A₅
marks force each ordinary field to have four elements. Existing full-row
exclusions remove the twisted, exceptional and binary comparisons. Every
surviving comparison retains both endpoint maps and the whole overlap.

Source: Aschbacher--Smith 11.1.2, printed p.762; DGS (6.1) and (15.2).
This is a reduction from the genuine earlier DGS catalogue, not its proof.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
open ChapterF.Source ChapterF.Source.SuzukiContainment
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

omit [Finite G] in
/-- The original full overlap normalizes its actual two-subgroup. -/
theorem overlap_normalizes_commonTwo (X : Subgroup G) :
    overlap T X ≤ normalizer (commonTwo T X : Set G) := by
  have hle : overlap T X ≤ X ⊔ (T : Subgroup G) :=
    sup_le (map_subtype_le (pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G))) le_sup_left
  apply hle.trans
  exact (X ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

omit [Finite G] in
/-- For the original triangle the DGS reduction leaves S₀ unchanged. -/
theorem original_reducedSylow {K₀ L₂ X : Subgroup G}
    (h : HypothesisF11 ![K₀,L₂] (commonTwo T X))
    (hb : commonBorel ![K₀,L₂] (commonTwo T X) = overlap T X) :
    reducedSylow ![K₀,L₂] (commonTwo T X) = commonTwo T X := by
  apply h.commonBorel_twoCore_eq
  intro i
  exact (borel_le_commonBorel i).trans (hb ▸ overlap_normalizes_commonTwo X)

/-- The actual original inclusion diagram, including the whole odd Borel. -/
def originalTriangle (T : Sylow 2 G) (X K₀ L₂ : Subgroup G) :=
  ofSubgroups (endpoint T X K₀) (overlap T X) (endpoint T X L₂)
    le_sup_right le_sup_right

/-- Reduction is the identity on the original ambient elements in all three groups. -/
def originalReducedIso {K₀ L₂ X : Subgroup G}
    (h : HypothesisF11 ![K₀,L₂] (commonTwo T X))
    (hb : commonBorel ![K₀,L₂] (commonTwo T X) = overlap T X) :
    Iso (originalTriangle T X K₀ L₂) (reducedAmalgam ![K₀,L₂] (commonTwo T X)) := by
  have hs := original_reducedSylow h hb
  have hp (i : Fin 2) : parabolic ![K₀,L₂] (reducedSylow ![K₀,L₂] (commonTwo T X)) i =
      endpoint T X (![K₀,L₂] i) := by
    rw [hs,parabolic_eq_sup_commonBorel,hb]
    rfl
  have hm : commonBorel ![K₀,L₂] (reducedSylow ![K₀,L₂] (commonTwo T X)) = overlap T X := by
    rw [hs,hb]
  exact {
    left := MulEquiv.subgroupCongr (hp 0).symm
    middle := MulEquiv.subgroupCongr hm.symm
    right := MulEquiv.subgroupCongr (hp 1).symm
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }

omit [Finite G] in
@[simp] theorem originalReducedIso_left_val {K₀ L₂ X : Subgroup G}
    (h : HypothesisF11 ![K₀,L₂] (commonTwo T X))
    (hb : commonBorel ![K₀,L₂] (commonTwo T X) = overlap T X)
    (x : endpoint T X K₀) : ((originalReducedIso h hb).left x : G) = x := rfl

omit [Finite G] in
@[simp] theorem originalReducedIso_middle_val {K₀ L₂ X : Subgroup G}
    (h : HypothesisF11 ![K₀,L₂] (commonTwo T X))
    (hb : commonBorel ![K₀,L₂] (commonTwo T X) = overlap T X)
    (x : overlap T X) : ((originalReducedIso h hb).middle x : G) = x := rfl

omit [Finite G] in
@[simp] theorem originalReducedIso_right_val {K₀ L₂ X : Subgroup G}
    (h : HypothesisF11 ![K₀,L₂] (commonTwo T X))
    (hb : commonBorel ![K₀,L₂] (commonTwo T X) = overlap T X)
    (x : endpoint T X L₂) : ((originalReducedIso h hb).right x : G) = x := rfl

namespace Parameters
variable {K : Fin 2 → Subgroup G} {U : Subgroup G}
  (h : HypothesisF11 K U)
  (a : ∀ i, Nonempty ((K i ⧸ pCore 2 (K i)) ≃* alternatingGroup (Fin 5)))
  (F : Type) [Field F] [Finite F] [CharP F 2]
include h a

omit [CharP F 2] in
theorem linear_four (b : Bool)
    (e : Iso (reducedAmalgam K U) (LinearNative.amalgam F b)) : Nat.card F = 4 := by
  have hh := (A5PairCatalogue.model_indices h a _ _ e).1
  rw [Matrix.PSL3.SmallCompletion.borel_relIndex] at hh
  omega

theorem symplectic_four (b : Bool)
    (e : Iso (reducedAmalgam K U) (SymplecticNative.amalgam F b)) : Nat.card F = 4 := by
  have hc := A5PairCatalogue.reduced_endpoint_card h 0 (a 0).some
  rw [Nat.card_congr e.left.toEquiv,Nat.card_congr e.middle.toEquiv] at hc
  have he : Nat.card (SymplecticNative.endpoint F b) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.borel (F := F)) * (Nat.card F + 1) := by
    rw [Theory.SpecificGroups.SymplecticFour.card_borel]
    cases b
    · exact Theory.SpecificGroups.SymplecticFour.FlagPaths.card_planeParabolic
    · exact Theory.SpecificGroups.SymplecticFour.FlagPaths.card_pointParabolic
  have hh := Nat.eq_of_mul_eq_mul_left
    (Nat.card_pos (α := Theory.SpecificGroups.SymplecticFour.borel (F := F))) (he.symm.trans hc)
  omega

omit [CharP F 2] in
theorem g2_four (b : Bool)
    (e : Iso (reducedAmalgam K U) (G2Native.amalgam F b)) : Nat.card F = 4 := by
  have hh := A5PairCatalogue.model_indices h a _ _ e
  have hi : (Atlas.G2.borel (K := F)).relIndex (Atlas.G2.parabolic (F := F)) = 5 := by
    cases b
    · exact hh.1
    · exact hh.2
  rw [Atlas.G2.borel_relIndex_parabolic] at hi
  omega
end Parameters

/-- Only actual field-four ordinary diagrams survive the full reduced input.
Both endpoints and the full original overlap are retained in every row. -/
inductive FieldFourComparison (T : Sylow 2 G) (X K₀ L₂ : Subgroup G) : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) (b : Bool)
      (e : Nonempty (Iso (originalTriangle T X K₀ L₂) (LinearNative.amalgam F b)))
  | symplectic (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) (b : Bool)
      (e : Nonempty (Iso (originalTriangle T X K₀ L₂) (SymplecticNative.amalgam F b)))
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) (b : Bool)
      (e : Nonempty (Iso (originalTriangle T X K₀ L₂) (G2Native.amalgam F b)))

/-- The genuine broad DGS input implies the marked original field-four alternatives. -/
theorem original_fieldFour_comparison {K₀ L₂ X : Subgroup G}
    (h : HypothesisF11 ![K₀,L₂] (commonTwo T X))
    (hqt : IsQuasithin (generated ![K₀,L₂] (commonTwo T X)))
    (hb : commonBorel ![K₀,L₂] (commonTwo T X) = overlap T X)
    (a : ∀ i, Nonempty ((![K₀,L₂] i ⧸ pCore 2 (![K₀,L₂] i)) ≃* alternatingGroup (Fin 5)))
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
      K₀ L₂ (commonTwo T X)) : FieldFourComparison T X K₀ L₂ := by
  cases ha with
  | linear F n hn hF b e =>
    exact .linear F (Parameters.linear_four h a F b e.some) b
      ⟨(originalReducedIso h hb).trans e.some⟩
  | symplectic F n hn hF b e =>
    exact .symplectic F (Parameters.symplectic_four h a F b e.some) b
      ⟨(originalReducedIso h hb).trans e.some⟩
  | g2 F b e =>
    exact .g2 F (Parameters.g2_four h a F b e.some) b
      ⟨(originalReducedIso h hb).trans e.some⟩
  | triality n hn b e => exact (A5PairCatalogue.not_triality h a n hn b e.some).elim
  | ree n b e => exact (A5PairCatalogue.not_ree h a n b e.some).elim
  | unitaryFour n hn b e => exact (A5PairCatalogue.not_unitaryFour h a n hn b e.some).elim
  | unitaryFive q hq heven M b e =>
    exact (A5PairCatalogue.not_unitaryFive h hqt a hq heven M b e.some).elim
  | exceptional c e => exact (A5PairCatalogue.not_reduced_exceptional a c e).elim
  | binaryLocal i e => exact (A5PairCatalogue.not_binary_overgroup_quotient i (a i).some le_rfl e).elim
  | binaryJoin i e => exact (A5PairCatalogue.not_binary_overgroup_quotient i (a i).some le_sup_left e).elim
  | binaryParabolic i e =>
    exact (A5PairCatalogue.not_binary_overgroup_quotient i (a i).some (le_sup_left.trans le_sup_left) e).elim


omit [Finite G] in
/-- All surviving full Borels have order at most the G₂(4) Borel order. -/
theorem FieldFourComparison.overlap_card_le {K₀ L₂ X : Subgroup G}
    (h : FieldFourComparison T X K₀ L₂) : Nat.card (overlap T X) ≤ 36864 := by
  cases h with
  | linear F hF b e =>
    have hc : Nat.card (Matrix.PSL3.LinearThree.borel F) ≤
        Nat.card (Matrix.PSL3.LinearThree.borelSL F) :=
      Nat.le_of_dvd (Nat.card_pos (α := Matrix.PSL3.LinearThree.borelSL F))
        ((Matrix.PSL3.LinearThree.borelSL F).card_map_dvd (Matrix.PSL3.projection F))
    rw [Nat.card_congr e.some.middle.toEquiv]
    apply hc.trans
    have hp : Nat.card (Matrix.PSL3.LinearThree.borelSL F) ≤
        Nat.card (Matrix.PSL3.SmallCompletion.parabolicSL F false) :=
      Nat.le_of_dvd (Nat.card_pos (α := Matrix.PSL3.SmallCompletion.parabolicSL F false))
        (card_dvd_of_le (show Matrix.PSL3.LinearThree.borelSL F ≤
          Matrix.PSL3.SmallCompletion.parabolicSL F false from inf_le_left))
    apply hp.trans
    rw [Matrix.PSL3.SmallCompletion.card_parabolicSL,hF]
    decide
  | symplectic F hF b e =>
    rw [Nat.card_congr e.some.middle.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_borel,hF]
    decide
  | g2 F hF b e =>
    rw [Nat.card_congr e.some.middle.toEquiv,Atlas.G2.card_borel,hF]
    decide

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
