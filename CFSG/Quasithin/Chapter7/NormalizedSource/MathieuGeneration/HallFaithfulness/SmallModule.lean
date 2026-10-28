module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadical
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.Representation.Mathieu.SmallModules.ElevenDimensionalCovers

/-!
# Native module markings for the remaining Mathieu Hall obstruction

The original module survives faithfully in the containing J₄ component's
literal central quotient. The proved two-rank bound therefore makes the
original orbit space have dimension at most eleven. Faithful irreducibility
and the full Mathieu cover comparison identify it as the M₁₂ heart or the
M₂₂ Todd/code module, of dimension ten and order 1024.

The Hall application derives these markings from the original nonfaithful
Hall subgroup and its actual pushing-up witnesses. No cover, representation,
or dimension premise is added. The small-Mathieu radical normalizer
contradictions and the final Hall-faithfulness statement remain open.

Source: Aschbacher–Smith 4.2.13 and 4.4.14, printed pp.611–612,624–625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.MathieuSmall Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped IsMulCommutative
variable {G : Type*} [instG : Group G] [finG : Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The faithful image of the original module in the full component quotient
bounds its original orbit representation, before any module recognition. -/
theorem sourceOrbit_pushingUp_finrank_le_eleven
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    Module.finrank (ZMod 2) D.orbitSpace ≤ 11 := by
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hb := (primeRank_le_iff_elementary_card_le Janko4.Model).mp
    Janko4.TwoRank.model_twoRank_le_eleven _ hn.2.2.2.2.2.2.1
  rw [hn.2.2.2.2.2.2.2.1] at hb
  have hc : Nat.card D.orbitSpace = Nat.card V :=
    (Nat.card_congr D.sourceOrbitCoordinates.toEquiv).trans
      (congrArg (fun X : Subgroup G => Nat.card X) hV.symm)
  rw [←hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hb
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

/-- Both surviving small Mathieu quotients have actual ten-dimensional
module markings on the original orbit; the full component cover is retained
until the faithful binary action rules out its center. -/
theorem sourceOrbit_pushingUp_small_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M12) →
      IsM12Heart (L := D.orbitComponent) (V := D.orbitSpace)
        (D.orbitRepresentation.comp D.orbitComponent.subtype)) ∧
    (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) →
      IsM22ToddOrDual (L := D.orbitComponent) (V := D.orbitSpace)
        (D.orbitRepresentation.comp D.orbitComponent.subtype)) := by
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hd := D.sourceOrbit_pushingUp_finrank_le_eleven hV hfix hw K hK e
  let σ : Representation (ZMod 2) D.orbitComponent D.orbitSpace :=
    D.orbitRepresentation.comp D.orbitComponent.subtype
  have hf : Function.Injective σ :=
    (Representation.BinaryOffender.subspaceImageRepresentation_injective _ _).comp D.orbitComponent.subtype_injective
  let : IsQuasisimple D.orbitComponent := D.orbitComponent_quasisimple h.toHypothesis1221
  let : σ.IsIrreducible := D.sourceOrbit_irreducible_of_many h hmany hnon hV
  exact ⟨fun em => m12_of_finrank_le_eleven σ hf em.some hd,
    fun em => m22_of_finrank_le_eleven σ hf em.some hd⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- A nonfaithful original Hall subgroup forces a genuine native marking of
the original ten-dimensional orbit action, and fixes the whole module order. -/
theorem sourceOrbit_mathieu_hall_small_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H₀)
    (B₀ : Subgroup H₀) (hBN : B₀ ≤ (normalizer (L : Set G)).subgroupOf H₀)
    (hHall : IsHallSubgroup oddPrimes
      (B₀.subgroupOf ((normalizer (L : Set G)).subgroupOf H₀)))
    (hker : B₀.map H₀.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    Module.finrank (ZMod 2) D.orbitSpace = 10 ∧ Nat.card V = 1024 ∧
      ((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M12) ∧
        IsM12Heart (L := D.orbitComponent) (V := D.orbitSpace)
        (D.orbitRepresentation.comp D.orbitComponent.subtype)) ∨
      (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) ∧
        IsM22ToddOrDual (L := D.orbitComponent) (V := D.orbitSpace)
        (D.orbitRepresentation.comp D.orbitComponent.subtype))) := by
  have hsource := @sourceOrbit_mathieu_hall_pushingUp_only G instG finG T L V D
    h hmany hV hm hnon H₀ hH hlarge B₀ hBN hHall hker
  obtain ⟨p,A,hA⟩ := hsource
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,hgap⟩ := hA
  obtain ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,hrest⟩ := hgap
  have hmodels := D.sourceOrbit_pushingUp_small_module h hmany hV hnon hw K hK e
  have hd : Module.finrank (ZMod 2) D.orbitSpace = 10 :=
    hsmall.elim (fun em => (hmodels.1 em).finrank) (fun em => (hmodels.2 em).finrank)
  refine ⟨hd,?_,hsmall.imp (fun em => ⟨em,hmodels.1 em⟩) (fun em => ⟨em,hmodels.2 em⟩)⟩
  have hc : Nat.card D.orbitSpace = Nat.card V :=
    (Nat.card_congr D.sourceOrbitCoordinates.toEquiv).trans
      (congrArg (fun X : Subgroup G => Nat.card X) hV.symm)
  rw [←hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  decide
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

/-- The literal Hall action is faithful for every genuine nontrivial cover.
The full center is excluded by the original faithful module action and its
native J4 embedding, rather than removed from the hypotheses. -/
theorem sourceOrbit_mathieu_hall_faithful_of_nontrivial_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hcenter : center D.orbitComponent ≠ ⊥)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H₀)
    (B₀ : Subgroup H₀) (hBN : B₀ ≤ (normalizer (L : Set G)).subgroupOf H₀)
    (hHall : IsHallSubgroup oddPrimes
      (B₀.subgroupOf ((normalizer (L : Set G)).subgroupOf H₀))) :
    B₀.map H₀.subtype ⊓ sectionCentralizer L = ⊥ := by
  by_contra hker
  obtain ⟨_,_,hmodel⟩ := @sourceOrbit_mathieu_hall_small_module G instG finG T L V D
    h hmany hV hm hnon H₀ hH hlarge B₀ hBN hHall hker
  apply hcenter
  rcases hmodel with h12 | h22
  · exact IsM12Heart.center_eq_bot (L := D.orbitComponent) (V := D.orbitSpace)
      (σ := D.orbitRepresentation.comp D.orbitComponent.subtype) h12.2
  · exact IsM22ToddOrDual.center_eq_bot (L := D.orbitComponent) (V := D.orbitSpace)
      (σ := D.orbitRepresentation.comp D.orbitComponent.subtype) h22.2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
