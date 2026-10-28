module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows.Classification
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.UnitaryExclusion
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.NativeLinearFive
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.Reductions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.RowExclusions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.CenterBounds
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical.Ordinary
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.OrdinaryModels

/-!
# Large-center radical reductions for the original Chapter 13 J₄ component

The original covering relation supplies the intersection residual's unitary
quotient and relative normality. Apply the ordinary central-quotient transports
to that same residual, radical, full module and component. The full native
radical normalizer consequently cannot lie in either certified small-center
local. Its normal unitary residual also excludes each of the three simple
quotient rows. The actual kernel and octad-preimage rows and every ambient
conjugate are consequently excluded. The bound on the elementary Mathieu
image now excludes the entire Mathieu local branch by its centralizer and
automorphism sections. The proved native full-core quotient excludes every
conjugate linear-five local without an additional quotient premise. The native
coverage theorem and terminal
J₄ exclusion are not asserted here.

Source: Aschbacher--Smith 4.2.13, pp.611--612, and its application in 13.3.16;
An--O'Brien--Wilson (2003), Section 4 and Table 1, pp.122,124.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers Chapter12.Section02
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal original intersection residual is normal in the native
large-center radical normalizer, with its actual unitary quotient retained. -/
theorem unitary_original_pushingUp_janko_radical
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let Dk := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := Dk.map f
    let N := normalizer (P : Set Janko4.Model)
    let B := ((Y.subgroupOf H).subgroupOf K).map f
    IsPRadical 2 P ∧ 64 ≤ Nat.card (center P) ∧
      B ≤ N ∧ (B.subgroupOf N).Normal ∧
      Nonempty ((B.subgroupOf N ⧸ pCore 2 (B.subgroupOf N)) ≃*
        commutator (Atlas.G2.Model (ZMod 2))) := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,a,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  obtain ⟨_,_,hP,_,_,hlarge⟩ := hc.unitary_ordinary_janko_radical (a.trans s.quotient) K hK e
  exact ⟨hP,hlarge,hc.unitary_ordinary_janko_normal_residual (a.trans s.quotient)
    ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn) K hK e⟩

/-- The original Chapter 13 configuration excludes both small-center local
branches at the level of its entire native radical normalizer. -/
theorem unitary_original_pushingUp_janko_small_local_exclusions
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model)
    (M0 : Subgroup Janko4.Model)
    (he : Nonempty (M0 ≃*
        Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.sourceSubgroup) ∨
      Nonempty (M0 ≃* Janko4.LocalStructure.SymmetricLinear.max4Subgroup)) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    ¬ normalizer (P : Set Janko4.Model) ≤ M0 := by
  obtain ⟨hP,hlarge,_⟩ := unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  rcases he with hb | hb
  · obtain ⟨b⟩ := hb
    exact Janko4.LocalStructure.LargeCenterRadicals.normalizer_not_le_max2 _ M0 hP hlarge b
  · obtain ⟨b⟩ := hb
    exact Janko4.LocalStructure.LargeCenterRadicals.normalizer_not_le_max4 _ M0 hP hlarge b

/-- The literal original J₄ configuration is incompatible with every simple
quotient row in the large-center radical list. Global coverage of that list is
still required to turn this incompatibility into the terminal exclusion. -/
theorem unitary_original_pushingUp_janko_quotients_excluded
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    let N := normalizer (P : Set Janko4.Model)
    ¬ (Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
       Nonempty ((N ⧸ pCore 2 N) ≃* Sporadic.Mathieu.M24) ∨
       Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 8))) := by
  obtain ⟨_,_,_,hn,⟨a⟩⟩ := unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  let := hn
  exact Janko4.LocalStructure.LargeCenterRadicals.unitary_normal_residual_quotients_excluded _ a

open Janko4.LocalStructure.LargeCenterRadicals.MathieuRows

/-- The actual original radical is in neither computed Mathieu row family,
including all ambient conjugates and with the original module maps retained. -/
theorem unitary_original_pushingUp_janko_not_mathieu_rows
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    (∀ g : Janko4.Model, P ≠
      Janko4.LocalStructure.ElementaryNormalizerCover.embeddedKernel.map
        (MulAut.conj g).toMonoidHom) ∧
    ∀ (O : Sporadic.Mathieu.M24LocalGeometry.Octad) (g : Janko4.Model),
      P ≠ (octadRadical O).map (MulAut.conj g).toMonoidHom :=
  not_mathieu_rows_of_quotients_excluded _
    (unitary_original_pushingUp_janko_quotients_excluded s hcover hJH hc K hK e)

/-- In the remaining Mathieu branch, the literal radical image is elementary
of order at most sixteen. The original full module supplies the center bound;
the Mathieu placement remains the branch condition, not a cover assumption. -/
theorem unitary_original_pushingUp_janko_mathieu_image_small
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    let A := (P.subgroupOf Janko4.LocalStructure.ElementaryNormalizerCover.max1).map
      Janko4.LocalStructure.MathieuHallActors.projection
    normalizer (P : Set Janko4.Model) ≤ Janko4.LocalStructure.ElementaryNormalizerCover.max1 →
      IsElementaryAbelian 2 A ∧ Nat.card A ≤ 16 := by
  intro f P A hN
  obtain ⟨hP,hlarge,_⟩ := unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  exact radical_mathieu_image_small P hP hN hlarge

/-- A unitary residual cannot enter a conjugate linear-five local: its order
has a factor 27, while the binary extension of SL₅(2) does not. The exact
native quotient remains the independent F producer's explicit premise. -/
theorem unitary_original_pushingUp_janko_not_linearFive_local
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model)
    (eF : ((normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)) ⧸
      pCore 2 (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model))) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    ∀ g : Janko4.Model, ¬ normalizer (P : Set Janko4.Model) ≤
      (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)).map
        (MulAut.conj g).toMonoidHom := by
  intro f P g hle
  obtain ⟨_,_,_,_,⟨b⟩⟩ := unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  exact Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal.unitary_residual_not_embed_linearFive
    b (Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal.nativeConjugateQuotientEquiv eF g)
    ((inclusion hle).comp (Subgroup.subtype _))
    ((inclusion_injective hle).comp (Subgroup.subtype_injective _))

/-- The arbitrary linear-five radical quotient calculation excludes every
conjugate placement of the original radical. The original whole module supplies
the center bound, and the whole-normal residual excludes both SL₅(2) and A₈. -/
theorem unitary_original_pushingUp_janko_not_recognized_linearFive_local
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    ∀ g : Janko4.Model, ¬ normalizer (P : Set Janko4.Model) ≤
      (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)).map
        (MulAut.conj g).toMonoidHom := by
  intro f P g
  obtain ⟨hP,hlarge,_⟩ := unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  exact Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows.not_le_conjugate_of_quotients_excluded
    P hP hlarge (unitary_original_pushingUp_janko_quotients_excluded s hcover hJH hc K hK e) g

/-- The original whole module and unitary residual exclude every conjugate
Mathieu local. Nontrivial Mathieu images use their actual conjugation kernel;
the trivial image uses normality in the entire radical normalizer. -/
theorem unitary_original_pushingUp_janko_not_mathieu_local
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    ∀ g : Janko4.Model, ¬ normalizer (P : Set Janko4.Model) ≤
      Janko4.LocalStructure.ElementaryNormalizerCover.max1.map
        (MulAut.conj g).toMonoidHom := by
  intro f P g
  obtain ⟨hP,hlarge,_,hn,⟨b⟩⟩ := unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  let := hn
  exact unitary_radical_normalizer_not_le_mathieu_conjugate P hP hlarge _ b g

/-- The same original radical and whole module supply a large fixed space
under the literal recognized SL₅ action, whenever this local branch occurs. -/
theorem unitary_original_pushingUp_janko_linear_image_large
    (s : Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := (((J.pCoreIn 2).subgroupOf H).subgroupOf K).map f
    normalizer (P : Set Janko4.Model) ≤ Janko4.LocalStructure.LinearFive.fullNormalizer →
      64 ≤ Nat.card (Representation.BinaryOffender.fixedSpace
        (Representation.SL5TenDimensional.exteriorAction 2)
        (Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows.image P)) := by
  intro f P hN
  obtain ⟨hP,hlarge,_⟩ := unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  exact Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows.large_fixedSpace P hP hN hlarge

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
