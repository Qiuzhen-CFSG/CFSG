module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedFrattini

/-!
# The exact five factors in the original two-core

Hypothesis F.1.1 discharges the faithful Borel and local characteristic-two
inputs to the derived-product theorem. The original endpoint map identifies
its Frattini subgroup with the five factors, hence with an elementary
abelian group of order q⁵. The specialization keeps the literal Q.q and
endpoint inclusion, even when the original ambient group is infinite.
Source: Fong--Seitz I (1973), (6H)(f), printed p.55.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include ν hC μ hB hn in
/-- The original two-core Frattini image is exactly the five source factors. -/
theorem original_source_radical_frattini_eq_five
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (frattini (pCore 2 (parabolic L S 1))).map
      ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) =
      fiveDerivedSubgroup Q split := by
  rw [original_source_radical_frattini_image Q e split n hn m ν T hC μ hB h hm]
  exact source_radical_derived_eq_five Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

include e split ν hC μ hB hn in
/-- The actual original Frattini subgroup is elementary abelian of order q⁵. -/
theorem original_source_radical_frattini_data
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    IsElementaryAbelian 2 (frattini (pCore 2 (parabolic L S 1))) ∧
      Nat.card (frattini (pCore 2 (parabolic L S 1))) = (2^(2*m+1))^5 := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let f := originalRadicalEquiv Q e split 1 hV
  let j := (simpleRemainder Q split 1).subtype.comp f.toMonoidHom
  have hj : Function.Injective j := (simpleRemainder Q split 1).subtype_injective.comp f.injective
  have he : j = (endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype := by
    ext x
    exact originalRadicalEquiv_apply Q e split 1 hV x
  have hi : (frattini (pCore 2 (parabolic L S 1))).map j = fiveDerivedSubgroup Q split := by
    rw [he]
    exact original_source_radical_frattini_eq_five Q e split n hn m ν T hC μ hB h hm
  let a := ((frattini (pCore 2 (parabolic L S 1))).equivMapOfInjective j hj).trans
    (MulEquiv.subgroupCongr hi)
  let : IsElementaryAbelian 2 (fiveDerivedSubgroup Q split) :=
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm
      (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)).1
  exact ⟨IsElementaryAbelian.of_injective a.toMonoidHom a.injective,
    (Nat.card_congr a.toEquiv).trans (source_five_derived_card Q split n hn m ν T hC μ hB hm
      (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1))⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include ν hC μ hB hn in
/-- The equality uses literally Q.q and the original endpoint inclusion. -/
theorem original_source_radical_frattini_eq_five_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (frattini (pCore 2 (parabolic L S 1))).map
      ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
        (pCore 2 (parabolic L S 1)).subtype) = fiveDerivedSubgroup Q split := by
  rw [original_source_radical_frattini_image_quotient Q split n hn m ν T hC μ hB h hm]
  exact source_radical_derived_eq_five Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q (originalMarkedIso Q) h)
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h 1)

include split ν hC μ hB hn in
/-- The same elementary abelian order statement on the original source quotient. -/
theorem original_source_radical_frattini_data_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    IsElementaryAbelian 2 (frattini (pCore 2 (parabolic L S 1))) ∧
      Nat.card (frattini (pCore 2 (parabolic L S 1))) = (2^(2*m+1))^5 :=
  original_source_radical_frattini_data Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
