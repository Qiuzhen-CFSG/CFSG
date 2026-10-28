module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalEffectiveRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# The original two-core Frattini identity

The actual marked endpoint equivalence identifies its two-core with the
Suzuki radical. Transporting the source proof of Φ(V)=[V,V] gives the
intrinsic identity and its full image under the original endpoint map.
The specialization uses literally Q.q composed with the original inclusion;
the original ambient group may be infinite.

Source: Fong--Seitz I (1973), (6H)(f), printed p.55. Hypothesis F.1.1
discharges the Borel-core and two-core-centralizer assumptions.
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

include e split ν hC μ hB hn in
/-- The actual original two-core has elementary abelian abelianization. -/
theorem original_source_radical_frattini_eq_commutator
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    frattini (pCore 2 (parabolic L S 1)) = _root_.commutator (pCore 2 (parabolic L S 1)) := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let f := originalRadicalEquiv Q e split 1 hV
  apply map_injective (f := f.toMonoidHom) f.injective
  rw [frattini_map_equiv,map_commutator_eq,MonoidHom.range_eq_top.mpr f.surjective]
  exact source_radical_frattini_eq_commutator Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

include ν hC μ hB hn in
/-- The source derived radical is the image of the original two-core Frattini subgroup. -/
theorem original_source_radical_frattini_image
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (frattini (pCore 2 (parabolic L S 1))).map
      ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) =
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let f := originalRadicalEquiv Q e split 1 hV
  have he : (endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype =
      (simpleRemainder Q split 1).subtype.comp f.toMonoidHom := by
    ext x
    exact (originalRadicalEquiv_apply Q e split 1 hV x).symm
  rw [he,←map_map,frattini_map_equiv]
  exact (source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)).symm

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

include split ν hC μ hB hn in
/-- Intrinsic Frattini equality for the same source quotient and original endpoint. -/
theorem original_source_radical_frattini_eq_commutator_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    frattini (pCore 2 (parabolic L S 1)) = _root_.commutator (pCore 2 (parabolic L S 1)) := by
  exact original_source_radical_frattini_eq_commutator Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- The full literal Q.q image of the original Frattini subgroup, including q=2. -/
theorem original_source_radical_frattini_image_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (frattini (pCore 2 (parabolic L S 1))).map
      ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
        (pCore 2 (parabolic L S 1)).subtype) =
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_radical_frattini_image Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
