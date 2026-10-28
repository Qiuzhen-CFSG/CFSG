module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorAction

/-!
# Original unitary covers without a perfectness assumption

The regular factor-cover comparison is transported to the literal SU₃ or
PSU₃ marking. Its factor and canonical-root representative equations agree,
and its map to the same local permutation group is the actual scalar
projection in the special-unitary case. The full root-action kernel is its
center. The proof applies to every positive binary parameter, retaining (2B)
as an explicit premise at q = 2.

UnitaryFactorApplications discharges (2B) at q ≥ 4 and applies both versions
to the literal Chapter 12 pair. The full Borel and both original endpoint
maps remain those of the supplied marked quotient. This local comparison
does not supply exhaustive rank-two selection or the final amalgam Iso.
Source: Fong--Seitz I (5B)--(5C); AS F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
open HermitianForm
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)] (T : Sylow 2 (L i))
  (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 0 < n) (hc : Nat.card E = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

include hT hn hc hconj hV in
/-- Special-unitary whole-cover and local comparisons without original perfectness. -/
theorem specialUnitary_factor_comparison
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    letI := originalRadicalInClosure_normal Q e h split i
    ∃ a : originalRankOne Q e split i ≃* J.specialSubgroup,
      ∃ b : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ c : (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
            J.specialSubgroup,
          (∀ r, J.specialToProjective (a r) = b (originalRootProjection Q e split i r)) ∧
          (∀ r, c (QuotientGroup.mk' _ (inclusion (originalRankOne_le_localClosure Q e split i) r)) = a r) ∧
          (∀ l : L i, c (QuotientGroup.mk' _ (originalFactorIntoClosure Q e h split i l)) =
            ν (QuotientGroup.mk' (pCore 2 (L i)) l)) ∧
          (RootLocalCover.projection Q split i).ker = center (rankOne Q split i) := by
  let := originalRadicalInClosure_normal Q e h split i
  have hs := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hc hconj ν
  let a := (regularOriginalFactorRootEquiv Q e h split i T hT hV hs).trans ν
  let b := specialUnitaryFactorLocalEquiv Q e h split i T hT J hn hc hconj hV ν
  let c := (regularOriginalFactorCoverEquiv Q e h split i T hT hV hs).trans ν
  refine ⟨a,b,c,?_,?_,?_,regular_root_projection_ker_eq_center Q e h split i T hT hV hs⟩
  · intro r
    change J.specialToProjective (ν (regularOriginalFactorRootEquiv Q e h split i T hT hV hs r)) = _
    rw [← factorQuotientLocalMap_originalRoot Q e h split i T hT hV hs]
    exact (specialUnitaryFactorLocalEquiv_factor Q e h split i T hT J hn hc hconj hV ν _).symm
  · intro r
    change ν (regularOriginalFactorCoverEquiv Q e h split i T hT hV hs _) =
      ν (regularOriginalFactorRootEquiv Q e h split i T hT hV hs r)
    rw [regularOriginalFactorCoverEquiv_mk_root]
  · intro l
    change ν (regularOriginalFactorCoverEquiv Q e h split i T hT hV hs _) = _
    rw [regularOriginalFactorCoverEquiv_mk_factor]

include hT hn hc hconj hV in
/-- Projective-unitary whole-cover and local comparisons, including the regular q = 2 branch. -/
theorem projectiveUnitary_factor_comparison
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    letI := originalRadicalInClosure_normal Q e h split i
    ∃ a : originalRankOne Q e split i ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ b : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ c : (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
            ProjectiveSpecialUnitaryMatrixGroup J,
          (∀ r, a r = b (originalRootProjection Q e split i r)) ∧
          (∀ r, c (QuotientGroup.mk' _ (inclusion (originalRankOne_le_localClosure Q e split i) r)) = a r) ∧
          (∀ l : L i, c (QuotientGroup.mk' _ (originalFactorIntoClosure Q e h split i l)) =
            μ (QuotientGroup.mk' (pCore 2 (L i)) l)) := by
  let := originalRadicalInClosure_normal Q e h split i
  have hs := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hc hconj μ
  let a := (regularOriginalFactorRootEquiv Q e h split i T hT hV hs).trans μ
  let b := projectiveUnitaryFactorLocalEquiv Q e h split i T hT J hn hc hconj hV μ
  let c := (regularOriginalFactorCoverEquiv Q e h split i T hT hV hs).trans μ
  refine ⟨a,b,c,?_,?_,?_⟩
  · intro r
    change μ (regularOriginalFactorRootEquiv Q e h split i T hT hV hs r) = _
    rw [← factorQuotientLocalMap_originalRoot Q e h split i T hT hV hs]
    exact (projectiveUnitaryFactorLocalEquiv_factor Q e h split i T hT J hn hc hconj hV μ _).symm
  · intro r
    change μ (regularOriginalFactorCoverEquiv Q e h split i T hT hV hs _) =
      μ (regularOriginalFactorRootEquiv Q e h split i T hT hV hs r)
    rw [regularOriginalFactorCoverEquiv_mk_root]
  · intro l
    change μ (regularOriginalFactorCoverEquiv Q e h split i T hT hV hs _) = _
    rw [regularOriginalFactorCoverEquiv_mk_factor]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
