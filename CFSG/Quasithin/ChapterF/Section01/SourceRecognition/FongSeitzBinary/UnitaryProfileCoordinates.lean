module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryProfileRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalAllFields
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
variable {G X E : Type*} [Group G] [Group X] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : Nat.card ((parabolic L S j).pCoreIn 2) = (2^n)^7)
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
include e h hn hE hJ hconj hm hij hfactor hindexi hindexj hQi hQj hderived hfrattini

theorem marked_unitary_profile_coordinates :
    letI := MarkedLocal.originalRadicalInClosure_normal Q e h split j
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ hr : ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q e k) =
        pCore 2 (parabolic L S k),
    ∃ (ξ : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
      (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (γ : (MarkedLocal.originalLocalClosure Q e split j ⧸
        MarkedLocal.originalRadicalInClosure Q e split j) ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ r, ν (RootLocalCover.projection Q split j r) = J.specialToProjective (κ r)) ∧
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q e h split j l) =
        J.specialToProjective (ξ l)) ∧
      (RootLocalCover.projection Q split j).ker = center (rankOne Q split j) ∧
      (∀ l : L j, γ (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e h split j l)) =
        ξ (QuotientGroup.mk' (pCore 2 (L j)) l)) ∧
      (∀ r : MarkedLocal.originalRankOne Q e split j,
        γ (QuotientGroup.mk' _ (inclusion (MarkedLocal.originalRankOne_le_localClosure Q e split j) r)) =
          κ (MarkedLocal.originalRankOneEquiv Q e split j r)) ∧
      ∀ r v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j (hr j).1) r v) = Matrix.mulVec (κ r).val.val (c v) := by
  let := MarkedLocal.originalRadicalInClosure_normal Q e h split j
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  have hr := QuadrangleStructure.marked_unitary_profile_regularity Q e h split hm i j hij
    (2^n) (pow_pos (by decide) n) hindexi hindexj hQi hQj
  obtain ⟨ν,π,hπ,hπν⟩ := MarkedLocal.regular_unitary_cover_of_factor Q e h split
    J hn hE hconj j (hr j).1 hfactor
  have hfixed : Nat.card {x : E // J.conj x = x} = 2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
  obtain ⟨κ,c,_,hpanel,hc⟩ := marked_natural_coordinates_all Q split e h J hn hE hfixed hJ hconj
    hm i j hij (hr i).1 (hr j).1 (UnitarySource.actorReflection Q split j) ν π hπ hπν
    hindexi hindexj hQi hderived hfrattini
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  have hcount : Nat.card (simpleRoot Q split j) = Nat.card (quotientSylow T) := by
    rcases hfactor with hs | hp
    · obtain ⟨a⟩ := hs
      exact MarkedLocal.specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J hn hE hconj a
    · obtain ⟨a⟩ := hp
      exact MarkedLocal.projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J hn hE hconj a
  let a := MarkedLocal.regularFactorRootEquiv Q e h split j T hT (hr j).1 hcount
  let ξ := a.symm.trans κ
  let γ := (MarkedLocal.regularOriginalFactorCoverEquiv Q e h split j T hT (hr j).1 hcount).trans ξ
  refine ⟨hr,ξ,ν,κ,γ,c,hpanel,?_,
    MarkedLocal.regular_root_projection_ker_eq_center Q e h split j T hT (hr j).1 hcount,?_,?_,hc⟩
  · intro l
    have he := MarkedLocal.factorQuotientLocalMap_regularRoot Q e h split j T hT
      (hr j).1 hcount (a.symm l)
    change MarkedLocal.factorQuotientLocalMap Q e h split j (a (a.symm l)) = _ at he
    rw [a.apply_symm_apply] at he
    rw [he,hpanel]
    rfl
  · intro l
    change ξ (MarkedLocal.regularOriginalFactorCoverEquiv Q e h split j T hT (hr j).1 hcount _) = _
    rw [MarkedLocal.regularOriginalFactorCoverEquiv_mk_factor]
  · intro r
    change ξ (MarkedLocal.regularOriginalFactorCoverEquiv Q e h split j T hT (hr j).1 hcount _) = _
    rw [MarkedLocal.regularOriginalFactorCoverEquiv_mk_root,MarkedLocal.regularOriginalFactorRootEquiv_apply]
    change κ (a.symm (a (MarkedLocal.originalRankOneEquiv Q e split j r))) = _
    rw [a.symm_apply_apply]
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
variable {G E : Type*} [Group G] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : Nat.card ((parabolic L S j).pCoreIn 2) = (2^n)^7)
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
include h hn hE hJ hconj hm hij hfactor hindexi hindexj hQi hQj hderived hfrattini

/-- The same natural action on literal source quotient representatives, with
both original core preimages and the original factor's projective square. -/
theorem original_unitary_profile_representatives :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ _hr : ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q (originalMarkedIso Q) k) =
        pCore 2 (parabolic L S k),
    ∃ (ξ : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
      (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ r, ν (RootLocalCover.projection Q split j r) = J.specialToProjective (κ r)) ∧
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q (originalMarkedIso Q) h split j l) =
        J.specialToProjective (ξ l)) ∧
      (RootLocalCover.projection Q split j).ker = center (rankOne Q split j) ∧
      ∀ (a v : generated L S) (ha : Q.q a ∈ rankOne Q split j)
        (hv : Q.q v ∈ simpleRemainder Q split j),
        ∃ w : simpleRemainder Q split j,
          (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
          c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w)) =
            Matrix.mulVec (κ ⟨Q.q a,ha⟩).val.val
              (c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j))
                ⟨Q.q v,hv⟩))) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨hr,ξ,ν,κ,γ,c,hpanel,hfactorSquare,hker,_,_,hc⟩ := marked_unitary_profile_coordinates
    Q split (originalMarkedIso Q) h J hn hE hJ hconj hm i j hij hfactor
    hindexi hindexj hQi hQj hderived hfrattini
  refine ⟨hr,ξ,ν,κ,c,hpanel,hfactorSquare,hker,?_⟩
  intro a v ha hv
  let w := remainderRankOneAction Q split j (hr j).1 ⟨Q.q a,ha⟩ ⟨Q.q v,hv⟩
  refine ⟨w,?_,?_⟩
  · rw [remainderRankOneAction_apply,map_mul,map_mul,map_inv]
  · have he := hc ⟨Q.q a,ha⟩ (Additive.ofMul (QuotientGroup.mk'
      (frattini (simpleRemainder Q split j)) ⟨Q.q v,hv⟩))
    change c (Additive.ofMul (remainderFrattiniAction Q split j (hr j).1 ⟨Q.q a,ha⟩
      (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) ⟨Q.q v,hv⟩))) = _ at he
    rw [remainderFrattiniAction_mk] at he
    exact he
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

