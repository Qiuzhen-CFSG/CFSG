module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.ModelRemainder
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.G2Exclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.JankoExclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Assembly
public import Theory.Representation.BinaryOffender.SylowCentral

/-!
# Pure-point core control, fusion and abelian closure

Select the original marked pure point and a central involution of the
original Sylow. The genuine 1.1.5 application gives a component unless the
point centralizer has characteristic two. The central point and quotient
rank reduce its actual model to G₂(4), Rudvalis or J₄; the three preceding
exclusions eliminate all of them. Pure-vector conjugacy transports the
characteristic-two conclusion to every required point.

The existing G.2 and two-conjugate arguments now give full core containment
and natural-section centrality. The original three centralizer orders then
supply fusion, abelian centralizer closure and intersection centralization.
Dimension five uses only its permitted positive weak-closure premise.
Dimension four retains exactly MarkedOmegaFixed, the unproved source-specific
MS consequence owned by qt-rank-two-ms93. Final discharge remains with
qt-d-double-natural-pure-fusion and qt-d-double-natural-centralizers;
no universal EarlierMSClassifications premise is used here.

Source: Aschbacher--Smith 12.1.4--6, printed pp.790--792/PDF pp.807--809.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All source 1.1.5 component alternatives are excluded at the marked pure
point, using the original ambient Sylow and exact component quotient. -/
theorem doubleNatural_marked_pure_characteristicTwo_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) := by
  let := D.doubledOrbit_elementary h
  intro S hns hs w hw hp hfix
  let W := componentOrbit V (T : Subgroup G)
  have hn := D.doubledOrbit_normalizer_eq h B.orbit_eq
  have hWT := (D.doubledOrbit_E322 h).le_sylow
  have hWne : W ≠ ⊥ := by
    intro he
    exact hw (Subtype.ext (mem_bot.mp (he ▸ w.property)))
  obtain ⟨z,hzW,hz,hzt⟩ := Representation.BinaryOffender.exists_sylow_central_involution_of_normal_elementary
    W T inferInstance hWne hWT (hn.symm ▸ D.sylow_normalizes_component)
  have hzT : z ∈ centerIn (T : Subgroup G) := ⟨hWT hzW,fun x hx => (hzt x hx).eq.symm⟩
  rcases D.doubleNatural_pure_component_alternative_of_many h hmany B S hns hs
      w hw hp hfix z hz hzT with hc | ⟨K,hK,_,_,hm⟩
  · exact hc
  obtain ⟨hKn,hX,hU⟩ := D.doubleNatural_pure_component_identification_of_many
    h hmany B S hns hs w hw hp hfix K hK
  let := hKn
  let := hK.2
  have hc : center K = pCore 2 K := IsQuasisimple.center_eq_pCore
    (hK.1.pPrimeCore_eq_bot (D.doubleNatural_pure_oddCore_eq_bot_of_many h hmany B S hns w hw hp) K)
  obtain ⟨v,_,hv,hv2⟩ := S.pure_component_central_point w hw hp K hU
  have hr := D.doubleNatural_pure_component_quotient_rank_of_many
    h hmany B S hns hs w hw hp hfix K hK
  have hr6 : 6 ≤ primeRank 2 (K ⧸ pCore 2 K) := by
    have hn : 4 ≤ n := by rcases B.degree with he | he <;> omega
    exact (show 6 ≤ 2*n-2 by omega).trans hr
  obtain ⟨a,_,ha⟩ := hm
  rcases DoubledBranch.SourceModel.model115_of_central_involution_of_six_le_rank
      a ha hc v hv hv2 hr6 with ⟨hg2,_⟩ | ⟨he,_⟩
  · exact (S.pure_component_not_g2_four hn w hw hp K hX hU hc hg2).elim
  · rcases he with he | he
    · obtain ⟨e⟩ := he
      exact (S.pure_component_not_rudvalis D.sylow_normalizes_component hn hs
        w hw hp hfix K hX hU hc e).elim
    · obtain ⟨e⟩ := he
      exact (S.pure_component_not_janko_four D.sylow_normalizes_component hn hs
        w hw hp hfix K hX hU hc e).elim

/-- Transport the proved marked-point characteristic-two conclusion to every
pure point along the original natural-vector orbit. -/
theorem doubleNatural_pure_characteristicTwo_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) := by
  let := D.doubledOrbit_elementary h
  intro S hns hs w hw hpw
  obtain ⟨v,hv,hpv,hfix⟩ := S.exists_marked_point D.sylow_normalizes_component
  have hc := D.doubleNatural_marked_pure_characteristicTwo_of_many
    h hmany B S hns hs v hv hpv hfix
  obtain ⟨m,_,he⟩ := (S.ambient_orbit_iff v w hv hw).mpr
    (Or.inl ⟨⟨hv,Or.inl hpv⟩,⟨hw,Or.inl hpw⟩⟩)
  have hmap : (B.pointCentralizer v).map (MulAut.conj m).toMonoidHom = B.pointCentralizer w := by
    change (centralizer ({(v : G)} : Set G)).map (MulAut.conj m).toMonoidHom =
      centralizer ({(w : G)} : Set G)
    rw [map_centralizer_singleton,he]
  let e := ((MulAut.conj m).subgroupMap (B.pointCentralizer v)).trans
    (MulEquiv.subgroupCongr hmap)
  apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hc)

/-- The complete independent pure-point geometry: the actual ambient Sylows
supply all three orders, core control, fusion, abelian closure and intersection
centralization. No local component or core callback remains. -/
theorem doubleNatural_pure_conclusions_of_marked_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureCoreControl ∧
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hns hs
  obtain ⟨ho,hps,_⟩ := D.doubleNatural_pure_orders_sylows_fusion_of_marked_of_many h hmany B S hns hs
  have hc := D.doubleNatural_pure_coreControl_of_characteristicTwo_of_many h hmany B S hps hns
    (D.doubleNatural_pure_characteristicTwo_of_many h hmany B S hns hs)
  exact ⟨ho,hps,hc,D.doubleNatural_pure_conclusions_of_orders_and_core_of_many h hmany B S ho hps hc⟩

/-- Both source degrees, with the sole remaining original MS fixed-subgroup
premise explicit in dimension four. Its existing producer is qt-rank-two-ms93;
final discharge remains with this task and qt-d-double-natural-centralizers. -/
theorem doubleNatural_pure_conclusions_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      (n = 4 → S.MarkedOmegaFixed D.sylow_normalizes_component) →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureCoreControl ∧
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hns hfixed
  exact D.doubleNatural_pure_conclusions_of_marked_of_many h hmany B S hns
    (D.doubleNatural_markedAmbientSylow_of_many_of_omega_fixed h hmany B hW S hfixed)

/-- In dimension five the permitted earlier positive weak-closure input
discharges the ambient Sylow, completing all original pure-point conclusions. -/
theorem doubleNatural_five_pure_conclusions_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureCoreControl ∧
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hns
  exact D.doubleNatural_pure_conclusions_of_many_of_omega_fixed h hmany B (fun _ => hW) S hns
    (fun he => by omega)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
