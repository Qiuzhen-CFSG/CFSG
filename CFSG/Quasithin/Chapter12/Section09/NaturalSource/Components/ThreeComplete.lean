module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.ThreeRadical
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality

/-!
# The degree-five three-space assertion and complete component geometry

A strict three-space component has a characteristic seven-radical of rank
two. Its detected ordinary component orbit in G₁ must coincide with the
normal point component: otherwise that orbit centralizes the original
PSL₄(2) residual, giving seven-rank at least three in the SQTK point local.
The point component would then have seven-rank at least two, contrary to
the actual orders of PSL₄(2), PSL₅(2), M₂₄ and J₄.

This proves K₃=L₃ with normality in N_G(V₃), and assembles the entire
original degree-five ComponentGeometry. The degree-four cases, nonnormal
abelianity and original local-control proofs remain with the natural-source
assembly owner; this does not yet assert NaturalBranchInput.
Source: Aschbacher--Smith 12.9.3, printed p.858.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- A strict three-space radical forces the original normal point component to have a quasisimple two-core quotient of seven-rank at least two. -/
theorem five_three_radical_forces_point_seven_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) {K C : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.Gi 3))
    (hLK : F.Li L 3 ≤ K) (hN : (K.subgroupOf (F.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (hC : C ∈ Chapter1.cComponentsIn (F.H))
    (hLC : F.Li L 1 ≤ C) (hNC : (C.subgroupOf (F.H)).Normal) :
    IsQuasisimple (C ⧸ pCore 2 C) ∧ 2 ≤ primeRank 7 (C ⧸ pCore 2 C) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨Q,hQ,hqQ,hXQ,_⟩ := three_radical_point_component_orbit h (Or.inr rfl) earlier F hK hLK hN hn
  let H := F.H
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (F.Li L 1).subgroupOf H
  let C₀ := C.subgroupOf H
  let Q₀ := Q.subgroupOf H
  let X := Chapter1.XiP 7 K
  let X₀ := X.subgroupOf H
  have hXH : X ≤ H := three_radical_le_point h (Or.inr rfl) F hK.1 hLK
  let a : Q₀ ≃* Q := subgroupOfEquivOfLe hQ.1
  let e : (Q ⧸ pCore 2 Q) ≃* Q₀.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hQ.2)
  let := hqQ
  let : IsQuasisimple (Q₀.map q) := IsQuasisimple.of_mulEquiv e
  have hQo : IsComponent (H ⧸ pCore 2 H) (Q₀.map q) :=
    ⟨(hQ.2.map_quotient _).subnormal,inferInstance⟩
  let : C₀.Normal := hNC
  let : (C₀.map q).Normal := Normal.map hNC q (QuotientGroup.mk'_surjective _)
  let b : B ≃* F.Li L 1 := subgroupOfEquivOfLe ((F.Li_le L 1).trans inf_le_right)
  let := h.chosen.elementary
  let : IsQuasisimple (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) :=
    Li_core_quasisimple F h.naturalMarking 1 (Or.inl ⟨rfl,by decide,by decide⟩)
  have hbtop := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (F.Li L 1)) pCore_isPGroup (Li_twoPerfect F 1)
  let := hbtop.perfect
  let : Group.IsPerfect (F.Li L 1) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := F.Li L 1)).toMonoidHom) topEquiv.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  obtain ⟨d,hd,_,⟨eL⟩⟩ := Li_core_linear F h.naturalMarking 1 (Or.inl ⟨rfl,by decide,by decide⟩)
  norm_num at hd
  rw [hd] at eL
  let bq : (B ⧸ pCore 2 B) ≃* SL(4,ZMod 2) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (eL.trans (slEquivLinear 4).symm)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup SL(4,ZMod 2) := (projectiveEquivSL (by decide : 0 < 4)).symm.isSimpleGroup
  let : IsSimpleGroup (B ⧸ pCore 2 B) := bq.isSimpleGroup
  let f := q.subgroupMap B
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsPerfect (B.map q) := Group.IsPerfect.ofSurjective (f := f) (q.subgroupMap_surjective B)
  let eb := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f (q.subgroupMap_surjective B)
  let : IsSimpleGroup ((B.map q) ⧸ pCore 2 (B.map q)) := eb.symm.isSimpleGroup
  have hzle : center (B.map q) ≤ pCore 2 (B.map q) := by
    rw [←PerfectCoreTwoExtension.radical_eq_core (G := B.map q)]
    exact le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm fun x y => Subtype.ext (mem_center_iff.mp x.property y).symm)
  have hz : Nat.Coprime 7 (Nat.card (center (B.map q))) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hzle).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 7 2).pow_right n
  have hqker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hrB : 1 ≤ primeRank 7 (B.map q) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hqker,
      ←primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 B) pCore_isPGroup]
    have hbcard : Nat.card (B ⧸ pCore 2 B) = 20160 :=
      (Nat.card_congr bq.toEquiv).trans Atlas.Order20160A8.sl4Two_card
    by_contra hr
    have hz0 : primeRank 7 (B ⧸ pCore 2 B) = 0 := by omega
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz0
    exact hh (by rw [hbcard]; decide)
  have hrX : 2 ≤ primeRank 7 (X₀.map q) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hqker,
      primeRank_congr 7 (subgroupOfEquivOfLe hXH)]
    exact three_radical_seven_rank h (Or.inr rfl) F hK hLK hN hn
  have hXorb : X₀.map q ≤ componentOrbit (Q₀.map q) (((T : Subgroup G).subgroupOf H).map q) := by
    have hh := map_mono (f := q) (comap_mono (f := H.subtype) hXQ)
    exact hh.trans_eq (Chapter1.XiEmbedding.quotientImage_componentOrbit_source
      H Q (T : Subgroup G) hQ.1 (F.invariant 1))
  have hrH : primeRank 7 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 7 (by decide) _ pCore_isPGroup).trans
      ((h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))).stronglyQuasithin
        7 (by decide) (by decide))
  have he : Q₀.map q = C₀.map q := hQo.eq_normal_cComponent_of_orbit_rank
    (B := B.map q) (hC.2.map_quotient _) (map_mono (comap_mono hLC)) hXorb hz (by omega)
  have he₀ : Q₀ = C₀ := hQ.2.eq_of_map_quotient_eq hC.2 _ he
  have heQ : Q = C := by
    have hh := congrArg (map H.subtype) he₀
    exact (map_subgroupOf_eq_of_le hQ.1).symm.trans
      (hh.trans (map_subgroupOf_eq_of_le hC.1))
  subst Q
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hC.1).mp hNC)
  have hXC : X ≤ C := hXQ.trans (iSup_conjugates_le_of_le_normalizer C (T : Subgroup G) C le_rfl hTC)
  refine ⟨hqQ,?_⟩
  rw [primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 C) pCore_isPGroup]
  exact (three_radical_seven_rank h (Or.inr rfl) F hK hLK hN hn).trans (primeRank_mono 7 hXC)

private theorem large_point_seven_rank {A : Type*} [Group A] [Finite A]
    (hm : ClassicalGroup.IsPSL A 5 2 ∨ Nonempty (A ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (A ≃* Janko4.Model)) : primeRank 7 A ≤ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply primeRank_le_of_prime_pow_not_dvd
  rcases hm with hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF
    let a := (e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5))
    rw [Nat.card_congr a.toEquiv,Representation.SL5ExteriorSquare.card_specialLinearFive]
    decide
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m24_order]
    decide
  · rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card]
    decide


/-- Each actual degree-five point quotient has seven-rank at most one. -/
theorem five_point_component_seven_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn F.H) (hLC : F.Li L 1 ≤ C) :
    primeRank 7 (C ⧸ pCore 2 C) ≤ 1 := by
  rcases five_endpoint_component_models h earlier F 1 (Or.inl rfl) C hC hLC with he | hm
  · subst C
    let := h.chosen.elementary
    obtain ⟨d,hd,_,⟨e⟩⟩ := Li_core_linear F h.naturalMarking 1 (Or.inl ⟨rfl,by decide,by decide⟩)
    norm_num at hd
    rw [hd] at e
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    apply primeRank_le_of_prime_pow_not_dvd
    rw [Nat.card_congr (e.trans (slEquivLinear 4).symm).toEquiv, Atlas.Order20160A8.sl4Two_card]
    decide
  · exact large_point_seven_rank hm

/-- The original degree-five three-space component has quasisimple
quotient: its nonquasisimple radical contradicts the point seven-rank bound. -/
theorem five_three_component_quasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 3)) (hLD : F.Li L 3 ≤ D)
    (hN : (D.subgroupOf (F.Gi 3)).Normal) : IsQuasisimple (D ⧸ pCore 2 D) := by
  by_contra hq
  obtain ⟨C,hC,hLC,hNC,_⟩ := exists_five_point_component h earlier F
  have hr := (five_three_radical_forces_point_seven_rank h earlier F hD hLD hN hq hC hLC hNC).2
  have hb := five_point_component_seven_rank h earlier F hC hLC
  omega

/-- The complete degree-five three-space assertion of 12.9.3, with the
original solvable residual and normality in its literal normalizer. -/
theorem five_three_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) :
    ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 3
    (Or.inl ⟨rfl,by decide,by decide⟩)
  let := h.chosen.elementary
  have he := component_eq_of_quasisimple h earlier F 3 (by decide) (by decide)
    D hd.1 hd.2.1 hd.2.2 (five_three_component_quasisimple h earlier F hd.1 hd.2.1 hd.2.2)
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- All clauses of the original degree-five component assertion, with no
remaining component-comparison premise. Abelianity is a separate obligation. -/
theorem five_componentGeometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) : Nonempty (ComponentGeometry F L) :=
  five_componentGeometry_of_three_component h earlier F (five_three_component h earlier F)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
