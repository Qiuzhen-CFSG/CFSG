module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourEven
/-!
# Degree-four component geometry when the point residual is normal

A nonquasisimple three-space enlargement has a characteristic seven-radical
of rank at least two. Its detected ordinary component orbit in G₁ must
coincide with the normal point component: otherwise the original SL₃(2)
residual adds a third seven-rank, contradicting SQTK. The point component
therefore has quasisimple quotient of seven-rank at least two.

When K₁=L₁ its quotient has order 168, excluding this obstruction and
proving K₃=L₃ with normality in the literal three-space normalizer. The
existing commutator-form argument gives abelianity of the original point
span. This constructs the unchanged degree-four ComponentGeometry and
applies it to all the rank-one and even rank-two comparisons, including
both signs of the even classical covering groups. The full component
catalogue and nonnormal abelianity remain with the natural-source owner.
Source: Aschbacher--Smith 12.9.3--4, pp.858--859; the orbit-rank argument
extends the checked degree-five construction to the original SL₃(2) point.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- A strict three-space radical forces the original normal point component to have a quasisimple two-core quotient of seven-rank at least two. -/
theorem four_three_radical_point_data
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) {K C : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.Gi 3))
    (hLK : F.Li L 3 ≤ K) (hN : (K.subgroupOf (F.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (hC : C ∈ Chapter1.cComponentsIn (F.H))
    (hLC : F.Li L 1 ≤ C) (hNC : (C.subgroupOf (F.H)).Normal) :
    (IsQuasisimple (C ⧸ pCore 2 C) ∧ 2 ≤ primeRank 7 (C ⧸ pCore 2 C)) ∧
      Chapter1.XiP 7 K ≤ C := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨Q,hQ,hqQ,hXQ,_⟩ := three_radical_point_component_orbit h (Or.inl rfl) earlier F hK hLK hN hn
  let H := F.H
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (F.Li L 1).subgroupOf H
  let C₀ := C.subgroupOf H
  let Q₀ := Q.subgroupOf H
  let X := Chapter1.XiP 7 K
  let X₀ := X.subgroupOf H
  have hXH : X ≤ H := three_radical_le_point h (Or.inl rfl) F hK.1 hLK
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
    Li_core_quasisimple F h.naturalMarking 1 (Or.inr ⟨rfl,Or.inl rfl⟩)
  have hbtop := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (F.Li L 1)) pCore_isPGroup (Li_twoPerfect F 1)
  let := hbtop.perfect
  let : Group.IsPerfect (F.Li L 1) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := F.Li L 1)).toMonoidHom) topEquiv.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  obtain ⟨d,hd,_,⟨eL⟩⟩ := Li_core_linear F h.naturalMarking 1 (Or.inr ⟨rfl,Or.inl rfl⟩)
  norm_num at hd
  rw [hd] at eL
  let bq : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (eL.trans (slEquivLinear 3).symm)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup SL(3,ZMod 2) := (projectiveEquivSL (by decide : 0 < 3)).symm.isSimpleGroup
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
    have hbcard : Nat.card (B ⧸ pCore 2 B) = 168 :=
      (Nat.card_congr bq.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
    by_contra hr
    have hz0 : primeRank 7 (B ⧸ pCore 2 B) = 0 := by omega
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz0
    exact hh (by rw [hbcard]; decide)
  have hrX : 2 ≤ primeRank 7 (X₀.map q) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hqker,
      primeRank_congr 7 (subgroupOfEquivOfLe hXH)]
    exact three_radical_seven_rank h (Or.inl rfl) F hK hLK hN hn
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
  refine ⟨⟨hqQ,?_⟩,hXC⟩
  rw [primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 C) pCore_isPGroup]
  exact (three_radical_seven_rank h (Or.inl rfl) F hK hLK hN hn).trans (primeRank_mono 7 hXC)

/-- The seven-rank consequence of the detected radical containment. -/
theorem four_three_radical_forces_point_seven_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) {K C : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.Gi 3))
    (hLK : F.Li L 3 ≤ K) (hN : (K.subgroupOf (F.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (hC : C ∈ Chapter1.cComponentsIn (F.H))
    (hLC : F.Li L 1 ≤ C) (hNC : (C.subgroupOf (F.H)).Normal) :
    IsQuasisimple (C ⧸ pCore 2 C) ∧ 2 ≤ primeRank 7 (C ⧸ pCore 2 C) :=
  (four_three_radical_point_data h earlier F hK hLK hN hn hC hLC hNC).1

/-- The degree-four three-space assertion follows whenever the original
normal point component has seven-rank at most one. -/
theorem four_three_component_of_point_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn F.H) (hLC : F.Li L 1 ≤ C)
    (hNC : (C.subgroupOf F.H).Normal)
    (hr : primeRank 7 (C ⧸ pCore 2 C) ≤ 1) :
    ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 3
    (Or.inr ⟨rfl,Or.inr rfl⟩)
  have hq : IsQuasisimple (D ⧸ pCore 2 D) := by
    by_contra hn
    have hh := (four_three_radical_forces_point_seven_rank h earlier F
      hd.1 hd.2.1 hd.2.2 hn hC hLC hNC).2
    omega
  let := h.chosen.elementary
  have he := component_eq_of_quasisimple h earlier F 3 (by decide) (by decide)
    D hd.1 hd.2.1 hd.2.2 hq
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- In the normal point-residual case, degree four has the complete original
component geometry and an abelian point span. -/
theorem four_abelian_componentGeometry_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    IsMulCommutative F.U ∧ Nonempty (ComponentGeometry F L) := by
  have hl : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  let := h.chosen.elementary
  let a := subgroupOfEquivOfLe hl
  let : IsQuasisimple (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) :=
    Li_core_quasisimple F h.naturalMarking 1 (Or.inr ⟨rfl,Or.inl rfl⟩)
  let : IsQuasisimple (((F.Li L 1).subgroupOf F.H) ⧸
      pCore 2 ((F.Li L 1).subgroupOf F.H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  have hp := Li_twoPerfect F (L := L) 1
  have hp' : IsPPerfect 2 ((F.Li L 1).subgroupOf F.H) :=
    hp.of_surjective a.symm.toMonoidHom a.symm.surjective
  have hc : ((F.Li L 1).subgroupOf F.H).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal hp'
  have hr : primeRank 7 (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) ≤ 1 := by
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    apply primeRank_le_of_prime_pow_not_dvd
    rw [Nat.card_congr (Li_three_core_equiv h F 1 (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some.toEquiv,
      Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  have h3 := four_three_component_of_point_rank h earlier F ⟨hl,hc⟩ le_rfl hn hr
  refine ⟨point_span_abelian_of_point_residual_normal h (Or.inl rfl) earlier F hn,
    ⟨{ K1 := F.Li L 1, point_le := hl, contains := le_rfl,
       component := hc, normal := hn, alternatives := Or.inl rfl,
       other_components := ?_ }⟩⟩
  intro i hi
  rcases hi with ⟨he,_,_⟩ | ⟨_,rfl⟩
  · omega
  · exact h3

/-- The rank-one model comparison discharges both component and abelian-span
obligations in the actual degree-four consumer. -/
theorem four_abelian_componentGeometry_of_non_enlarging_model
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn F.H) (hLD : F.Li L 1 ≤ D)
    (hN : (D.subgroupOf F.H).Normal)
    (hm : ClassificationModels.IsBenderModel (D ⧸ pCore 2 D) ∨
      ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 3 2 ∨
      (∃ p e : ℕ, p.Prime ∧ Odd p ∧ (e = 1 ∨ e = 2) ∧
        ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 (p ^ e)) ∨
      (∃ n : ℕ, 0 < n ∧ Chapter1.Section02.LocalModels.IsSU (D ⧸ pCore 2 D) 3 (2 ^ n))) :
    IsMulCommutative F.U ∧ Nonempty (ComponentGeometry F L) := by
  have he := four_point_component_eq_of_non_enlarging_model h earlier F hD hLD hm
  exact four_abelian_componentGeometry_of_point_normal h earlier F (he.symm ▸ hN)

/-- The complete even rank-two comparison supplies the unchanged component
geometry and abelianity assertions in degree four. -/
theorem four_abelian_componentGeometry_of_even_rank_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn F.H) (hLD : F.Li L 1 ≤ D)
    (hN : (D.subgroupOf F.H).Normal)
    (hm : Chapter1.Section02.LocalModels.RankTwoTheoremC (D ⧸ pCore 2 D)) :
    IsMulCommutative F.U ∧ Nonempty (ComponentGeometry F L) := by
  have he := four_point_component_eq_of_even_rank_two h earlier F hD hLD hm
  exact four_abelian_componentGeometry_of_point_normal h earlier F (he.symm ▸ hN)

/-- Both even classical cover signs feed the original component and
abelian-span consumer through the proved residual equality. -/
theorem four_abelian_componentGeometry_of_even_classical_cover
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn F.H) (hLD : F.Li L 1 ≤ D)
    (hN : (D.subgroupOf F.H).Normal)
    {m : ℕ} (hm : 0 < m) (unitary : Bool)
    (hmodel : Chapter1.Section02.LocalModels.IsSLSign (D ⧸ pCore 2 D) unitary 3 (2 ^ m)) :
    IsMulCommutative F.U ∧ Nonempty (ComponentGeometry F L) := by
  have he := four_point_component_eq_of_even_classical_cover h earlier F hD hLD hm unitary hmodel
  exact four_abelian_componentGeometry_of_point_normal h earlier F (he.symm ▸ hN)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
