module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.ThreeRadical
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Six
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import Theory.GroupTheory.CComponent.NormalOrbitRank
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality

/-!
# Excluding the three-space radical by its seven-rank

The actual three-space radical X has noncyclic seven-quotient and hence
seven-rank at least two. The previously constructed detected component
orbit contains X inside G₁. Pass through the literal G₁/O₂(G₁): the original
point residual image has positive seven-rank and center of order prime
to seven. A different detected component would have its entire Sylow orbit
centralizing the normal point component, giving ambient seven-rank at
least three. The SQTK bound therefore identifies the detected component
with the point component, making the latter quasisimple of seven-rank two.

This contradicts every source point alternative. The equal, L₅(2), M₂₄
and J₄ rows have seven-rank one by their actual quotient orders. The
E₄₉-by-SL₂(7) row cannot be quasisimple: its normal seven-group would be
central, whereas the proved A.3.6 center has order one or three.

Consequently a refined point component proves K₃ = L₃ and its relative
normality. Together with the established four- and six-space cases this
constructs all four LocalComponents from that single point refinement.
PointCore.PointAlternative applies the construction to the actual original
point-core and fusion consumers. The point refinement, general normalizer
containments and quasisimple escape remain with qt-d-1251-local; the final
source assembly remains with qt-d-1251-source. No generation-one exclusion
is used in this three-space argument.

Source: Aschbacher--Smith, 12.5.3, printed pp.817--819, using A.3.6,
A.3.7 and the genuine component-orbit detection of 1.3.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The genuine noncyclic seven-quotient forces rank at least two in the original radical. -/
theorem three_radical_seven_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    2 ≤ primeRank 7 (Chapter1.XiP 7 K) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨hx,hq⟩ := s.three_radical_mem_Xi h hK hLK hN hn
  let P : Sylow 7 (Chapter1.XiP 7 K) := Classical.choice inferInstance
  by_contra hr
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  exact hq.not_isCyclic ((hx.sylowQuotientEquiv (by decide) hq P).isCyclic.mp hc)

/-- A strict three-space radical forces the original normal point component to have a quasisimple two-core quotient of seven-rank at least two. -/
theorem three_radical_forces_point_seven_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K C : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLC : s.marking.Li 1 ≤ C) (hNC : (C.subgroupOf (s.marking.Gi 1)).Normal) :
    IsQuasisimple (C ⧸ pCore 2 C) ∧ 2 ≤ primeRank 7 (C ⧸ pCore 2 C) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨Q,hQ,hqQ,hXQ,_⟩ := s.three_radical_point_component_orbit h hK hLK hN hn
  let H := s.marking.Gi 1
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (s.marking.Li 1).subgroupOf H
  let C₀ := C.subgroupOf H
  let Q₀ := Q.subgroupOf H
  let X := Chapter1.XiP 7 K
  let X₀ := X.subgroupOf H
  have hXH : X ≤ H := s.three_radical_le_point hK.1 hLK
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
  let b : B ≃* s.marking.Li 1 := subgroupOfEquivOfLe (s.marking.Li_le_Gi 1)
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  let bq : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans (s.marking.LiCoreEquiv 1 (.inl rfl))
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
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
    exact s.three_radical_seven_rank h hK hLK hN hn
  have hXorb : X₀.map q ≤ componentOrbit (Q₀.map q) (((T : Subgroup G).subgroupOf H).map q) := by
    have hh := map_mono (f := q) (comap_mono (f := H.subtype) hXQ)
    exact hh.trans_eq (Chapter1.XiEmbedding.quotientImage_componentOrbit_source
      H Q (T : Subgroup G) hQ.1 s.sylow_le_G₁)
  have hrH : primeRank 7 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 7 (by decide) _ pCore_isPGroup).trans
      ((h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))).stronglyQuasithin
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
    s.sylow_le_G₁.trans ((normal_subgroupOf_iff_le_normalizer hC.1).mp hNC)
  have hXC : X ≤ C := hXQ.trans (iSup_conjugates_le_of_le_normalizer C (T : Subgroup G) C le_rfl hTC)
  refine ⟨hqQ,?_⟩
  rw [primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 C) pCore_isPGroup]
  exact (s.three_radical_seven_rank h hK hLK hN hn).trans (primeRank_mono 7 hXC)

private theorem point_component_center_seven_free
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    [IsQuasisimple (C ⧸ pCore 2 C)] :
    ¬ 7 ∣ Nat.card (center (C ⧸ pCore 2 C)) := by
  let H := s.marking.Gi 1
  let C₀ := C.subgroupOf H
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  let a := subgroupOfEquivOfLe hC.1
  let e : (C ⧸ pCore 2 C) ≃* C₀.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hC.2)
  let : IsQuasisimple (C₀.map q) := IsQuasisimple.of_mulEquiv e
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))) (pCore 2 H) pCore_isPGroup
  rw [Nat.card_congr (centerCongr e).toEquiv]
  rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
      hQ (pCore_quotient_pCore_eq_bot 2) (hC.2.map_quotient _) with ⟨hs,_⟩ | ⟨⟨z⟩,_⟩
  · let := hs
    have hz : center (C₀.map q) = ⊥ := by
      rcases (inferInstance : (center (C₀.map q)).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exact ((hC.2.map_quotient _).not_isSolvable
          (Group.isSolvable_of_comm (fun x y =>
            (mem_center_iff.mp (hz ▸ mem_top x) y).symm))).elim
    rw [hz,Subgroup.card_bot]
    decide
  · rw [Nat.card_congr z.toEquiv]
    norm_num

/-- The literal E₄₉ extension in the point alternative is incompatible with a quasisimple two-core quotient. -/
theorem point_radical_alternative_not_quasisimple
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hm : Chapter1.Section02.LocalModels.HasExtension (C ⧸ pCore 2 C)
      (Chapter1.Section02.LocalModels.ElementaryModel 7 2)
      (fun X _ => Chapter1.Section02.LocalModels.IsSL X 2 7)) :
    ¬ IsQuasisimple (C ⧸ pCore 2 C) := by
  intro hq
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let := hq
  let A := C ⧸ pCore 2 C
  obtain ⟨N,hN,⟨e⟩,_⟩ := hm
  let := hN
  have hc : Nat.card N = 49 := by rw [Nat.card_congr e.toEquiv]; simp
  let : Group.IsNilpotent N := (IsPGroup.of_card (p := 7) (n := 2) hc).isNilpotent
  have hz : N ≤ center A := by
    rcases IsQuasisimple.normal_le_center_or_eq_top N with hz | ht
    · exact hz
    · let : Group.IsSolvable A := Group.isSolvable_of_surjective
        (f := N.subtype) (by rw [ht]; exact topEquiv.surjective)
      let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
      let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
      exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
  exact s.point_component_center_seven_free h hC
    ((show 7 ∣ Nat.card N by rw [hc]; decide).trans (card_dvd_of_le hz))

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
  · rw [Nat.card_congr hm.some.toEquiv,AtlasPort.Mathieu.M24_card]
    decide
  · rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card]
    decide

/-- Every quasisimple source point alternative has seven-rank at most one on its actual two-core quotient. -/
theorem point_component_seven_rank_of_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (ha : LocalComponentAlternative s 1 C)
    [IsQuasisimple (C ⧸ pCore 2 C)] : primeRank 7 (C ⧸ pCore 2 C) ≤ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  cases ha with
  | equal he =>
    subst C
    apply primeRank_le_of_prime_pow_not_dvd
    rw [Nat.card_congr (s.marking.LiCoreEquiv 1 (.inl rfl)).toEquiv]
    change ¬ 7 ^ (1+1) ∣ Nat.card SL(3,ZMod 2)
    rw [Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  | large _ hm _ => exact large_point_seven_rank hm
  | radical _ _ hm => exact (s.point_radical_alternative_not_quasisimple h hC hm inferInstance).elim

/-- The source point alternatives exclude the radical enlargement at the original three-space. -/
theorem local_three_component_eq_of_point_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K C : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 3))
    (hLK : s.marking.Li 3 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 3)).Normal)
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLC : s.marking.Li 1 ≤ C) (hNC : (C.subgroupOf (s.marking.Gi 1)).Normal)
    (ha : LocalComponentAlternative s 1 C) : s.marking.Li 3 = K := by
  have hq : IsQuasisimple (K ⧸ pCore 2 K) := by
    by_contra hn
    obtain ⟨hqC,hrC⟩ := s.three_radical_forces_point_seven_rank h hK hLK hN hn hC hLC hNC
    let := hqC
    have hb := s.point_component_seven_rank_of_alternative h hC ha
    omega
  let := hq
  exact s.local_component_eq_of_quasisimple 3 (.inl rfl) hK hLK

/-- The component and relative-normality clauses at index three, from the refined point component alone. -/
theorem local_three_component_source_of_point_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLC : s.marking.Li 1 ≤ C) (hNC : (C.subgroupOf (s.marking.Gi 1)).Normal)
    (ha : LocalComponentAlternative s 1 C) :
    s.marking.Li 3 ∈ Chapter1.cComponentsIn (s.marking.Gi 3) ∧
      ((s.marking.Li 3).subgroupOf (s.marking.Gi 3)).Normal := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 3 (.inr (.inl rfl))
  exact (s.local_three_component_eq_of_point_alternative h hK hLK hN hC hLC hNC ha).symm ▸ ⟨hK,hN⟩

/-- Assemble all four original components from a refined point component;
the other three indices are proved, including exclusion of the three-space radical. -/
@[expose] def localComponentsOfPointAlternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (C : Subgroup G)
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLC : s.marking.Li 1 ≤ C) (hNC : (C.subgroupOf (s.marking.Gi 1)).Normal)
    (ha : LocalComponentAlternative s 1 C) : LocalComponents s where
  K i := if i = 1 then C else s.marking.Li i
  contains i hi := by
    split_ifs with he
    · subst i; exact hLC
    · exact le_rfl
  component i hi := by
    rcases hi with rfl | rfl | rfl | rfl
    · simpa using hC
    · simpa using (s.local_three_component_source_of_point_alternative h hC hLC hNC ha).1
    · simpa using (s.local_four_component_source h).1
    · simpa using (s.local_six_component_source h).1
  normal i hi := by
    rcases hi with rfl | rfl | rfl | rfl
    · simpa using hNC
    · simpa using (s.local_three_component_source_of_point_alternative h hC hLC hNC ha).2
    · simpa using (s.local_four_component_source h).2
    · simpa using (s.local_six_component_source h).2
  alternative i hi := by
    by_cases he : i = 1
    · subst i; simpa using ha
    · exact .equal (by simp only [he,ite_false])

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
