module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalCarrierExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.OrdinaryComplete
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.ExceptionalSmall
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held
public import CFSG.Quasithin.ChapterC.Section01.BlockCentralQuotient
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Order

/-!
# The two ordinary carriers of a remaining natural local escape

Every escaping natural local member K has parameter two at the original
prime three and lies properly in the original selected component L. The
constrained-carrier exclusion makes L ordinary. Restrict K and its full
normalizing Sylow to L, then apply the independently proved ordinary source
catalogue at this same pre-exclusion marker.

The natural plane survives a central two-group quotient with its actual
action and order sixteen. Its full commutator layer can have a central
attachment; only the justified lower bound on the image layer is used.
This normalized elementary subgroup excludes M11, M12 and J2 by their
native Sylow bounds. The literal local A5 section excludes the binary
linear rows, M24 and Held. The Tits two-local order bound and the actual
orders of binary G2 and triality exclude the binary rank-two row.

Consequently the selected carrier has central quotient M22 or M23. The
original-marker application retains the cubic prime, natural degree two,
moving plane of order four, proper inclusion, normality and maximality of
that same carrier. Neither remaining embedding is excluded here; these
conclusions do not make K an ambient C-component or make its Borel
M_Z-invariant. Original 15.1.14 and the whole-core A6 reconstruction retain
their earlier producers and final assembly owners.

Source: Aschbacher--Smith 15.1.20(2), 15.1.22, printed pp.1094--1100,
and A.3.12, printed pp.47--48, for the local-section model exclusions.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem natural_image_layer
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (q : A →* H) (hp : IsPGroup 2 q.ker) (hz : q.ker ≤ center A)
    (P : Sylow 2 A) (hq : Function.Surjective q)
    (B : Subgroup A) (hb : IsL2EvenBlock B 2)
    (hn : (P : Subgroup A) ≤ normalizer (B : Set A)) :
    let D := B.map q
    IsElementaryAbelian 2 (blockU D) ∧ 16 ≤ Nat.card (blockU D) ∧
      pCore 2 D ≠ ⊥ ∧
      ((P.mapSurjective hq : Sylow 2 H) : Subgroup H) ≤
        normalizer ((blockU D).map D.subtype : Set H) := by
  intro D
  let f := q.subgroupMap B
  have hf : Function.Surjective f := q.subgroupMap_surjective B
  have hfp : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hp.comap_subtype
  have hfc : f.ker ≤ center B := by
    intro b hb
    have hzb : (b : A) ∈ center A := hz (congrArg Subtype.val (MonoidHom.mem_ker.mp hb))
    exact mem_center_iff.mpr (fun a => Subtype.ext (mem_center_iff.mp hzb a))
  have hU : (blockU B).map f = blockU D := by
    have hc : (pCore 2 B).map f = pCore 2 D := by
      rw [← f.comap_pCore_of_ker_isPGroup hf hfp,map_comap_eq_self_of_surjective hf]
    rw [blockU,map_commutator,hc,map_top_of_surjective _ hf]
    rfl
  have hE : IsElementaryAbelian 2 (blockU D) := by
    let := hb.2.1.elementary
    rw [←hU]
    exact IsElementaryAbelian.map f
  have hm : Nat.card (BlockModule D) = 16 := by
    obtain ⟨F,hF,hfin,hcard,_,ρ,⟨m⟩,hρ⟩ := hb.2.2
    obtain ⟨m'⟩ := m.exists_of_central_two_quotient f hf hb.2.1.twoPerfect hfp hfc ρ
    rw [Nat.card_congr m'.moduleIso.toEquiv]
    change Nat.card (Fin 2 → F) = 16
    rw [Nat.card_fun,Nat.card_fin,hcard]
    norm_num
  have hsize : 16 ≤ Nat.card (blockU D) := by
    rw [←hm]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (blockFixed D))
      (QuotientGroup.mk'_surjective _)
  refine ⟨hE,hsize,?_,?_⟩
  · intro hc
    have hu : blockU D = ⊥ := bot_unique (blockU_le_core.trans hc.le)
    rw [hu,card_bot] at hsize
    omega
  · exact ((map_mono hn).trans (B.le_normalizer_map q)).trans
      (normalizer_le_normalizer_characteristic_image D (blockU D))

private theorem natural_small_rank_excluded
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (q : A →* H) (hp : IsPGroup 2 q.ker) (hz : q.ker ≤ center A)
    (P : Sylow 2 A) (hq : Function.Surjective q)
    (B : Subgroup A) (hb : IsL2EvenBlock B 2)
    (hn : (P : Subgroup A) ≤ normalizer (B : Set A))
    (he : Nonempty (H ≃* Sporadic.Mathieu.M11) ∨
      Nonempty (H ≃* Sporadic.Mathieu.M12) ∨
      Nonempty (H ≃* Sporadic.LeechRelated.J2.Carrier)) : False := by
  let D := B.map q
  let E := (blockU D).map D.subtype
  obtain ⟨hE,hsize,_,hPE⟩ := natural_image_layer q hp hz P hq B hb hn
  let := hE
  have hE' : IsElementaryAbelian 2 E := IsElementaryAbelian.map D.subtype
  have hc : 16 ≤ Nat.card E := by
    rwa [card_map_of_injective D.subtype_injective]
  rcases he with he | he | he <;> obtain ⟨e⟩ := he
  · exact FiveLocalFF.SporadicSieve.not_mathieuEleven (P.mapSurjective hq) E hE' hPE hc e
  · exact FiveLocalFF.SporadicSieve.not_mathieuTwelve E hE' hc e
  · exact FiveLocalFF.SporadicSieve.not_jankoTwo (P.mapSurjective hq) E hE' hPE hc e

private theorem natural_m24_held_excluded
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (q : A →* H) (hp : IsPGroup 2 q.ker) (hz : q.ker ≤ center A)
    (P : Sylow 2 A) (hq : Function.Surjective q)
    (B : Subgroup A) (hb : IsL2EvenBlock B 2)
    (hl : B ∈ localCComponents P)
    (hn : (P : Subgroup A) ≤ normalizer (B : Set A))
    (he : Nonempty (H ≃* Sporadic.Mathieu.M24) ∨ Nonempty (H ≃* _root_.Held.He)) : False := by
  let : Group.IsNilpotent q.ker := hp.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hn' := (map_mono hn).trans (B.le_normalizer_map q)
  have hc := (natural_image_layer q hp hz P hq B hb hn).2.2.1
  obtain ⟨eB⟩ := FiveLocalFF.SolvableQuotients.section_map q B hl hb.four_quotient_alternatingFive.some
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · exact FiveLocalFF.MathieuTwentyFour.not_section e (P.mapSurjective hq) (B.map q) hl' hn' hc eB
  · exact FiveLocalFF.Held.not_section e (P.mapSurjective hq) (B.map q) hl' hn' hc eB

private theorem natural_binary_rank_two_excluded
    {A : Type*} [Group A] [Finite A]
    (B : Subgroup A) (hb : IsL2EvenBlock B 2)
    (hm : OrdinaryBinaryRankTwo A) : False := by
  have hd := (FiveLocalFF.SolvableQuotients.five_dvd_card B
    hb.four_quotient_alternatingFive.some).trans B.card_subgroup_dvd_card
  rcases hm with he | he | he <;> obtain ⟨e⟩ := he
  · rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  · have hc : pCore 2 B ≠ ⊥ := by
      intro he
      have hu := hb.2.1.blockU_ne_bot
      exact hu (bot_unique (blockU_le_core.trans he.le))
    exact FiveLocalFF.ExceptionalSmall.not_tits B hc hb.four_quotient_alternatingFive.some e
  · rw [Nat.card_congr e.toEquiv,
      Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.card_binaryCarrier] at hd
    norm_num at hd

/-- The complete ordinary catalogue leaves only M₂₂ and M₂₃ central-quotient
carriers for an escaping natural local member. All other rows are excluded
using the original full Sylow and actual A₅ section, including central covers. -/
theorem PreExclusionSource.localFamily_linearTwo_carrier_mathieu
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    ∃ name : ClassificationModels.SporadicName, (name = .m22 ∨ name = .m23) ∧
      Nonempty ((d.L ⧸ center d.L) ≃* name.Carrier) := by
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  obtain ⟨_,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  obtain ⟨hKL,_,_,_,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)
  let B := K.subgroupOf d.L
  let e : B ≃* K := subgroupOfEquivOfLe hKL.le
  have hB : IsL2EvenBlock B 2 := (hn ▸ hb : IsL2EvenBlock K 2).of_mulEquiv e.symm
  obtain ⟨P,hP⟩ := s.component_sylow
  have hPS : (P : Subgroup d.L) = d.S.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
    rfl
  have hl : B ∈ localCComponents P := by
    rw [hPS]
    exact local_restrict hK.2.1 hKL.le
  have hSN := s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hPB : (P : Subgroup d.L) ≤ normalizer (B : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro l hl k hk
    have hlS : l.val ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hl).1
    exact le_normalizer_iff.mp hSN l hlS k hk
  have rows := s.source_ordinary22 (h := h) hG hempty hM hJ hu hne hmany hres hL hp
  cases rows with
  | binaryRankTwo model _ _ _ _ _ _ _ =>
    exact (natural_binary_rank_two_excluded B hB model).elim
  | mathieuEleven model _ _ =>
    have hp : IsPGroup 2 (MonoidHom.id d.L).ker :=
      IsPGroup.ker_isPGroup_of_injective Function.injective_id
    exact (natural_small_rank_excluded (MonoidHom.id d.L) hp (by simp) P
      Function.surjective_id B hB hPB (.inl model)).elim
  | linear n hn e _ _ _ _ _ =>
    exact (FiveLocalFF.BinaryLinear.not_section_binary_linear P B hl
      hB.four_quotient_alternatingFive.some hn
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩).elim
  | sporadic name allowed model _ _ =>
    let q := QuotientGroup.mk' (center d.L)
    have hp : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact (d.ordinary_center hL s.odd_core).2
    have hz : q.ker ≤ center d.L := by rw [QuotientGroup.ker_mk']
    rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (natural_small_rank_excluded q hp hz P (QuotientGroup.mk'_surjective _)
        B hB hPB (.inr (.inl model))).elim
    · exact ⟨.m22,.inl rfl,model⟩
    · exact ⟨.m23,.inr rfl,model⟩
    · exact (natural_m24_held_excluded q hp hz P (QuotientGroup.mk'_surjective _)
        B hB hl hPB (.inl model)).elim
    · exact (natural_small_rank_excluded q hp hz P (QuotientGroup.mk'_surjective _)
        B hB hPB (.inr (.inr model))).elim
    · exact (natural_m24_held_excluded q hp hz P (QuotientGroup.mk'_surjective _)
        B hB hl hPB (.inr model)).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Any natural escape in the original marked family has a normal M₂₂ or M₂₃
central-quotient carrier. The original cubic, field-four degree and moving
plane of order four are retained; this does not identify K with that carrier. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_mathieu_carrier
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 ∧ K < d.L ∧
            d.L ∈ Chapter1.LStarIn d.G1 d.S ∧
            (d.L.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (d.L : Set G) ∧
            IsComponent d.G1 (d.L.subgroupOf d.G1) ∧
            ∃ name : ClassificationModels.SporadicName, (name = .m22 ∨ name = .m23) ∧
              Nonempty ((d.L ⧸ center d.L) ≃* name.Carrier) := by
  obtain ⟨d,hZ,hr,s,hfamily,_⟩ := h.source_preExclusion_local_carrier_rows
    hG T hempty hM hmany hJ hu hne hfull m hp hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,hGn,hordinary⟩ := hfamily K hK hq hout n hb
  exact ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,hGn,hordinary,
    s.localFamily_linearTwo_carrier_mathieu (h := h) hp hG hempty hM hJ hu hne hmany
      hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
