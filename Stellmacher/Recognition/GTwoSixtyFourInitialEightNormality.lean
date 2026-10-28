module

public import Stellmacher.Recognition.GTwoSixtyFourInitialEightGeometry
public import Stellmacher.SL2TwoTranspositionNormalizer

/-!
# An elementary eight normal in the initial vertex

The normal closure of the neighboring core is the entire initial vertex:
its image in the SL₂(2) quotient is normal and contains a transposition.
The case-(a) commutator is the initial center, which centralizes the initial
core. An elementary eight is self-centralizing inside that core, so this
commutator lies in the eight and proves normality.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

private theorem closure_le {K : Type*} [Group K] (C P N : Subgroup K)
    (hCN : C ≤ N) (hPN : P ≤ Subgroup.normalizer (N : Set K)) :
    conjugateClosure C P ≤ N := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨g, c, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hPN g.property) c).mp (hCN c.property)

private theorem closure_normalizer {K : Type*} [Group K] (C P : Subgroup K) :
    P ≤ Subgroup.normalizer (conjugateClosure C P : Set K) := by
  rw [conjugateClosure, Subgroup.le_normalizer_closure_iff]
  rintro g hg x ⟨h, c, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨⟨g * h, P.mul_mem hg h.property⟩, c, ?_⟩
  simp only [mul_inv_rev]
  group

private theorem sl2_normal_eq_top (M B : Subgroup SL2Two) [M.Normal]
    (hBM : B ≤ M) (hB : Nat.card B = 2) : M = ⊤ := by
  have h6 : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hd := M.card_subgroup_dvd_card
  rw [h6] at hd
  have htwo := Subgroup.card_dvd_of_le hBM
  rw [hB] at htwo
  have hpos := Nat.card_pos (α := M)
  have hbound : Nat.card M ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hcases : Nat.card M = 2 ∨ Nat.card M = 6 := by
    interval_cases h : Nat.card M <;> norm_num [h] at *
  rcases hcases with h | h
  · exact (sl2Two_normalizer_eq_of_card_two M h).symm.trans
      (Subgroup.normalizer_eq_top_iff.mpr inferInstance)
  · exact Subgroup.eq_top_of_card_eq M (h.trans h6.symm)

/-- The case-(a) normal closure is the whole initial vertex in the order-64 branch. -/
public theorem gTwo_card64_initial_closure_eq_vertex
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    data.L = GAt data.Γ data.criticalPath.a := by
  let := data.groupK
  let := data.finiteK
  let P := GAt data.Γ data.criticalPath.a
  let Q := QAt data.Γ data.criticalPath.a
  let B := QAt data.Γ data.criticalPath.firstStep
  let C := QAt data.Γ data.aPrev
  have hQdef : Q = twoCoreIn P := data.Γ.twoCoreAt_def _
  have hQP : Q ≤ P := hQdef ▸ twoCoreIn_le P
  have hPQ : P ≤ Subgroup.normalizer (Q : Set data.K) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp
    rw [hQdef]
    exact twoCoreIn_normal P
  obtain ⟨hQcard, _, hBcard, _, _⟩ := gTwo_card64_vertex_structure data hcard
  change Nat.card Q = 32 at hQcard
  change Nat.card B = 32 at hBcard
  have hBP : B ≤ P := by
    intro x hx
    have hxS := (gTwo_card64_cores_le_sylow data).2
      (Subgroup.mem_map_of_mem data.embedding hx)
    have hSP : (data.sylowIntersection : Subgroup G) ≤ P.map data.embedding := by
      rw [← data.intersection_eq]
      exact inf_le_left
    obtain ⟨y, hy, heq⟩ := hSP hxS
    exact data.embedding_injective heq ▸ hy
  obtain ⟨g, hg⟩ := (lemma_seven_one_graph data.Γ).local_transitivity
    data.criticalPath.a
    ((mem_neighborhood_iff_adjacent data.Γ).mpr data.criticalPath.firstStep_adj)
    data.caseA.previous_vertex.1
  have hCeq : C = B.map (MulAut.conj (g : data.K)⁻¹).toMonoidHom := by
    change CosetGraphContext.q data.Γ data.aPrev =
      (CosetGraphContext.q data.Γ data.criticalPath.firstStep).map _
    rw [← hg, q_act]
  have hCP : C ≤ P := by
    rw [hCeq]
    rintro x ⟨y, hy, rfl⟩
    exact P.mul_mem (P.mul_mem (P.inv_mem g.property) (hBP hy))
      (P.inv_mem (P.inv_mem g.property))
  have hCcard : Nat.card C = 32 := by
    rw [hCeq, Subgroup.card_map_of_injective (MulAut.conj (g : data.K)⁻¹).injective]
    exact hBcard
  have hCQ : ¬ C ≤ Q := by
    intro hCQ
    have hBQ : B ≤ Q := by
      intro b hb
      have hc : (g : data.K)⁻¹ * b * ((g : data.K)⁻¹)⁻¹ ∈ C := by
        rw [hCeq]
        exact Subgroup.mem_map_of_mem _ hb
      exact (Subgroup.mem_normalizer_iff.mp (hPQ (P.inv_mem g.property)) b).mpr (hCQ hc)
    have hCe : C = Q := Subgroup.eq_of_le_of_card_ge hCQ (by omega)
    have hBe : B = Q := Subgroup.eq_of_le_of_card_ge hBQ (by omega)
    have hD : data.D = Q := by
      rw [data.caseA.definitions.1]
      change C ⊓ B = Q
      rw [hCe, hBe, inf_idem]
    have hDc := gTwo_card64_elementary_intersection_card data hcard
    rw [hD] at hDc
    omega
  have hLdef : data.L = conjugateClosure C P := data.caseA.definitions.2.1
  have hLP : data.L ≤ P := by
    rw [hLdef]
    exact closure_le C P P hCP P.le_normalizer
  have hPL : P ≤ Subgroup.normalizer (data.L : Set data.K) := by
    rw [hLdef]
    exact closure_normalizer C P
  have hCL : C ≤ data.L := by
    rw [hLdef]
    intro c hc
    exact Subgroup.subset_closure ⟨1, ⟨c, hc⟩, by simp⟩
  have hQL : Q ≤ data.L := by
    change QAt data.Γ data.criticalPath.a ≤ data.L
    rw [← data.caseA.Q_eq, data.caseA.definitions.2.2.1]
    exact twoCoreIn_le _
  obtain ⟨f, hf, hker⟩ := data.caseA.local_quotients data.criticalPath.a
  let M := (data.L.subgroupOf P).map f
  let Cbar := (C.subgroupOf P).map f
  let : (data.L.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLP).mpr hPL
  let : M.Normal := Subgroup.Normal.map inferInstance f hf
  have hCbarCard : Nat.card Cbar = 2 := by
    have hd6 := Cbar.card_subgroup_dvd_card
    have h6 : Nat.card SL2Two = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
    rw [h6] at hd6
    have hd32 := (C.subgroupOf P).card_map_dvd f
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv, hCcard] at hd32
    have hd2 : Nat.card Cbar ∣ 2 := by
      simpa using Nat.dvd_gcd hd6 hd32
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hone | htwo
    · have hbot := Subgroup.card_eq_one.mp hone
      have hle : C.subgroupOf P ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp hbot
      rw [hker] at hle
      exact (hCQ (fun c hc => hle (show (⟨c, hCP hc⟩ : P) ∈ C.subgroupOf P from hc))).elim
    · exact htwo
  have hM : M = ⊤ := sl2_normal_eq_top M Cbar
    (Subgroup.map_mono (Subgroup.subgroupOf_mono P hCL)) hCbarCard
  apply le_antisymm hLP
  intro p hp
  have hm : f ⟨p, hp⟩ ∈ M := by rw [hM]; trivial
  obtain ⟨l, hl, heq⟩ := hm
  have hk : l⁻¹ * (⟨p, hp⟩ : P) ∈ f.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
  rw [hker] at hk
  have hmem := data.L.mul_mem hl (hQL hk)
  change (l : data.K) * ((l : data.K)⁻¹ * p) ∈ data.L at hmem
  simpa only [mul_inv_cancel_left] using hmem

private theorem initial_center_centralizes_core
    {K : Type*} [Group K] [Finite K] {S P1 P2 : Subgroup K}
    (Γ : CosetGraphContext K S P1 P2) (a : Γ.Vertex) :
    ZAt Γ a ≤ Subgroup.centralizer (QAt Γ a : Set K) := by
  change Γ.zAt a ≤ _
  rw [Γ.zAt_def]
  apply sSup_le
  rintro Z ⟨T, rfl⟩
  let W := (T : Subgroup (Γ.vertexStabilizer a)).map (Γ.vertexStabilizer a).subtype
  have hQW : QAt Γ a ≤ W := by
    change Γ.twoCoreAt a ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal T)
  exact (omegaOneCenter_le_centerAmbient W).trans
    ((centerAmbient_le_centralizer W).trans (Subgroup.centralizer_le hQW))

private theorem intersection_self_centralizing
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    QAt data.Γ data.criticalPath.a ⊓ Subgroup.centralizer (data.D : Set data.K) = data.D := by
  let := data.groupK
  let := data.finiteK
  let : IsElementaryAbelian 2 data.D := data.caseA.base.2.2
  let S := (data.sylowIntersection : Subgroup G)
  let D := data.D.map data.embedding
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map data.embedding
  have hDcore := gTwo_card64_elementary_intersection_le_core data hcard
  have hDS : D ≤ S := (Subgroup.map_mono hDcore).trans
    (gTwo_card64_cores_le_sylow data).1
  let Dn := D.subgroupOf S
  let : IsElementaryAbelian 2 Dn := IsElementaryAbelian.subgroupOf hDS
  obtain ⟨e, _, heQa, _⟩ := gTwo_card64_marked_equiv data hcard
  let Dm := Dn.map e.toMonoidHom
  let : IsElementaryAbelian 2 Dm := IsElementaryAbelian.map e.toMonoidHom
  have hDmCard : Nat.card Dm = 8 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDS).toEquiv,
      Subgroup.card_map_of_injective data.embedding_injective]
    exact gTwo_card64_elementary_intersection_card data hcard
  have hDmCore : Dm ≤ C4SquareSignSwap.inverterCore := by
    rw [← heQa]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono S (Subgroup.map_mono hDcore))
  have hself := C4SquareSignSwap.elementary_eight_centralizer_inverterCore Dm hDmCard hDmCore
  apply le_antisymm ?_ (le_inf hDcore
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance))
  intro c hc
  have hcS : data.embedding c ∈ S := (gTwo_card64_cores_le_sylow data).1
    (Subgroup.mem_map_of_mem data.embedding hc.1)
  let cS : S := ⟨data.embedding c, hcS⟩
  have heCore : e cS ∈ C4SquareSignSwap.inverterCore := by
    rw [← heQa]
    exact Subgroup.mem_map_of_mem e.toMonoidHom
      (show cS ∈ ((QAt data.Γ data.criticalPath.a).map data.embedding).subgroupOf S from
        Subgroup.mem_map_of_mem data.embedding hc.1)
  have heC : e cS ∈ Subgroup.centralizer (Dm : Set C4SquareSignSwap.Model) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨d, hd, rfl⟩
    change e d * e cS = e cS * e d
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨d0, hd0, heq⟩ := hd
    change (d : G) * data.embedding c = data.embedding c * (d : G)
    change data.embedding d0 = (d : G) at heq
    rw [← heq, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_iff.mp hc.2 d0 hd0]
  have heD : e cS ∈ Dm := by rw [← hself]; exact ⟨heCore, heC⟩
  obtain ⟨d, hd, heq⟩ := heD
  have hdc : d = cS := e.injective heq
  have hcD : data.embedding c ∈ D := by
    have hval := congrArg Subtype.val hdc
    change (d : G) = data.embedding c at hval
    change (d : G) ∈ D at hd
    exact hval ▸ hd
  obtain ⟨d0, hd0, heq⟩ := hcD
  exact data.embedding_injective heq ▸ hd0

/-- The actual neighboring-core intersection is normalized by the initial vertex. -/
public theorem gTwo_card64_elementary_intersection_normalizer
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    (GAt data.Γ data.criticalPath.a).map data.embedding ≤
      Subgroup.normalizer (data.D.map data.embedding : Set G) := by
  let := data.groupK
  let := data.finiteK
  let P := GAt data.Γ data.criticalPath.a
  let Q := QAt data.Γ data.criticalPath.a
  have hDQ : data.D ≤ Q := gTwo_card64_elementary_intersection_le_core data hcard
  have hQdef : Q = twoCoreIn P := data.Γ.twoCoreAt_def _
  have hQP : Q ≤ P := hQdef ▸ twoCoreIn_le P
  have hPQ : P ≤ Subgroup.normalizer (Q : Set data.K) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp
    rw [hQdef]
    exact twoCoreIn_normal P
  have hcomm : ⁅data.D, P⁆ = ZAt data.Γ data.criticalPath.a := by
    change ⁅data.D, GAt data.Γ data.criticalPath.a⁆ = _
    rw [← gTwo_card64_initial_closure_eq_vertex data hcard]
    exact data.caseA.base.1
  have hZQ : ZAt data.Γ data.criticalPath.a ≤ Q := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono hDQ le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hPQ)
  have hZD : ZAt data.Γ data.criticalPath.a ≤ data.D := by
    rw [← intersection_self_centralizing data hcard]
    exact le_inf hZQ ((initial_center_centralizes_core data.Γ data.criticalPath.a).trans
      (Subgroup.centralizer_le hDQ))
  have hPD : P ≤ Subgroup.normalizer (data.D : Set data.K) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hcomm ▸ hZD)
  exact (Subgroup.map_mono hPD).trans (Subgroup.le_normalizer_map data.embedding)

/-- There is an elementary eight in the initial core normal in the initial vertex. -/
public theorem gTwo_card64_initial_eight_exists
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    ∃ U : Subgroup G, IsElementaryAbelian 2 U ∧ Nat.card U = 8 ∧
      U ≤ (QAt data.Γ data.criticalPath.a).map data.embedding ∧
      (GAt data.Γ data.criticalPath.a).map data.embedding ≤ Subgroup.normalizer (U : Set G) := by
  let := data.groupK
  let := data.finiteK
  let : IsElementaryAbelian 2 data.D := data.caseA.base.2.2
  refine ⟨data.D.map data.embedding, IsElementaryAbelian.map data.embedding, ?_,
    Subgroup.map_mono (gTwo_card64_elementary_intersection_le_core data hcard),
    gTwo_card64_elementary_intersection_normalizer data hcard⟩
  rw [Subgroup.card_map_of_injective data.embedding_injective]
  exact gTwo_card64_elementary_intersection_card data hcard

end Stellmacher.Recognition
