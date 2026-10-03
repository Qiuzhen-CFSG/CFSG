module

public import Stellmacher.Recognition.GTwoSixtyFourIndexTwo
public import Stellmacher.SectionNine.CubicLocalAction
public import Theory.SpecificGroups.C4SquareSignSwapPresentation
public import Theory.SpecificGroups.C4SquareSignSwapRecognition

/-!
# Marked presentations for the order-64 G₂ Sylow

The two embedded vertex cores lie in the distinguished Sylow intersection.
When its order is 64, each core is normal of index two. A sign-and-swap
presentation of this Sylow, marking the canonical transfer subgroup and the
two cores by their generators, yields the required simultaneous equivalence.

The elementary intersection D supplies an involutive inverter in both cores.
Its two defining cores have index six in the first vertex, giving |D| > 4.
The vertex acts transitively on three neighbors with a two-group point
stabilizer. Since D fixes two neighbors, it lies in the action kernel and
hence in the first core. An element of D outside the C₄ × C₄ base therefore
inverts that base and has square one.

Containment uses normal two-subgroups of the vertices. The quaternion central
product and this involutive inverter give compatible base generators and a
commuting swap involution by `C4SquareSignSwapRecognition`. Their explicit
presentation identifies all three marked subgroups simultaneously.
No involutivity assumption on the originally supplied inverter is used.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

private theorem vertex_core_le_sylow
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    letI := data.groupK
    letI := data.finiteK
    ∀ d : data.Γ.Vertex,
      (data.sylowIntersection : Subgroup G) ≤ (GAt data.Γ d).map data.embedding →
      (QAt data.Γ d).map data.embedding ≤ (data.sylowIntersection : Subgroup G) := by
  let := data.groupK
  let := data.finiteK
  intro d hSP
  let P := GAt data.Γ d
  let N := QAt data.Γ d
  have hN : N = twoCoreIn P := data.Γ.twoCoreAt_def d
  have hNP : N ≤ P := by rw [hN]; exact twoCoreIn_le _
  have hNN : (N.subgroupOf P).Normal := by rw [hN]; exact twoCoreIn_normal _
  have hNtwo : IsPGroup 2 N := by rw [hN]; exact pCore_isPGroup.map P.subtype
  have hmP : N.map data.embedding ≤ P.map data.embedding := Subgroup.map_mono hNP
  have hPN : P.map data.embedding ≤ Subgroup.normalizer (N.map data.embedding : Set G) :=
    (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNN)).trans
      (Subgroup.le_normalizer_map data.embedding)
  have hmN : ((N.map data.embedding).subgroupOf (P.map data.embedding)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hmP).mpr hPN
  let := hmN
  have hmTwo : IsPGroup 2 ((N.map data.embedding).subgroupOf (P.map data.embedding)) :=
    (hNtwo.map data.embedding).of_equiv (Subgroup.subgroupOfEquivOfLe hmP).symm
  have hle := hmTwo.le_sylow_of_normal (data.sylowIntersection.subtype hSP)
  intro x hx
  exact hle (show (⟨x, hmP hx⟩ : P.map data.embedding) ∈
    (N.map data.embedding).subgroupOf (P.map data.embedding) from hx)

/-- Both distinguished embedded vertex cores lie in the actual Sylow. -/
public theorem gTwo_card64_cores_le_sylow
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    letI := data.groupK
    letI := data.finiteK
    (QAt data.Γ data.criticalPath.a).map data.embedding ≤
        (data.sylowIntersection : Subgroup G) ∧
      (QAt data.Γ data.criticalPath.firstStep).map data.embedding ≤
        (data.sylowIntersection : Subgroup G) := by
  let := data.groupK
  let := data.finiteK
  constructor
  · exact vertex_core_le_sylow data _ (by rw [← data.intersection_eq]; exact inf_le_left)
  · exact vertex_core_le_sylow data _ (by rw [← data.intersection_eq]; exact inf_le_right)

/-- The two actual cores, viewed in the order-64 Sylow, are normal of index two. -/
public theorem gTwo_card64_cores_index_two
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let S := (data.sylowIntersection : Subgroup G)
    let Qa := ((QAt data.Γ data.criticalPath.a).map data.embedding).subgroupOf S
    let Qb := ((QAt data.Γ data.criticalPath.firstStep).map data.embedding).subgroupOf S
    Qa.Normal ∧ Qa.index = 2 ∧ Qb.Normal ∧ Qb.index = 2 := by
  let := data.groupK
  let := data.finiteK
  dsimp only
  obtain ⟨hQaS, hQbS⟩ := gTwo_card64_cores_le_sylow data
  obtain ⟨hQa, _, hQb, _⟩ := gTwo_card64_vertex_structure data hcard
  have index_two (Q : Subgroup data.K) (hQS : Q.map data.embedding ≤
      (data.sylowIntersection : Subgroup G)) (hQ : Nat.card Q = 32) :
      ((Q.map data.embedding).subgroupOf (data.sylowIntersection : Subgroup G)).index = 2 := by
    have hc := ((Q.map data.embedding).subgroupOf
      (data.sylowIntersection : Subgroup G)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv,
      Subgroup.card_map_of_injective data.embedding_injective, hQ, hcard] at hc
    omega
  have ha := index_two _ hQaS hQa
  have hb := index_two _ hQbS hQb
  exact ⟨Subgroup.normal_of_index_eq_two ha, ha, Subgroup.normal_of_index_eq_two hb, hb⟩

/-- The elementary intersection of the two neighboring cores has more than
four elements: both cores have index six in the order-192 first vertex. -/
public theorem gTwo_card64_elementary_intersection_card_gt_four
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) : 4 < Nat.card data.D := by
  let := data.groupK
  let := data.finiteK
  let P := GAt data.Γ data.criticalPath.a
  let B := QAt data.Γ data.criticalPath.firstStep
  let C := QAt data.Γ data.aPrev
  obtain ⟨_, hPcard, hBcard, _, _⟩ := gTwo_card64_vertex_structure data hcard
  have hSP : (data.sylowIntersection : Subgroup G) ≤ P.map data.embedding := by
    rw [← data.intersection_eq]
    exact inf_le_left
  have hBP : B ≤ P := by
    intro x hx
    have hxS := (gTwo_card64_cores_le_sylow data).2
      (Subgroup.mem_map_of_mem data.embedding hx)
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
    change (g : data.K)⁻¹ * y * ((g : data.K)⁻¹)⁻¹ ∈ P
    exact P.mul_mem (P.mul_mem (P.inv_mem g.property) (hBP hy))
      (P.inv_mem (P.inv_mem g.property))
  have hCcard : Nat.card C = 32 := by
    rw [hCeq, Subgroup.card_map_of_injective (MulAut.conj (g : data.K)⁻¹).injective]
    exact hBcard
  have hcount (H : Subgroup data.K) (hHP : H ≤ P) :
      Nat.card H * H.relIndex P = Nat.card P := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup data.K) H P bot_le hHP
  have hBi : B.relIndex P = 6 := by
    have h := hcount B hBP
    change Nat.card B = 32 at hBcard
    change Nat.card P = 192 at hPcard
    rw [hBcard, hPcard] at h
    omega
  have hCi : C.relIndex P = 6 := by
    have h := hcount C hCP
    change Nat.card P = 192 at hPcard
    rw [hCcard, hPcard] at h
    omega
  have hDeq : data.D = C ⊓ B := data.caseA.definitions.1
  have hDi : data.D.relIndex P ≤ 36 := by
    rw [hDeq]
    have h := Subgroup.relIndex_inf_le (H := C) (K := B) (L := P)
    simpa only [hBi, hCi] using h
  have hDcount := hcount data.D (hDeq ▸ inf_le_left.trans hCP)
  change Nat.card P = 192 at hPcard
  rw [hPcard] at hDcount
  nlinarith

private theorem perm_three_eq_one_of_two_fixed
    {X : Type*} [Finite X] (hcard : Nat.card X = 3) (f : Equiv.Perm X)
    {a b : X} (hab : a ≠ b) (ha : f a = a) (hb : f b = b) : f = 1 := by
  classical
  let := Fintype.ofFinite X
  ext x
  change f x = x
  by_cases hxa : x = a
  · simpa only [hxa] using ha
  by_cases hxb : x = b
  · simpa only [hxb] using hb
  have hcover : ({a, b, x} : Finset X) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hcard]
    simp [hab, Ne.symm hxa, Ne.symm hxb]
  have hmem : f x ∈ ({a, b, x} : Finset X) := by
    rw [hcover]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact (hxa (f.injective (h.trans ha.symm))).elim
  · exact (hxb (f.injective (h.trans hb.symm))).elim
  · exact h

/-- The neighboring-core intersection fixes two of the three neighbors, so
it belongs to the two-core of the first vertex. Only the actual local Sylow
data, rather than Section Seven's global hypotheses, are used. -/
public theorem gTwo_card64_elementary_intersection_le_core
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    data.D ≤ QAt data.Γ data.criticalPath.a := by
  classical
  let := data.groupK
  let := data.finiteK
  let P := GAt data.Γ data.criticalPath.a
  let E := P ⊓ GAt data.Γ data.criticalPath.firstStep
  let : Finite data.Γ.Vertex := data.Γ.finiteVertex
  let N := {v // data.Γ.adjacent data.criticalPath.a v}
  let := SectionNine.coset_neighbor_action data.Γ data.criticalPath.a
  let : MulAction.IsPretransitive P N := {
    exists_smul_eq := by
      intro first second
      obtain ⟨g, hg⟩ := (lemma_seven_one_graph data.Γ).local_transitivity
        data.criticalPath.a
        ((mem_neighborhood_iff_adjacent data.Γ).mpr first.property)
        ((mem_neighborhood_iff_adjacent data.Γ).mpr second.property)
      exact ⟨g⁻¹, Subtype.ext (by
        change data.Γ.act ((g : data.K)⁻¹)⁻¹ first = second
        simpa only [inv_inv] using hg)⟩ }
  let first : N := ⟨data.criticalPath.firstStep, data.criticalPath.firstStep_adj⟩
  let previous : N := ⟨data.aPrev,
    (mem_neighborhood_iff_adjacent data.Γ).mp data.caseA.previous_vertex.1⟩
  have hEmap : E.map data.embedding = (data.sylowIntersection : Subgroup G) := by
    dsimp [E, P]
    rw [Subgroup.map_inf _ _ _ data.embedding_injective]
    exact data.intersection_eq
  have hEcard : Nat.card E = 64 := by
    rw [← Subgroup.card_map_of_injective data.embedding_injective, hEmap]
    exact hcard
  have hEP : E ≤ P := inf_le_left
  have hPcard : Nat.card P = 192 := (gTwo_card64_vertex_structure data hcard).2.1
  have hindex : (E.subgroupOf P).index = 3 := by
    have h := (E.subgroupOf P).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv,
      hEcard, hPcard] at h
    omega
  have hdegree : Nat.card N = 3 := by
    rw [← MulAction.index_stabilizer_of_transitive P first,
      SectionNine.coset_neighbor_stabilizer]
    exact hindex
  let ρ := MulAction.toPermHom P N
  have hkerle : ρ.ker ≤ E.subgroupOf P := by
    rw [← SectionNine.coset_neighbor_stabilizer data.Γ data.criticalPath.a first]
    intro x hx
    exact congrArg (fun f : Equiv.Perm N => f first) (show ρ x = 1 from hx)
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 6) hEcard
  have hkerp : IsPGroup 2 ρ.ker :=
    (hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEP).symm).to_le hkerle
  have hkerCore : ρ.ker ≤ pCore 2 P := le_sSup ⟨inferInstance, hkerp⟩
  have hQG (v : data.Γ.Vertex) : QAt data.Γ v ≤ GAt data.Γ v := by
    change data.Γ.twoCoreAt v ≤ _
    rw [data.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  intro d hd
  have hd' := hd
  rw [data.caseA.definitions.1] at hd'
  have hdS := (gTwo_card64_cores_le_sylow data).2
    (Subgroup.mem_map_of_mem data.embedding hd'.2)
  have hdP : d ∈ P := by
    have hSP : (data.sylowIntersection : Subgroup G) ≤ P.map data.embedding := by
      rw [← data.intersection_eq]
      exact inf_le_left
    obtain ⟨y, hy, heq⟩ := hSP hdS
    exact data.embedding_injective heq ▸ hy
  have hfix (v : N) (hv : d ∈ GAt data.Γ v) : ρ ⟨d, hdP⟩ v = v := by
    apply Subtype.ext
    change data.Γ.act d⁻¹ v = v
    exact (Set.ext_iff.mp (data.Γ.stabilizer_def v) d⁻¹).mp
      ((GAt data.Γ v).inv_mem hv)
  have hdker : (⟨d, hdP⟩ : P) ∈ ρ.ker :=
    perm_three_eq_one_of_two_fixed hdegree (ρ ⟨d, hdP⟩)
      (a := first) (b := previous)
      (fun h => data.caseA.previous_vertex.2 (congrArg Subtype.val h).symm)
      (hfix first (hQG _ hd'.2)) (hfix previous (hQG _ hd'.1))
  change d ∈ data.Γ.twoCoreAt data.criticalPath.a
  rw [data.Γ.twoCoreAt_def]
  exact Subgroup.mem_map_of_mem P.subtype (hkerCore hdker)

/-- The actual elementary intersection supplies an involutive inverter in
both distinguished cores, generating the first core over its abelian base. -/
public theorem gTwo_card64_involutive_inverter
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    ∃ t : data.K,
      t ∈ data.D ∧
      t ∈ QAt data.Γ data.criticalPath.a ∧
      t ∈ QAt data.Γ data.criticalPath.firstStep ∧
      t ∉ twoCoreIn (EAt data.Γ data.criticalPath.a) ∧
      t ^ 2 = 1 ∧
      IsInvertingOn t (twoCoreIn (EAt data.Γ data.criticalPath.a)) ∧
      QAt data.Γ data.criticalPath.a =
        GeneratedWith (twoCoreIn (EAt data.Γ data.criticalPath.a)) t :=
  gTwo_card64_involutive_inverter_of_elementary_intersection data hcard
    (gTwo_card64_elementary_intersection_le_core data hcard)
    (gTwo_card64_elementary_intersection_card_gt_four data hcard)

/-- Sign-and-swap generators identifying the actual marked Sylow. -/
@[expose] public def GTwoCard64MarkedGenerators
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) : Prop :=
  letI := data.groupK
  letI := data.finiteK
  let S := (data.sylowIntersection : Subgroup G)
  let Qa := ((QAt data.Γ data.criticalPath.a).map data.embedding).subgroupOf S
  let Qb := ((QAt data.Γ data.criticalPath.firstStep).map data.embedding).subgroupOf S
  ∃ a b t u : data.sylowIntersection,
    C4SquareSignSwap.Relations a b t u ∧
    Subgroup.closure ({a, b, t, u} : Set data.sylowIntersection) = ⊤ ∧
    gTwoCard64TransferSubgroup data = Subgroup.closure ({a, b, u} : Set data.sylowIntersection) ∧
    Qa = Subgroup.closure ({a, b, t} : Set data.sylowIntersection) ∧
    Qb = Subgroup.closure ({a * b, a * b⁻¹, t, u} : Set data.sylowIntersection)

/-- A marked generator construction gives the simultaneous equivalence with the model. -/
public theorem gTwo_card64_marked_equiv_of_generators
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (hgen : GTwoCard64MarkedGenerators data) :
    letI := data.groupK
    letI := data.finiteK
    let S := (data.sylowIntersection : Subgroup G)
    let Qa := (QAt data.Γ data.criticalPath.a).map data.embedding
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    ∃ e : data.sylowIntersection ≃* C4SquareSignSwap.Model,
      (gTwoCard64TransferSubgroup data).map e.toMonoidHom = C4SquareSignSwap.transfer ∧
      (Qa.subgroupOf S).map e.toMonoidHom = C4SquareSignSwap.inverterCore ∧
      (Qb.subgroupOf S).map e.toMonoidHom = C4SquareSignSwap.extraspecialCore := by
  let := data.groupK
  let := data.finiteK
  obtain ⟨a, b, t, u, hrel, htop, hU, hQa, hQb⟩ := hgen
  exact C4SquareSignSwap.exists_marked_equiv_of_relations hcard _ _ _ hrel htop hU hQa hQb

/-- The actual order-64 Sylow admits sign-and-swap generators marking the
canonical transfer subgroup and both embedded vertex cores. -/
public theorem gTwo_card64_marked_generators
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) : GTwoCard64MarkedGenerators data := by
  let := data.groupK
  let := data.finiteK
  let S := (data.sylowIntersection : Subgroup G)
  let A0 := twoCoreIn (EAt data.Γ data.criticalPath.a)
  let R0 := QAt data.Γ data.criticalPath.firstStep ⊓ EAt data.Γ data.criticalPath.firstStep
  let lift (H : Subgroup data.K) := (H.map data.embedding).subgroupOf S
  let A := lift A0
  let R := lift R0
  let Qa := lift (QAt data.Γ data.criticalPath.a)
  let Qb := lift (QAt data.Γ data.criticalPath.firstStep)
  obtain ⟨hQaS, hQbS⟩ := gTwo_card64_cores_le_sylow data
  have hAmS : A0.map data.embedding ≤ S :=
    le_sup_left.trans (gTwo_card64_transfer_le_sylow data)
  have hRmS : R0.map data.embedding ≤ S :=
    le_sup_right.trans (gTwo_card64_transfer_le_sylow data)
  obtain ⟨hAN, hRN⟩ := gTwo_card64_transfer_factors_normal data
  let : A.Normal := hAN
  let : R.Normal := hRN
  have lift_equiv (H : Subgroup data.K) (hHS : H.map data.embedding ≤ S) :
      lift H ≃* H :=
    (Subgroup.subgroupOfEquivOfLe hHS).trans
      (H.equivMapOfInjective data.embedding data.embedding_injective).symm
  have hA : Nonempty (A ≃* C4 × C4) :=
    data.caseA.twoCore_model.map (fun e => (lift_equiv A0 hAmS).trans e)
  have hR : Nonempty (R ≃* Q8) :=
    data.caseA.next_twoCore.2.map (fun e => (lift_equiv R0 hRmS).trans e)
  have hRQ : R ≤ Qb := Subgroup.comap_mono (Subgroup.map_mono inf_le_left)
  have hQbi : Qb.index = 2 := (gTwo_card64_cores_index_two data hcard).2.2.2
  obtain ⟨_, _, _, _, B0, C0, hB0, hC0, hBC0, hinter0, hcomm0, _⟩ :=
    gTwo_card64_vertex_structure data hcard
  have hBmS : B0.map data.embedding ≤ S :=
    (Subgroup.map_mono (hBC0 ▸ le_sup_left)).trans hQbS
  have hCmS : C0.map data.embedding ≤ S :=
    (Subgroup.map_mono (hBC0 ▸ le_sup_right)).trans hQbS
  let B := lift B0
  let C := lift C0
  have hB : Nonempty (B ≃* Q8) :=
    hB0.map (fun e => (lift_equiv B0 hBmS).trans e)
  have hC : Nonempty (C ≃* Q8) :=
    hC0.map (fun e => (lift_equiv C0 hCmS).trans e)
  have hBC : Qb = B ⊔ C := by
    dsimp [Qb, B, C, lift]
    rw [hBC0, Subgroup.map_sup, Subgroup.subgroupOf_sup hBmS hCmS]
  have hinter : Nat.card (B ⊓ C : Subgroup S) = 2 := by
    have heq : B ⊓ C = lift (B0 ⊓ C0) := by
      dsimp [B, C, lift]
      rw [Subgroup.map_inf _ _ _ data.embedding_injective]
      rfl
    rw [heq, Nat.card_congr (lift_equiv (B0 ⊓ C0)
      ((Subgroup.map_mono inf_le_left).trans hBmS)).toEquiv]
    exact hinter0
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b := by
    intro b hb c hc
    obtain ⟨b0, hb0, heb⟩ := hb
    obtain ⟨c0, hc0, hec⟩ := hc
    change data.embedding b0 = (b : G) at heb
    change data.embedding c0 = (c : G) at hec
    apply Subtype.ext
    change (b : G) * (c : G) = (c : G) * (b : G)
    rw [← heb, ← hec, ← map_mul, ← map_mul, hcomm0 b0 hb0 c0 hc0]
  obtain ⟨t, _, htQa, htQb, _, ht2, hinv, hQa⟩ :=
    gTwo_card64_involutive_inverter data hcard
  have htS : data.embedding t ∈ S := hQaS ⟨t, htQa, rfl⟩
  let tS : S := ⟨data.embedding t, htS⟩
  have htQbS : tS ∈ Qb := ⟨t, htQb, rfl⟩
  have ht2S : tS ^ 2 = 1 := by
    apply Subtype.ext
    change data.embedding t ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hinvS : ∀ x ∈ A, tS * x * tS⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hx
    change data.embedding y = (x : G) at heq
    apply Subtype.ext
    change data.embedding t * (x : G) * (data.embedding t)⁻¹ = (x : G)⁻¹
    rw [← heq, ← map_inv, ← map_mul, ← map_mul, hinv y hy, map_inv]
  have hQaS' : Qa = A ⊔ Subgroup.zpowers tS := by
    apply (Subgroup.map_injective S.subtype_injective)
    change ((lift (QAt data.Γ data.criticalPath.a)).map S.subtype) = _
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hQaS,
      Subgroup.map_subgroupOf_eq_of_le hAmS]
    change (QAt data.Γ data.criticalPath.a).map data.embedding =
      A0.map data.embedding ⊔ Subgroup.zpowers (data.embedding t)
    rw [hQa, GeneratedWith, Subgroup.map_sup, MonoidHom.map_zpowers]
  obtain ⟨a, b, t', u, hrel, hgen, _, hU, hQa', hQb'⟩ :=
    C4SquareSignSwap.exists_marked_generators_of_split_local_structure hcard
      A R Qa Qb B C hA hR hRQ hQbi hBC hB hC hinter hcomm tS htQbS ht2S hinvS hQaS'
  refine ⟨a, b, t', u, hrel, hgen, ?_, hQa', hQb'⟩
  exact (Subgroup.subgroupOf_sup hAmS hRmS).trans hU

/-- The actual order-64 Sylow is the sign-and-swap model, with its canonical
transfer subgroup and both embedded vertex cores identified simultaneously. -/
public theorem gTwo_card64_marked_equiv
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let S := (data.sylowIntersection : Subgroup G)
    let Qa := (QAt data.Γ data.criticalPath.a).map data.embedding
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    ∃ e : data.sylowIntersection ≃* C4SquareSignSwap.Model,
      (gTwoCard64TransferSubgroup data).map e.toMonoidHom = C4SquareSignSwap.transfer ∧
      (Qa.subgroupOf S).map e.toMonoidHom = C4SquareSignSwap.inverterCore ∧
      (Qb.subgroupOf S).map e.toMonoidHom = C4SquareSignSwap.extraspecialCore :=
  gTwo_card64_marked_equiv_of_generators data hcard
    (gTwo_card64_marked_generators data hcard)

end Stellmacher.Recognition
