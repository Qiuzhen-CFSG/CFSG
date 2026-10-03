module

public import Theory.GroupTheory.NormalCoverIntersection
public import Stellmacher.PushingUp.DistanceFourInitialRelations
public import Stellmacher.PushingUp.CriticalPairMiddleSylow
public import Stellmacher.PushingUp.CriticalPairCoreIntersectionGeneration

/-!
# The core product at critical distance four

This module proves `Q_a = D U` in the chosen five-vertex configuration, where
`D` is the intersection of its five vertex cores and `U = Z_a Z_c Z_u`.
It is the product assertion in Stellmacher, *Pushing up* (1986), (3.3)(1),
journal p.15, with the original pushing-up hypotheses and `b = 4`.

The four shared-Sylow covers are `Q_a ≤ Z_c Q_u`, `Q_a ≤ Z_u Q_c`,
`Q_u ≤ Z_a Q_v`, and `Q_c ≤ Z_a Q_(a')`. First cancel an element of `Q_a`
by `Z_c` and then `Z_u`, leaving `K = Q_a ∩ Q_u ∩ Q_c`. Within `K`, the
normal subgroups induced by `Q_v` and `Q_(a')` each have supplement `Z_a`.
The two critical opposite vertices generate the local action, so their
core intersections generate `Z_a`. The normal-cover intersection theorem
therefore gives `K ≤ Z_a D`. Combining the cancellations proves the result.

All auxiliary factorization calculations are private. The production source
subgroups are used throughout; no finite vertex-set or free-amalgam instance
and no unproved source equation is assumed.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem mem_sup_of_normalizes_right
    {G : Type*} [Group G] (A B : Subgroup G)
    (hn : A ≤ Subgroup.normalizer B) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let H := A ⊔ B
  let AI := A.subgroupOf H
  let BI := B.subgroupOf H
  let _ : BI.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hn
  have htop : AI ⊔ BI = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (show A ≤ H from le_sup_left),
      Subgroup.map_subgroupOf_eq_of_le (show B ≤ H from le_sup_right),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hxI : (⟨x, hx⟩ : H) ∈ AI ⊔ BI := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, heq⟩ := Subgroup.mem_sup_of_normal_right.mp hxI
  exact ⟨a, ha, b, hb, congrArg Subtype.val heq⟩

private theorem subgroupOf_cover_eq_top
    {G : Type*} [Group G] (A B K : Subgroup G)
    (hAK : A ≤ K) (hK : K ≤ A ⊔ B) (hn : K ≤ Subgroup.normalizer B) :
    A.subgroupOf K ⊔ B.subgroupOf K = ⊤ := by
  apply top_unique
  intro k _hk
  obtain ⟨a, ha, b, hb, heq⟩ := mem_sup_of_normalizes_right A B
    (hAK.trans hn) (hK k.property)
  have hbK : b ∈ K := by
    have h := K.mul_mem (K.inv_mem (hAK ha)) k.property
    rw [← heq] at h
    simpa only [inv_mul_cancel_left] using h
  have hprod : (⟨a, hAK ha⟩ : K) * ⟨b, hbK⟩ = k := Subtype.ext heq
  rw [← hprod]
  exact (A.subgroupOf K ⊔ B.subgroupOf K).mul_mem
    ((show A.subgroupOf K ≤ A.subgroupOf K ⊔ B.subgroupOf K from le_sup_left) ha)
    ((show B.subgroupOf K ≤ A.subgroupOf K ⊔ B.subgroupOf K from le_sup_right) hb)

private theorem first_core_cancellation
    {G : Type*} [Group G] (Q B C R T : Subgroup G)
    (hQR : Q ≤ B ⊔ R) (hQT : Q ≤ C ⊔ T)
    (hB : B ≤ Q ⊓ T) (hC : C ≤ Q ⊓ R)
    (hnB : B ≤ Subgroup.normalizer R) (hnC : C ≤ Subgroup.normalizer T) :
    Q ≤ (Q ⊓ R ⊓ T) ⊔ B ⊔ C := by
  intro q hq
  obtain ⟨b, hb, r, hr, hbr⟩ := mem_sup_of_normalizes_right B R hnB (hQR hq)
  have hrQ : r ∈ Q := by
    have h := Q.mul_mem (Q.inv_mem (hB hb).1) hq
    rw [← hbr] at h
    simpa only [inv_mul_cancel_left] using h
  obtain ⟨c, hc, t, ht, hct⟩ := mem_sup_of_normalizes_right C T hnC (hQT hrQ)
  have htQ : t ∈ Q := by
    have h := Q.mul_mem (Q.inv_mem (hC hc).1) hrQ
    rw [← hct] at h
    simpa only [inv_mul_cancel_left] using h
  have htR : t ∈ R := by
    have h := R.mul_mem (R.inv_mem (hC hc).2) hr
    rw [← hct] at h
    simpa only [inv_mul_cancel_left] using h
  rw [← hbr, ← hct]
  apply ((Q ⊓ R ⊓ T) ⊔ B ⊔ C).mul_mem
  · exact (show B ≤ (Q ⊓ R ⊓ T) ⊔ B ⊔ C from le_sup_right.trans le_sup_left) hb
  · apply ((Q ⊓ R ⊓ T) ⊔ B ⊔ C).mul_mem
    · exact (show C ≤ (Q ⊓ R ⊓ T) ⊔ B ⊔ C from le_sup_right) hc
    · exact (show Q ⊓ R ⊓ T ≤ (Q ⊓ R ⊓ T) ⊔ B ⊔ C from
        le_sup_left.trans le_sup_left) ⟨⟨htQ, htR⟩, ht⟩

private theorem last_core_cancellation
    {G : Type*} [Group G] (A B C K : Subgroup G)
    (hAK : A ≤ K) (hKB : K ≤ A ⊔ B) (hKC : K ≤ A ⊔ C)
    (hAn : K ≤ Subgroup.normalizer A)
    (hBn : K ≤ Subgroup.normalizer B) (hCn : K ≤ Subgroup.normalizer C)
    (hA : A = (A ⊓ B) ⊔ (A ⊓ C)) :
    K ≤ A ⊔ (K ⊓ B ⊓ C) := by
  let AI := A.subgroupOf K
  let BI := B.subgroupOf K
  let CI := C.subgroupOf K
  let _ : AI.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAn
  let _ : BI.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBn
  let _ : CI.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCn
  have hAB : AI ⊔ BI = ⊤ := subgroupOf_cover_eq_top A B K hAK hKB hBn
  have hAC : AI ⊔ CI = ⊤ := subgroupOf_cover_eq_top A C K hAK hKC hCn
  have hAI : (AI ⊓ BI) ⊔ (AI ⊓ CI) = AI := by
    apply Subgroup.map_injective K.subtype_injective
    have hABK : A ⊓ B ≤ K := inf_le_left.trans hAK
    have hACK : A ⊓ C ≤ K := inf_le_left.trans hAK
    have hABI : AI ⊓ BI = (A ⊓ B).subgroupOf K := rfl
    have hACI : AI ⊓ CI = (A ⊓ C).subgroupOf K := rfl
    rw [hABI, hACI, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hABK,
      Subgroup.map_subgroupOf_eq_of_le hACK,
      Subgroup.map_subgroupOf_eq_of_le hAK]
    exact hA.symm
  have htop := Subgroup.sup_inf_eq_top_of_normal_covers AI BI CI hAB hAC hAI
  intro k hk
  have hkI : (⟨k, hk⟩ : K) ∈ AI ⊔ (BI ⊓ CI) := by rw [htop]; trivial
  have hmap := Subgroup.mem_map_of_mem K.subtype hkI
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAK] at hmap
  apply (show A ⊔ (BI ⊓ CI).map K.subtype ≤ A ⊔ (K ⊓ B ⊓ C) from ?_) hmap
  apply sup_le le_sup_left
  apply le_trans ?_ le_sup_right
  rintro x ⟨xi, hxi, rfl⟩
  exact ⟨⟨xi.property, hxi.1⟩, hxi.2⟩


private theorem adjacent_for_initial (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) : ∃ d : Vertex S, Adjacent S a d := by
  obtain ⟨g, rfl⟩ := ha
  exact ⟨act S g (hVertex S 1),
    (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2 (base_adjacent S)⟩

private theorem strict_core_for_initial [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (x y : Vertex S) (hx : InMVertexOrbit S x) (hy : InMVertexOrbit S y)
    (hlt : (cosetGraph S).dist x y < criticalDistance S) :
    vertexZ S x ≤ vertexTwoCore S y := by
  obtain ⟨d, hyd⟩ := adjacent_for_initial S y hy
  rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS y d hy hyd]
  exact vertexZ_le_neighborhoodKernel_of_dist_lt S hx hlt

private theorem core_normalized_for_product (S : Subgroup M) (a : Vertex S) :
    stabilizer S a ≤ Subgroup.normalizer (vertexTwoCore S a) := by
  have hle : vertexTwoCore S a ≤ stabilizer S a :=
    Subgroup.map_subtype_le _
  have hn : ((vertexTwoCore S a).subgroupOf (stabilizer S a)).Normal := by
    rw [← Subgroup.comap_subtype, vertexTwoCore, twoCoreAmbient,
      Subgroup.comap_map_eq_self_of_injective (stabilizer S a).subtype_injective]
    exact (inferInstance : (pCore 2 (stabilizer S a)).Normal)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hn

private theorem sylowIn_le_for_product
    {G : Type*} [Group G] {P H : Subgroup G} (h : IsSylowSubgroupIn P H) : P ≤ H := by
  obtain ⟨PI, hPI⟩ := h
  rw [← hPI]
  exact Subgroup.map_subtype_le _

set_option maxHeartbeats 800000 in
public theorem distanceFour_core_product [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (hconf : DistanceFour.Configuration S a a' c u v) :
    vertexTwoCore S a = DistanceFour.D S a a' c u v ⊔ DistanceFour.U S a c u := by
  have hb : 0 < criticalDistance S := by omega
  have htwo : 2 < criticalDistance S := by omega
  have hcrit := hconf.critical
  have hu := hconf.first_shift
  have hv := hconf.second_shift
  have hinit := distanceFour_initialRelations S T hTS hP hSne hA
    a a' c u v hb4 hconf
  have hac : (cosetGraph S).dist a c = 2 := by
    have := hconf.first_frame.left_length
    omega
  obtain ⟨_, _, hUC⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c hu.shifted_critical hb
  obtain ⟨_, _, hAA'⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    a a' hcrit hb
  obtain ⟨_, _, hVA⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    v a hv.shifted_critical hb
  have hc := (criticalPair_path T hTS hP hSne u c hu.shifted_critical hb)
    |>.opposite_inMVertexOrbit
  obtain ⟨hQaCover, _⟩ := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    a a' c u hcrit htwo hconf.first_frame hu
  obtain ⟨hQuCover, _⟩ := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    u c a v hu.shifted_critical htwo hconf.second_frame hv
  obtain ⟨_, hQaCover'⟩ := criticalPair_middleSylow S T hTS hP hSne hA
    c u a hUC.critical.reverse_critical hb hcrit.1
    (by rw [SimpleGraph.dist_comm]; exact hac)
    (by rw [SimpleGraph.dist_comm]; have := hu.distance_two; omega)
  obtain ⟨_, hQcCover⟩ := criticalPair_middleSylow S T hTS hP hSne hA
    a' a c hAA'.critical.reverse_critical hb hc
    (by rw [SimpleGraph.dist_comm]; exact hconf.first_frame.right_length)
    (by omega)
  have hZuQu : vertexZ S u ≤ vertexTwoCore S u := fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ z).mp (hUC.left_Z_le_coreOmega hz)).1
  have hZcQc : vertexZ S c ≤ vertexTwoCore S c := fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ z).mp (hUC.right_Z_le_coreOmega hz)).1
  have hZuQa : vertexZ S u ≤ vertexTwoCore S a := le_sup_right.trans hinit.U_le_core
  have hZcQa : vertexZ S c ≤ vertexTwoCore S a :=
    le_sup_right.trans le_sup_left |>.trans hinit.U_le_core
  have hZaQa : vertexZ S a ≤ vertexTwoCore S a :=
    le_sup_left.trans le_sup_left |>.trans hinit.U_le_core
  have hZaQu : vertexZ S a ≤ vertexTwoCore S u :=
    strict_core_for_initial S T hTS a u hcrit.1 hu.shifted_critical.1 (by
      have := hu.distance_two
      omega)
  have hZaQc : vertexZ S a ≤ vertexTwoCore S c :=
    strict_core_for_initial S T hTS a c hcrit.1 hc (by omega)
  have hZcGu : vertexZ S c ≤ stabilizer S u :=
    (criticalPair_path T hTS hP hSne u c hu.shifted_critical hb)
      |>.right_Z_le_left_stabilizer
  have hZuGc : vertexZ S u ≤ stabilizer S c := hUC.left_Z_le_right_stabilizer
  have hfirst := first_core_cancellation (vertexTwoCore S a)
    (vertexZ S c) (vertexZ S u) (vertexTwoCore S u) (vertexTwoCore S c)
    hQaCover hQaCover' (le_inf hZcQa hZcQc) (le_inf hZuQa hZuQu)
    (hZcGu.trans (core_normalized_for_product S u))
    (hZuGc.trans (core_normalized_for_product S c))
  let K := vertexTwoCore S a ⊓ vertexTwoCore S u ⊓ vertexTwoCore S c
  have hZaK : vertexZ S a ≤ K := le_inf (le_inf hZaQa hZaQu) hZaQc
  have hKQa : K ≤ vertexTwoCore S a := inf_le_left.trans inf_le_left
  have hKQu : K ≤ vertexTwoCore S u := inf_le_left.trans inf_le_right
  have hKQc : K ≤ vertexTwoCore S c := inf_le_right
  have hKGa : K ≤ stabilizer S a := hKQa.trans (Subgroup.map_subtype_le _)
  obtain ⟨_, _, h22VA⟩ := criticalPair_sl2Two S T hTS hP hSne hA
    v a hv.shifted_critical hb
  obtain ⟨_, _, h22A'A⟩ := criticalPair_sl2Two S T hTS hP hSne hA
    a' a hAA'.critical.reverse_critical hb
  have hKGv : K ≤ stabilizer S v :=
    (hKQu.trans hQuCover).trans (sylowIn_le_for_product h22VA.sourceSylow)
  have hKGa' : K ≤ stabilizer S a' :=
    (hKQc.trans hQcCover).trans (sylowIn_le_for_product h22A'A.sourceSylow)
  have hKnormZa : K ≤ Subgroup.normalizer (vertexZ S a) := hKGa.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (vertexZ_le_stabilizer S a)).mp
      (vertexZ_normal_stabilizer S a))
  have hZaGen := criticalPair_coreIntersections_generate S T hTS hP hSne hA
    a v a' hVA.critical.reverse_critical hcrit hb hinit.F_generates_modulo_core
  have hlast := last_core_cancellation (vertexZ S a) (vertexTwoCore S v)
    (vertexTwoCore S a') K hZaK (hKQu.trans hQuCover) (hKQc.trans hQcCover)
    hKnormZa (hKGv.trans (core_normalized_for_product S v))
    (hKGa'.trans (core_normalized_for_product S a')) hZaGen
  have hD : DistanceFour.D S a a' c u v = K ⊓ vertexTwoCore S v ⊓ vertexTwoCore S a' := by
    dsimp [DistanceFour.D, K]
    ac_rfl
  rw [← hD] at hlast
  apply le_antisymm
  · apply hfirst.trans
    apply sup_le
    · apply sup_le
      · apply hlast.trans
        exact sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right) le_sup_left
      · exact (le_sup_right.trans le_sup_left).trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  · apply sup_le
    · rw [hD]
      exact inf_le_left.trans inf_le_left |>.trans hKQa
    · exact hinit.U_le_core

end Stellmacher.PushingUp
