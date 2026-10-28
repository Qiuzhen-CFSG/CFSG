module

public import Stellmacher.Recognition.Parrott.NormalizerElementaryFusion
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmega
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeFixed
public import Stellmacher.Recognition.Parrott.LocalNormalizer.ElementaryCentralizer
public import Stellmacher.Recognition.Parrott.LocalNormalizer.ElementaryClassIntersection

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerElementaryFusion`.
-/

open Subgroup MulAction

private theorem conjugacy_of_complement_card
    {G : Type*} [Group G] [Finite G] (A B C : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) (hAC : A ≤ normalizer (C : Set G))
    (hCB : C ≤ B) (x : G) (hxB : x ∈ B) (hxC : x ∉ C)
    (hcount : Nat.card A = (Nat.card B - Nat.card C) *
      Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G)) :
    ∀ y : G, y ∈ B → y ∉ C → ∃ a : A, (a : G) * x * (a : G)⁻¹ = y := by
  classical
  let : Normalizes A B := ⟨hAB⟩
  let b : B := ⟨x, hxB⟩
  let S := stabilizer A b
  have hS : S.map A.subtype = A ⊓ centralizer ({x} : Set G) := by
    ext a
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (congrArg B.subtype ha))⟩
    · rintro ⟨haA, ha⟩
      refine ⟨⟨a, haA⟩, ?_, rfl⟩
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp ha))
  have hScard : Nat.card S = Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    rw [← hS, card_map_of_injective A.subtype_injective]
  have horbit : (orbit A b).ncard = Nat.card B - Nat.card C := by
    have hh := S.index_mul_card
    rw [show S.index = Nat.card (orbit A b) from index_stabilizer A b,
      hScard, hcount] at hh
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) hh
  let W : Set B := {y | (y : G) ∉ C}
  have hW : W.ncard = Nat.card B - Nat.card C := by
    have heq : W = Set.univ \ (C.subgroupOf B : Set B) := by
      ext y
      simp only [W, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, true_and]
      exact (not_congr (mem_subgroupOf : y ∈ C.subgroupOf B ↔ (y : G) ∈ C)).symm
    rw [heq]
    rw [Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ,
      ← Nat.card_coe_set_eq]
    change Nat.card B - Nat.card (C.subgroupOf B) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hCB).toEquiv]
  have hsub : orbit A b ⊆ W := by
    rintro _ ⟨a, rfl⟩ hc
    exact hxC ((mem_normalizer_iff.mp (hAC a.property) x).mpr hc)
  have heq : orbit A b = W := Set.eq_of_subset_of_ncard_le hsub (by omega)
  intro y hyB hyC
  have hy : (⟨y, hyB⟩ : B) ∈ orbit A b := heq.symm ▸ hyC
  obtain ⟨a, ha⟩ := hy
  exact ⟨a, congrArg B.subtype ha⟩

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The three nonidentity elements of the actual core center are conjugate to z
by elements of N, hence by elements of H∨N. -/
public theorem normalizer_core_center_involution_fusion_in_join_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let ZK := (center K).map (N.subtype.comp K.subtype)
    ∀ u : G, u ∈ ZK → orderOf u = 2 →
      ∃ l : (H ⊔ N : Subgroup G), (l : G) * z * (l : G)⁻¹ = u := by
  intro H N K ZK u hu hu2
  have hZcard : Nat.card ZK = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.2.2
  have hz : z ∉ (⊥ : Subgroup G) := by
    intro hz
    have hz1 : z = 1 := hz
    simpa [hz1] using h.involution
  have hu1 : u ∉ (⊥ : Subgroup G) := by
    intro hu1
    have hu' : u = 1 := hu1
    simp [hu'] at hu2
  obtain ⟨n, hn⟩ := conjugacy_of_complement_card N ZK ⊥
    d.normalizer_core_centers_normalized.1 le_normalizer_of_normal bot_le z
    d.z_mem_normalizer_core_center hz (by
      rw [hZcard, Subgroup.card_bot, d.normalizer_inf_centralizer h,
        d.sylow_card h, (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).1]) u hu hu1
  exact ⟨⟨n, mem_sup_right n.property⟩, hn⟩

private theorem involution_eq_of_mem_cyclic
    {v w : G} (hv : orderOf v = 2) (hw : orderOf w = 2) (hmem : w ∈ zpowers v) :
    w = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hv] at hmem
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hmem
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · have hw1 : w = 1 := by simpa using heq.symm
    simp [hw1] at hw
  · simpa using heq.symm

/-- The supplied fixed-line generator has the same center geometry as the
existentially chosen generator; the witness v is preserved. -/
public theorem normalizer_three_prescribed_fixed_generator_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    v ∈ E ⊓ d.F ∧ v ∉ ZK ∧ ZU = ZK ⊔ zpowers v ∧ ¬ IsConj z v := by
  intro H J E N K U ZK ZU
  obtain ⟨t, w, _, hw, _, hw2, _, hwZ, hZK, hZU, _, hwC, _, _, hnc⟩ :=
    d.exists_normalizer_three_fixed_generators_of_local_inputs h hlocal hproper Q
  have hwv : w = v := involution_eq_of_mem_cyclic hv hw2 (hfix ▸ ⟨hw.2, hwC⟩)
  subst w
  change ZK = zpowers z ⊔ zpowers t at hZK
  change ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v at hZU
  exact ⟨hw, hwZ, by rw [hZK]; exact hZU, hnc⟩

/-- The centralizer in the actual normalizer core of the prescribed v is
exactly the ambient omega subgroup. -/
public theorem normalizer_core_fixed_involution_centralizer_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    K.map N.subtype ⊓ centralizer ({v} : Set G) = U.map (N.subtype.comp K.subtype) := by
  intro N K U
  let X := K.map N.subtype
  let ZK := (center K).map (N.subtype.comp K.subtype)
  let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
  have hjoin : ZU = ZK ⊔ zpowers v :=
    (d.normalizer_three_prescribed_fixed_generator_of_local_inputs h hlocal hproper Q v hv hfix).2.2.1
  have hXC : X ≤ centralizer (ZK : Set G) := by
    rintro x ⟨xN, hxK, rfl⟩ k ⟨kK, hkZ, rfl⟩
    exact (congrArg (N.subtype.comp K.subtype)
      (mem_center_iff.mp hkZ (⟨xN, hxK⟩ : K))).symm
  rw [(d.normalizer_core_omega_structure_of_local_inputs h hlocal hproper).2.2.2]
  change X ⊓ centralizer ({v} : Set G) = X ⊓ centralizer (ZU : Set G)
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hh : ZU ≤ centralizer ({x} : Set G) := by
      rw [hjoin]
      apply sup_le
      · intro k hk
        exact mem_centralizer_singleton_iff.mpr (hXC hx.1 k hk)
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hx.2).symm)
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hh hk)
  · apply inf_le_inf_left
    apply centralizer_le
    intro w hw
    have hwv : w = v := Set.mem_singleton_iff.mp hw
    change w ∈ ZU
    rw [hwv, hjoin]
    exact mem_sup_right (mem_zpowers v)

/-- Every element of Z(Ω₁(K)) outside Z(K) is conjugate to the prescribed v
by an element of the actual core, hence of H∨N. -/
public theorem normalizer_omega_center_fusion_in_join_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∀ u : G, u ∈ ZU → u ∉ ZK →
      ∃ l : (H ⊔ N : Subgroup G), (l : G) * v * (l : G)⁻¹ = u := by
  intro H N K U ZK ZU u hu huZ
  let X := K.map N.subtype
  have hXN : X ≤ N := map_subtype_le _
  have hZcard : Nat.card ZK = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.2.2
  have hZUcard : Nat.card ZU = 8 :=
    (card_map_of_injective (K := center U)
      (f := (N.subtype.comp K.subtype).comp U.subtype)
      ((N.subtype_injective.comp K.subtype_injective).comp U.subtype_injective)).trans
      (d.normalizer_core_omega_structure_of_local_inputs h hlocal hproper).2.1
  have hvdata := d.normalizer_three_prescribed_fixed_generator_of_local_inputs h hlocal hproper Q v hv hfix
  have hjoin : ZU = ZK ⊔ zpowers v := hvdata.2.2.1
  have hvZU : v ∈ ZU := by rw [hjoin]; exact mem_sup_right (mem_zpowers v)
  have hCcard : Nat.card (X ⊓ centralizer ({v} : Set G) : Subgroup G) = 256 := by
    rw [d.normalizer_core_fixed_involution_centralizer_of_local_inputs h hlocal hproper Q v hv hfix]
    exact (card_map_of_injective (K := U) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_omega_structure_of_local_inputs h hlocal hproper).1
  have hXcard : Nat.card X = 1024 :=
    (card_map_of_injective (K := K) N.subtype_injective).trans
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  obtain ⟨x, hx⟩ := conjugacy_of_complement_card X ZU ZK
    (hXN.trans d.normalizer_core_centers_normalized.2)
    (hXN.trans d.normalizer_core_centers_normalized.1)
    d.normalizer_core_omega_inclusions.2.1 v hvZU hvdata.2.1 (by
      rw [hZcard, hZUcard, hCcard, hXcard]) u hu huZ
  exact ⟨⟨x, mem_sup_right (hXN x.property)⟩, hx⟩

/-- A point of F outside the omega center with normalizer centralizer of
order 256 has all 24 points of that complement as its N-orbit. -/
public theorem normalizer_elementary_outside_omega_center_fusion_of_centralizer_card_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∀ w : G, w ∈ d.F → w ∉ ZU →
      Nat.card (N ⊓ centralizer ({w} : Set G) : Subgroup G) = 256 →
      ∀ u : G, u ∈ d.F → u ∉ ZU →
        ∃ n : N, (n : G) * w * (n : G)⁻¹ = u := by
  intro N K U ZU w hwF hwZ hcard
  have hZUcard : Nat.card ZU = 8 :=
    (card_map_of_injective (K := center U)
      (f := (N.subtype.comp K.subtype).comp U.subtype)
      ((N.subtype_injective.comp K.subtype_injective).comp U.subtype_injective)).trans
      (d.normalizer_core_omega_structure_of_local_inputs h hlocal hproper).2.1
  exact conjugacy_of_complement_card N d.F ZU le_rfl
    d.normalizer_core_centers_normalized.2 d.normalizer_core_omega_inclusions.2.2
    w hwF hwZ (by rw [d.card, hZUcard, hcard,
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).1])

/-- Assemble the two finer fusion assertions from the remaining local
centralizer calculation and the connection to the H-class of v. -/
public theorem elementary_fusion_in_join_of_local_calculations_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    let L := H ⊔ N
    (∀ w : G, w ∈ E ⊓ d.F → w ∉ ZU →
      Nat.card (N ⊓ centralizer ({w} : Set G) : Subgroup G) = 256) →
    (∃ w : G, w ∈ E ⊓ d.F ∧ w ∉ ZU ∧
      ∃ a : H, (a : G) * v * (a : G)⁻¹ = w) →
    (∀ u : G, u ∈ ZK → orderOf u = 2 →
      ∃ l : L, (l : G) * z * (l : G)⁻¹ = u) ∧
    (∀ u : G, u ∈ d.F → u ∉ ZK →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) := by
  intro H J E N K U ZK ZU L hcount hwitness
  refine ⟨d.normalizer_core_center_involution_fusion_in_join_of_local_inputs h hlocal hproper, ?_⟩
  intro u huF huZ
  by_cases huU : u ∈ ZU
  · exact d.normalizer_omega_center_fusion_in_join_of_local_inputs h hlocal hproper Q v hv hfix u huU huZ
  obtain ⟨w, hw, hwU, a, ha⟩ := hwitness
  obtain ⟨n, hn⟩ := d.normalizer_elementary_outside_omega_center_fusion_of_centralizer_card_of_local_inputs
    h hlocal hproper w hw.2 hwU (hcount w hw hwU) u huF huU
  let nL : L := ⟨n, mem_sup_right n.property⟩
  let aL : L := ⟨a, mem_sup_left a.property⟩
  refine ⟨nL * aL, ?_⟩
  change ((n : G) * (a : G)) * v * ((n : G) * (a : G))⁻¹ = u
  calc
    _ = (n : G) * ((a : G) * v * (a : G)⁻¹) * (n : G)⁻¹ := by group
    _ = u := by rw [ha, hn]

end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The order-256 centralizer calculation and the fixed-class intersection
complete the finer fusion in the supplied elementary subgroup.  Every
conjugator is retained in the actual join `C_G(z) ⊔ N_G(F)`.

The `hCD` premise is the supplied derived-centralizer input used by the
surrounding Parrott assembly; this local fusion argument consumes the two
proved local consequences independently.
-/
public theorem normalizer_elementary_fusion_in_join_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G)))
    (hCD : let N := normalizer (d.F : Set G)
      let K := pCore 2 N
      let X := K.map N.subtype
      let D := (commutator X).map X.subtype
      let A := (Q : Subgroup N).map N.subtype
      X ⊓ centralizer (A : Set G) ≤ D)
    (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer
      ((Q : Subgroup (normalizer (d.F : Set G))).map
        (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let _E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let _ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    let L := H ⊔ N
    (∀ u : G, u ∈ ZK → orderOf u = 2 →
      ∃ l : L, (l : G) * z * (l : G)⁻¹ = u) ∧
    (∀ u : G, u ∈ d.F → u ∉ ZK →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u) := by
  have _hCD := hCD
  exact d.elementary_fusion_in_join_of_local_calculations_of_local_inputs h hlocal hproper Q v hv hfix
    (fun w hw hwZ =>
      d.normalizer_elementary_outside_omega_center_centralizer_card_of_local_inputs
        h hlocal hproper w hw hwZ)
    (d.normalizer_fixed_class_meets_elementary_complement_of_local_inputs
      h hlocal hproper Q v hv hfix)

end Stellmacher.Recognition.ParrottSecondElementaryData
