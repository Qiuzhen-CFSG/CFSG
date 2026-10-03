module

public import Stellmacher.Recognition.Parrott.SecondNormalizerGrowth
public import Stellmacher.Recognition.Parrott.NormalizerCore
public import Stellmacher.Recognition.Parrott.NormalizerFusionFromLocalData

/-!
# Parrott's second normalizer and the two involution classes

For the actual second elementary subgroup F and Sylow two-subgroup T, we
assemble the structure of N = N_G(F), K = O₂(N), and U = Ω₁(K), together
with compatible center generators t, v and a Sylow three-subgroup Q.
Every involution is conjugate to exactly one of z and v. The finer fusion
statements retain conjugators in C_G(z) ∨ N, for use in the generation
argument with these same witnesses.

Normalizer growth supplies T < N. The normalizer-core package then gives
the orders, centers, fixed lines, and cyclic order-four centralizer. Its
containment in the derived core discharges the last input of local fusion.
No normalizer order, fusion assertion, or auxiliary local hypothesis is
required by the existence theorems.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.675–678, Lemmas 5–6 and the fusion lemma printed as Lemma 8.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable (d : ParrottSecondElementaryData z)

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => pCore 2 H
set_option quotPrecheck false in
local notation "E" => (commutator J).map ((H).subtype.comp (J).subtype)
set_option quotPrecheck false in
local notation "N" => normalizer ((d).F : Set G)
set_option quotPrecheck false in
local notation "K" => pCore 2 N
set_option quotPrecheck false in
local notation "U" => omega₁ K (p := 2)
set_option quotPrecheck false in
local notation "X" => (K).map (N).subtype
set_option quotPrecheck false in
local notation "D" => (commutator X).map (X).subtype
set_option quotPrecheck false in
local notation "W" => (U).map ((N).subtype.comp (K).subtype)
set_option quotPrecheck false in
local notation "ZK" => (center K).map ((N).subtype.comp (K).subtype)
set_option quotPrecheck false in
local notation "ZU" => (center U).map (((N).subtype.comp (K).subtype).comp (U).subtype)
set_option quotPrecheck false in
local notation "L" => (H ⊔ N : Subgroup G)

/-- A compatible configuration on the supplied second elementary data.
All subgroup images are literal inclusions in G, and all fusion witnesses
in the supplied Sylow stay in the join used for subsequent generation. -/
public structure ParrottNormalizerFusionData where
  sylow_lt_normalizer : (d.sylow : Subgroup G) < N
  normalizer_solvable : Group.IsSolvable N
  normalizer_card : Nat.card N = 6144
  core_card : Nat.card K = 1024
  core_quotient : Nonempty ((N ⧸ K) ≃* Equiv.Perm (Fin 3))
  core_center_card : Nat.card (center K) = 4
  ambient_core_center_card : Nat.card ZK = 4
  omega_card : Nat.card U = 256
  omega_center_card : Nat.card (center U) = 8
  ambient_omega_center_card : Nat.card ZU = 8
  elementary_le_omega : d.F ≤ W
  omega_le_core : W ≤ X
  core_le_sylow : X ≤ (d.sylow : Subgroup G)
  core_center_le_omega_center : ZK ≤ ZU
  omega_center_le_inf : ZU ≤ E ⊓ d.F
  omega_eq_centralizer : W = X ⊓ centralizer (ZU : Set G)
  omega_quotient :
    letI : (U).Characteristic := omega₁_characteristic K
    let V := (U).map (K).subtype
    letI : V.Normal := ConjAct.normal_of_characteristic_of_normal
    Nonempty ((N ⧸ V) ≃* Equiv.Perm (Fin 4))
  Q : Sylow 3 N
  t : G
  v : G
  b : G
  three_card : Nat.card Q = 3
  t_mem_inf : t ∈ E ⊓ d.F
  v_mem_inf : v ∈ E ⊓ d.F
  t_order : orderOf t = 2
  v_order : orderOf v = 2
  t_not_mem_zpowers : t ∉ zpowers z
  v_not_mem_core_center : v ∉ ZK
  core_center_eq : ZK = zpowers z ⊔ zpowers t
  omega_center_eq : ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v
  core_eq_sylow_centralizer : X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
  three_conjugates_z_t : ∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t
  v_fixed : v ∈ centralizer ((Q : Subgroup N).map (N).subtype : Set G)
  omega_center_fixed :
    ZU ⊓ centralizer ((Q : Subgroup N).map (N).subtype : Set G) = zpowers v
  elementary_fixed :
    d.F ⊓ centralizer ((Q : Subgroup N).map (N).subtype : Set G) = zpowers v
  not_isConj : ¬ IsConj z v
  b_mem_core : b ∈ X
  b_order : orderOf b = 4
  b_sq : b ^ 2 = v
  core_fixed : X ⊓ centralizer ((Q : Subgroup N).map (N).subtype : Set G) = zpowers b
  core_fixed_cyclic :
    IsCyclic (X ⊓ centralizer ((Q : Subgroup N).map (N).subtype : Set G) : Subgroup G)
  core_fixed_card :
    Nat.card (X ⊓ centralizer ((Q : Subgroup N).map (N).subtype : Set G) : Subgroup G) = 4
  core_fixed_le_derived :
    X ⊓ centralizer ((Q : Subgroup N).map (N).subtype : Set G) ≤ D
  sylow_fusion : ∀ u : G, u ∈ (d.sylow : Subgroup G) → orderOf u = 2 →
    ∃ l : L, (l : G) * z * (l : G)⁻¹ = u ∨ (l : G) * v * (l : G)⁻¹ = u
  involution_classes : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u
  core_center_fusion : ∀ u : G, u ∈ ZK → orderOf u = 2 →
    ∃ l : L, (l : G) * z * (l : G)⁻¹ = u
  elementary_fusion : ∀ u : G, u ∈ d.F → u ∉ ZK →
    ∃ l : L, (l : G) * v * (l : G)⁻¹ = u
  original_core_fusion : ∀ u : G, u ∈ (J).map (H).subtype → u ∉ E → orderOf u = 2 →
    ∃ l : L, (l : G) * v * (l : G)⁻¹ = u
  derived_fusion : ∀ u : G, u ∈ E → u ∉ zpowers z →
    (∃ a : H, (a : G) * t * (a : G)⁻¹ = u) ∨
    (∃ a : H, (a : G) * v * (a : G)⁻¹ = u)
  outer_transport :
    ∀ u : G, u ∈ (d.sylow : Subgroup G) → u ∉ (J).map (H).subtype → orderOf u = 2 →
      ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E

/-- Extend any supplied second elementary witnesses without changing F or T.
The only assumptions are the original simple nonsolvable N₂ hypotheses. -/
public theorem ParrottSecondElementaryData.exists_normalizer_fusion
    [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottNormalizerFusionData d) := by
  have hproper := d.sylow_lt_normalizer hns hN h
  obtain ⟨hsolv, hNcard, hKcard, hS3, hZKcard, hZKambient, hUcard, hZUcard,
      hZUambient, hFW, hWX, hXT, hZZ, hZE, hWC, hS4, Q, t, v, b, hQcard,
      ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hXC, hq, hvC, hZUfix, hFfix,
      hnc, hbX, hb4, hb2, hbC, hcyclic, hcard⟩ := d.exists_normalizer_core h hN hproper
  have hCD := d.normalizer_three_centralizer_le_derived h hN hproper Q
  obtain ⟨_, hSylow, hG, hZfusion, hFfusion, hJfusion⟩ :=
    d.normalizer_involution_fusion_from_local_data h hN hproper Q hCD v hv2 hFfix
  have hzt : IsConj z t := by
    obtain ⟨q, hq⟩ := hq
    exact isConj_iff.mpr ⟨((q : N) : G), hq⟩
  have hvz : v ∉ zpowers z := by
    intro hvz
    exact hvZ (hZK.symm ▸ mem_sup_left hvz)
  exact ⟨{
    sylow_lt_normalizer := hproper
    normalizer_solvable := hsolv
    normalizer_card := hNcard
    core_card := hKcard
    core_quotient := hS3
    core_center_card := hZKcard
    ambient_core_center_card := hZKambient
    omega_card := hUcard
    omega_center_card := hZUcard
    ambient_omega_center_card := hZUambient
    elementary_le_omega := hFW
    omega_le_core := hWX
    core_le_sylow := hXT
    core_center_le_omega_center := hZZ
    omega_center_le_inf := hZE
    omega_eq_centralizer := hWC
    omega_quotient := hS4
    Q := Q
    t := t
    v := v
    b := b
    three_card := hQcard
    t_mem_inf := ht
    v_mem_inf := hv
    t_order := ht2
    v_order := hv2
    t_not_mem_zpowers := htz
    v_not_mem_core_center := hvZ
    core_center_eq := hZK
    omega_center_eq := hZU
    core_eq_sylow_centralizer := hXC
    three_conjugates_z_t := hq
    v_fixed := hvC
    omega_center_fixed := hZUfix
    elementary_fixed := hFfix
    not_isConj := hnc
    b_mem_core := hbX
    b_order := hb4
    b_sq := hb2
    core_fixed := hbC
    core_fixed_cyclic := hcyclic
    core_fixed_card := hcard
    core_fixed_le_derived := hCD
    sylow_fusion := hSylow
    involution_classes := hG
    core_center_fusion := hZfusion
    elementary_fusion := hFfusion
    original_core_fusion := hJfusion
    derived_fusion := ParrottSecondElementaryData.derived_fusion_of_distinct_representatives
      h t v ht.1 htz hv.1 hvz (fun htv => hnc (hzt.trans htv))
    outer_transport := d.outer_involution_transport h hN hproper Q hCD v hv2 hFfix }⟩

/-- The full normalizer and fusion configuration exists from the original
hypotheses, with the same second elementary data for every conclusion. -/
public theorem parrott_normalizer_fusion_exists [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ d : ParrottSecondElementaryData z, Nonempty (ParrottNormalizerFusionData d) := by
  obtain ⟨d⟩ := parrott_second_elementary_exists z hns hN h
  exact ⟨d, d.exists_normalizer_fusion hns hN h⟩

namespace ParrottNormalizerFusionData

variable {d} (c : ParrottNormalizerFusionData d)

/-- The chosen center generator is conjugate to z inside the actual normalizer. -/
public theorem isConj_z_t : IsConj z c.t := by
  obtain ⟨q, hq⟩ := c.three_conjugates_z_t
  exact isConj_iff.mpr ⟨((q : N) : G), hq⟩

/-- No element belongs to both of the two involution classes. -/
public theorem not_both_classes (u : G) : ¬ (IsConj z u ∧ IsConj c.v u) := by
  rintro ⟨hz, hv⟩
  exact c.not_isConj (hz.trans hv.symm)

end ParrottNormalizerFusionData

end Stellmacher.Recognition
