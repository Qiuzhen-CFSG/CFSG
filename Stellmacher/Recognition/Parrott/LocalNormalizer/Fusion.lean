module

public import Stellmacher.Recognition.Parrott.NormalizerFusion
public import Stellmacher.Recognition.Parrott.SecondNormalizerGrowthLocal
public import Stellmacher.Recognition.Parrott.LocalNormalizer.Core
public import Stellmacher.Recognition.Parrott.LocalNormalizer.FusionFromLocalData
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmegaElementaryQuotient

/-!
# Parrott's actual normalizer and fusion package from local hypotheses

The original derived-core normalizer identity and solvability of N_G(F)
provide the full core, omega, Sylow-three action and two-class fusion package.
Every conclusion uses the same second elementary subgroup and Sylow witnesses.
The final existence theorem applies the independently proved growth theorem
and discharges the strict normalizer-containment premise.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.675–678, Lemmas 5–6 and the two-class fusion argument.
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

/-- Extend any supplied second elementary witnesses without changing F or T.
The exact local inputs and the independently proved growth step suffice. -/
public theorem ParrottSecondElementaryData.exists_normalizer_fusion_of_local_inputs
    [Finite G]
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < N) :
    Nonempty (ParrottNormalizerFusionData d) := by
  obtain ⟨hsolv, hNcard, hKcard, hS3, hZKcard, hZKambient, hUcard, hZUcard,
      hZUambient, hFW, hWX, hXT, hZZ, hZE, hWC, hS4, Q, t, v, b, hQcard,
      ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hXC, hq, hvC, hZUfix, hFfix,
      hnc, hbX, hb4, hb2, hbC, hcyclic, hcard⟩ := d.exists_normalizer_core_of_local_inputs h hlocal hproper
  have hCD := d.normalizer_three_centralizer_le_derived_of_local_inputs h hlocal hproper Q
  obtain ⟨_, hSylow, hG, hZfusion, hFfusion, hJfusion⟩ :=
    d.normalizer_involution_fusion_from_local_data_of_local_inputs h hlocal hproper Q hCD v hv2 hFfix
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
    outer_transport := d.outer_involution_transport_of_local_inputs h hlocal hproper Q hCD v hv2 hFfix }⟩

/-- The actual second elementary data and its full normalizer/fusion package
exist from the original simple nonsolvable hypotheses and the source local inputs. -/
public theorem parrott_normalizer_fusion_exists_of_local_inputs
    [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (h : ParrottCentralizerHypotheses z)
    (hlocal : ParrottLocalInputs z) :
    ∃ d : ParrottSecondElementaryData z, Nonempty (ParrottNormalizerFusionData d) := by
  obtain ⟨d⟩ := parrott_second_elementary_of_derived_normalizer
    hns z h hlocal.derived_normalizer
  exact ⟨d, d.exists_normalizer_fusion_of_local_inputs h hlocal
    (d.sylow_lt_normalizer_of_local_inputs hns h hlocal)⟩

end Stellmacher.Recognition
