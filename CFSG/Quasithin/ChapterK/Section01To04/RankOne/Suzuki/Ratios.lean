module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Suzuki.Group
public import Theory.Representation.Suzuki.NaturalMatrix
public import Theory.Representation.BinaryOffender.InvolutionRatio
import Mathlib.Tactic

/-!
# The Suzuki natural action on the original source module

The marked group and binary linear equivalences transport the matrix fixed
codimension and quadraticity calculations using the actual layer inclusion.
Odd outer order puts all elementary two-subgroups in that layer. Their fixed
codimension is 2r and their rank is at most r, with equality in a prescribed
Sylow subgroup exactly at Ω₁(T). This proves both global infima and the
literal singleton description of Q(T,V). Rank-nullity also gives freeness
of each involution as equality of its displacement image and kernel.

The only recognition input is SuzukiModel; the original SourceHypotheses
supply all ambient assumptions. Source: Aschbacher–Smith, K.3.6, printed
p.457, and Definition D.2.1, printed p.178 (1 March 2004 manuscript).
-/

public section
open BenderSuzuki BenderSuzuki.MatrixGroups Subgroup
open Representation Representation.BinaryOffender
open scoped ENNReal
namespace CFSG.Quasithin.ChapterK.RankOne
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {m : ℕ} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

namespace SuzukiModel
variable (M : SuzukiModel m ρ L)
include M

omit [Finite G] in
/-- The identified natural layer gives the fixed codimension on the original module. -/
theorem elementary_fixedCodim (hm : 1 ≤ m) {A : Subgroup G}
    (hA : IsElementaryTwo A) (hAL : A ≤ L) : fixedCodim ρ A = 2 * (2 * m + 1) := by
  let B := A.subgroupOf L
  let C := B.map M.groupEquiv.toMonoidHom
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAL
  have hC : IsElementaryTwo C := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hz
    have hB : B = ⊥ := (map_eq_bot_iff_of_injective B M.groupEquiv.injective).mp hz
    change A.subgroupOf L = ⊥ at hB
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAL, hB, Subgroup.map_bot]
  have he := fixedCodim_map_equivariant (ρ.comp L.subtype) (SuzukiNatural.natural m)
    M.groupEquiv.toMonoidHom M.coordinates M.intertwines B
  have hf := fixedSpace_comp_map ρ L.subtype B
  rw [map_subgroupOf_eq_of_le hAL] at hf
  change fixedCodim (ρ.comp L.subtype) B = fixedCodim (SuzukiNatural.natural m) C at he
  rw [fixedCodim, hf] at he
  exact he.trans (SuzukiNatural.elementary_fixedCodim (by omega) hC)

omit [Finite G] in
/-- Transport quadraticity using the literal inclusion of the marked layer. -/
theorem quadratic_of_model {A : Subgroup L}
    (hq : IsQuadratic (SuzukiNatural.natural m) (A.map M.groupEquiv.toMonoidHom)) :
    IsQuadratic ρ (A.map L.subtype) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  apply M.coordinates.injective
  have he (g : L) (w : V) : M.coordinates (ρ (g : G) w) =
      SuzukiNatural.natural m (M.groupEquiv g) (M.coordinates w) := M.intertwines g w
  change M.coordinates (ρ (a : G) (ρ (b : G) v - v)) = M.coordinates (ρ (b : G) v - v)
  rw [he, map_sub, he, map_sub]
  have hh := hq (M.groupEquiv a) ⟨a, ha, rfl⟩ (M.groupEquiv b) ⟨b, hb, rfl⟩ (M.coordinates v)
  rw [map_sub] at hh
  exact hh

/-- The ambient image of a layer Sylow omega acts quadratically. -/
theorem sylowImage_omega_quadratic (hm : 1 ≤ m) (P : Sylow 2 L) :
    IsQuadratic ρ (omegaOneAmbient ((P : Subgroup L).map L.subtype)) := by
  let Q : Sylow 2 (SuzukiMatrixGroup m) :=
    P.mapSurjective (f := M.groupEquiv.toMonoidHom) M.groupEquiv.surjective
  rw [← map_omegaOneAmbient_injective L.subtype L.subtype_injective]
  apply M.quadratic_of_model
  rw [map_omegaOneAmbient_injective M.groupEquiv.toMonoidHom M.groupEquiv.injective]
  exact SuzukiNatural.sylow_omega_quadratic (by omega) Q

end SuzukiModel

namespace SourceHypotheses
variable (h : SourceHypotheses ρ L) (M : SuzukiModel m ρ L) (hm : 1 ≤ m)
include h M hm

/-- Odd outer order places every elementary two-actor in the actual layer. -/
theorem suzuki_elementary_le_layer {A : Subgroup G} (hA : IsElementaryTwo A) : A ≤ L := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  exact hAT.trans (h.suzuki_sylow_le M hm T)

/-- Every nontrivial elementary two-actor has fixed codimension 2r. -/
theorem suzuki_elementary_fixedCodim {A : Subgroup G} (hA : IsElementaryTwo A) :
    fixedCodim ρ A = 2 * (2 * m + 1) :=
  M.elementary_fixedCodim hm hA (h.suzuki_elementary_le_layer M hm hA)

/-- The original Sylow omega acts quadratically on V. -/
theorem suzuki_omega_quadratic (T : Sylow 2 G) :
    IsQuadratic ρ (omegaOneAmbient (T : Subgroup G)) := by
  let : L.Normal := h.layer_normal
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  rw [inf_eq_left.mpr (h.suzuki_sylow_le M hm T)] at hP
  rw [← hP]
  exact M.sylowImage_omega_quadratic hm P

/-- The common fixed space of the original Sylow omega has binary dimension 2r. -/
theorem suzuki_omega_fixed_finrank [FiniteDimensional (ZMod 2) V] (T : Sylow 2 G) :
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient (T : Subgroup G))) =
      2 * (2 * m + 1) := by
  have hc := h.suzuki_elementary_fixedCodim M hm (h.suzuki_omega_calculation M hm T).1
  have he := fixedCodim_add_finrank ρ (omegaOneAmbient (T : Subgroup G))
  rw [hc, M.finrank_eq] at he
  omega

omit h M hm [Finite G] in
private theorem elementary_le_omega {A : Subgroup G} (hA : IsElementaryTwo A)
    (T : Sylow 2 G) (hAT : A ≤ T) : A ≤ omegaOneAmbient (T : Subgroup G) := by
  let : IsElementaryAbelian 2 A := hA.2
  rw [← omegaOneAmbient_eq_self A]
  exact omegaOneAmbient_mono hAT

/-- All elementary two-actors have binary rank at most r. -/
theorem suzuki_elementary_rank_le {A : Subgroup G} (hA : IsElementaryTwo A) :
    rank A ≤ 2 * m + 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hc := card_le_of_le (elementary_le_omega hA T hAT)
  rw [hA.card_eq_two_pow_rank, (h.suzuki_omega_calculation M hm T).1.card_eq_two_pow_rank,
    (h.suzuki_omega_calculation M hm T).2] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc

/-- The lower ratio bound holds for all nontrivial elementary two-actors. -/
theorem suzuki_actionRatio_ge_two {A : Subgroup G} (hA : IsElementaryTwo A) :
    2 ≤ actionRatio ρ A := by
  have hr := h.suzuki_elementary_rank_le M hm hA
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (by simp))]
  rw [h.suzuki_elementary_fixedCodim M hm hA]
  exact_mod_cast Nat.mul_le_mul_left 2 hr

/-- The original Sylow omega attains the ratio two. -/
theorem suzuki_omega_ratio (T : Sylow 2 G) :
    actionRatio ρ (omegaOneAmbient (T : Subgroup G)) = 2 := by
  have hc := h.suzuki_omega_calculation M hm T
  apply le_antisymm
  · apply (actionRatio_le_nat_iff ρ hc.1 2).mpr
    rw [h.suzuki_elementary_fixedCodim M hm hc.1, hc.2]
  · exact h.suzuki_actionRatio_ge_two M hm hc.1

/-- Both the quadratic and cubic global ratios are exactly two. -/
theorem suzuki_ratios : quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 := by
  have hlow : 2 ≤ cubicRatio ρ := by
    apply le_iInf
    intro A
    apply le_iInf
    intro hA
    exact h.suzuki_actionRatio_ge_two M hm hA.1
  let T : Sylow 2 G := Classical.choice inferInstance
  have hupp : quadraticRatio ρ ≤ 2 := by
    apply iInf_le_of_le (omegaOneAmbient (T : Subgroup G))
    apply iInf_le_of_le ⟨(h.suzuki_omega_calculation M hm T).1, h.suzuki_omega_quadratic M hm T⟩
    exact (h.suzuki_omega_ratio M hm T).le
  have hc := cubicRatio_le_quadraticRatio ρ
  exact ⟨le_antisymm hupp (hlow.trans hc), le_antisymm (hc.trans hupp) hlow⟩

/-- Membership in the source Q(T,V) is exactly equality with the original Sylow omega. -/
theorem suzuki_threshold_iff (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) :
    (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
      A = omegaOneAmbient (T : Subgroup G) := by
  constructor
  · rintro ⟨hA, _, hratio⟩
    have hbound := (actionRatio_le_nat_iff ρ hA 2).mp hratio
    rw [h.suzuki_elementary_fixedCodim M hm hA] at hbound
    have hle := elementary_le_omega hA T hAT
    apply eq_of_le_of_card_ge hle
    rw [hA.card_eq_two_pow_rank, (h.suzuki_omega_calculation M hm T).1.card_eq_two_pow_rank,
      (h.suzuki_omega_calculation M hm T).2]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · rintro rfl
    exact ⟨(h.suzuki_omega_calculation M hm T).1, h.suzuki_omega_quadratic M hm T,
      (h.suzuki_omega_ratio M hm T).le⟩

/-- The literal threshold family in G is a singleton; no larger normalizer is introduced. -/
theorem suzuki_threshold_family (T : Sylow 2 G) :
    {A : Subgroup G | A ≤ T ∧ IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2} =
      {omegaOneAmbient (T : Subgroup G)} := by
  ext A
  constructor
  · rintro ⟨hAT, hA⟩
    exact (h.suzuki_threshold_iff M hm T hAT).mp hA
  · intro hA
    change A = omegaOneAmbient (T : Subgroup G) at hA
    subst A
    exact ⟨omegaOneAmbient_le _,
      (h.suzuki_threshold_iff M hm T (omegaOneAmbient_le _)).mpr rfl⟩

/-- Every involution acts freely: its displacement image is its fixed space. -/
theorem suzuki_involution_free [FiniteDimensional (ZMod 2) V]
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    LinearMap.range (ρ t - LinearMap.id) = LinearMap.ker (ρ t - LinearMap.id) := by
  have hA : IsElementaryTwo (zpowers t) :=
    ⟨fun hb => ht (mem_bot.mp (hb ▸ mem_zpowers t)),
      IsElementaryAbelian.zpowers_of_pow_eq_one ht2⟩
  have hker : LinearMap.ker (ρ t - LinearMap.id) = fixedSpace ρ (zpowers t) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  have hle : LinearMap.range (ρ t - LinearMap.id) ≤ LinearMap.ker (ρ t - LinearMap.id) := by
    rintro _ ⟨v, rfl⟩
    exact sub_eq_zero.mpr (involution_fixes_displacement ρ (by simpa [pow_two] using ht2) v)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← fixedCodim_zpowers_eq_displacement_rank, hker]
  have hc := h.suzuki_elementary_fixedCodim M hm hA
  have hd := fixedCodim_add_finrank ρ (zpowers t)
  rw [hc, M.finrank_eq] at hd
  omega

/-- The explicit fixed-vector formulation of freeness on the binary module. -/
theorem suzuki_fixedVector_is_displacement [FiniteDimensional (ZMod 2) V]
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (v : V) (hv : ρ t v = v) : ∃ w, ρ t w - w = v := by
  have hk : v ∈ LinearMap.ker (ρ t - LinearMap.id) := sub_eq_zero.mpr hv
  rw [← h.suzuki_involution_free M hm t ht ht2] at hk
  exact hk

end SourceHypotheses
end CFSG.Quasithin.ChapterK.RankOne
