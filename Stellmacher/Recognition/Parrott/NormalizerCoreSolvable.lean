module

public import Stellmacher.Recognition.Parrott.NormalizerCoreOrder

/-!
# The second normalizer core from local solvability

Solvability of N_G(F) alone gives the faithful elementary-five-dimensional
image its two-core bound. The original orbit of z in the center of this core
then has three points, forcing order 6144, core order 1024 and quotient S₃.
No hypothesis on other two-locals of the ambient group is needed.

The original quasithin source supplies this local solvability. Strict Sylow
containment is the independent second-normalizer growth step.
Source: Parrott (1972), Lemma 6, printed p.677.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The linear-group bound transfers through the supplied action kernel F.
Only the relevant cardinal conclusions of `normalizer_card` are needed. -/
public theorem normalizer_core_card_ge_of_action_card_of_solvable
    (d : ParrottSecondElementaryData z) (hsolv : Group.IsSolvable (normalizer (d.F : Set G)))
    {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 31)
    (himage : Nat.card d.F.normalizerMonoidHom.range = 64 * n) :
    512 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G))) := by
  let : IsElementaryAbelian 2 d.F := d.elementary
  let : Group.IsSolvable (normalizer (d.F : Set G)) := hsolv
  let : Group.IsSolvable d.F.normalizerMonoidHom.range :=
    Group.isSolvable_of_surjective d.F.normalizerMonoidHom.rangeRestrict_surjective
  have hbound := sixteen_le_card_two_core_of_solvable_elementary_thirtytwo_automorphisms
    d.card d.F.normalizerMonoidHom.range hnpos hnle himage
  rw [d.normalizer_core_card_eq]
  omega

/-- For any integer supplied by `normalizer_card`, the requested normalizer
core alternative holds; solvability always gives its first branch. -/
public theorem normalizer_core_lower_bound_of_solvable
    (d : ParrottSecondElementaryData z) (hsolv : Group.IsSolvable (normalizer (d.F : Set G)))
    {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 31)
    (himage : Nat.card d.F.normalizerMonoidHom.range = 64 * n) :
    (512 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G)))) ∨
      (n = 21 ∧ 256 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G)))) := by
  exact Or.inl (d.normalizer_core_card_ge_of_action_card_of_solvable hsolv hnpos hnle himage)

/-- Under the original hypotheses, the actual normalizer two-core has order
at least 512, retaining the supplied second elementary subgroup. -/
public theorem normalizer_core_card_ge_of_solvable
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hsolv : Group.IsSolvable (normalizer (d.F : Set G))) :
    512 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G))) := by
  obtain ⟨n, _, hnpos, hnle, _, himage⟩ := d.normalizer_card h
  exact d.normalizer_core_card_ge_of_action_card_of_solvable hsolv hnpos hnle himage

/-- The order and quotient conclusions of Lemma 6 for the actual supplied F.
Local solvability and the centralizer hypotheses suffice once T<N is known. -/
public theorem normalizer_core_order_of_solvable (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hsolv : Group.IsSolvable (normalizer (d.F : Set G)))
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    Nat.card N = 6144 ∧ Nat.card K = 1024 ∧
      Nonempty ((N ⧸ K) ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (center K) = 4 := by
  classical
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let T := d.sylow.subtype d.sylow_le_normalizer
  let Z := (center K).map K.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  let zN : N := ⟨z, d.sylow_le_normalizer (d.le_sylow d.z_mem_inf.2)⟩
  have hzZ : zN ∈ Z := by
    obtain ⟨k, hk, heq⟩ := d.z_mem_normalizer_core_center
    exact ⟨k, hk, N.subtype_injective heq⟩
  have hz1 : zN ≠ 1 := by
    intro heq
    have hz : z = 1 := congrArg N.subtype heq
    have ho := h.involution
    simp [hz] at ho
  have hcentral : centralizer ({zN} : Set N) = (T : Subgroup N) := by
    ext x
    rw [mem_centralizer_singleton_iff]
    change x * zN = zN * x ↔ (x : G) ∈ (d.sylow : Subgroup G)
    rw [Subtype.ext_iff]
    change (x : G) * z = z * (x : G) ↔ _
    rw [← mem_centralizer_singleton_iff, ← d.normalizer_inf_centralizer h]
    exact (and_iff_right x.property).symm
  have hTcard : Nat.card (T : Subgroup N) = 2048 := by
    change Nat.card ((d.sylow : Subgroup G).subgroupOf N) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe d.sylow_le_normalizer).toEquiv]
    exact d.sylow_card h
  obtain ⟨n, hnodd, _, _, hNcard, _⟩ := d.normalizer_card h
  have hindex : (T : Subgroup N).index = n := by
    have hc := (T : Subgroup N).index_mul_card
    rw [hTcard, hNcard] at hc
    omega
  have hn : 1 < n := by
    have hlt : Nat.card (d.sylow : Subgroup G) < Nat.card N := by
      apply lt_of_not_ge
      intro hc
      exact hproper.ne (eq_of_le_of_card_ge hproper.le hc)
    rw [d.sylow_card h, hNcard] at hlt
    omega
  have horbit : n < Nat.card (center K) := by
    have hh := centralizer_index_lt_card_normal Z zN hzZ hz1
    rwa [hcentral, hindex, card_map_of_injective K.subtype_injective] at hh
  have hcenterBound := d.normalizer_core_center_card_le_four h (d.normalizer_core_card_ge_of_solvable h hsolv)
  have hn3 : n = 3 := by
    obtain ⟨r, hr⟩ := hnodd
    change Nat.card (center K) ≤ 4 at hcenterBound
    omega
  have hcenter : Nat.card (center K) = 4 := by
    change Nat.card (center K) ≤ 4 at hcenterBound
    omega
  have hN6144 : Nat.card N = 6144 := by rw [hNcard, hn3]
  have hKT : K < (T : Subgroup N) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal T) ?_
    intro heq
    have hc : Nat.card (center (T : Subgroup N)) = 2 := by
      change Nat.card (center ((d.sylow : Subgroup G).subgroupOf N)) = _
      rw [Nat.card_congr (Subgroup.centerCongr
        (subgroupOfEquivOfLe d.sylow_le_normalizer)).toEquiv]
      exact d.sylow_center_card h
    have hcc := Nat.card_congr (Subgroup.centerCongr
      (MulEquiv.subgroupCongr heq)).toEquiv
    exact (by decide : (4 : ℕ) ≠ 2) (hcenter.symm.trans (hcc.trans hc))
  obtain ⟨e⟩ := sylow_index_three_core_quotient T (hindex.trans hn3) hKT
  have hquot : Nat.card (N ⧸ K) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hK1024 : Nat.card K = 1024 := by
    have hc := K.index_mul_card
    change Nat.card (N ⧸ K) * Nat.card K = Nat.card N at hc
    rw [hquot, hN6144] at hc
    omega
  exact ⟨hN6144, hK1024, ⟨e⟩, hcenter⟩


end Stellmacher.Recognition.ParrottSecondElementaryData
