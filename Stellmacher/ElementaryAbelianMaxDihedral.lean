module

public import Stellmacher.ElementaryAbelianMaxProduct
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct
public import Theory.Frattini.DihedralOmega
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Maximum elementary families in dihedral two-groups

The cyclic subgroup of index two bounds elementary subgroups by order four.
Joining each reflection to the central half-turn gives a four-group attaining
that bound. Since reflections generate the dihedral group, its maximum
four-groups generate the whole group. The ambient transport uses the supplied
multiplicative equivalence and preserves subgroup inclusions.

Source: the dihedral calculation in Aschbacher--Smith, 16.3.12, printed
p.1182 / PDF p.1199 of the combined manuscript of 1 March 2004.
-/

public section

open Subgroup
namespace Stellmacher

private theorem dihedral_reflection_four {n : ℕ} (hn : 2 ≤ n) (i : ZMod (2 ^ n)) :
    ∃ E : Subgroup (DihedralGroup (2 ^ n)),
      IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ DihedralGroup.sr i ∈ E := by
  let z : DihedralGroup (2 ^ n) := DihedralGroup.r (2 ^ (n - 1) : ℕ)
  have hz : orderOf z = 2 := by
    have hs : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have h := orderOf_pow_orderOf_div
      (x := (DihedralGroup.r 1 : DihedralGroup (2 ^ n)))
      (by rw [DihedralGroup.orderOf_r_one]; positivity)
      (show 2 ∣ orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ n)) by
        rw [DihedralGroup.orderOf_r_one, hs]; exact dvd_mul_left _ _)
    simpa [DihedralGroup.orderOf_r_one, hs, DihedralGroup.r_one_pow, z] using h
  have hzc : z ∈ center (DihedralGroup (2 ^ n)) := by
    rw [DihedralFrattini.center_eq_half hn]
    exact mem_zpowers _
  let : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa only [hz] using pow_orderOf_eq_one z)
  have hout : DihedralGroup.sr i ∉ zpowers z := by
    rintro ⟨k, hk⟩
    simp only [z, DihedralGroup.r_zpow] at hk
    cases hk
  have hc : zpowers (DihedralGroup.sr i) ≤ centralizer (zpowers z : Set _) := by
    apply zpowers_le.mpr
    rintro x ⟨k, rfl⟩
    exact (show Commute z (DihedralGroup.sr i) from (mem_center_iff.mp hzc _).symm).zpow_left k
  let : IsElementaryAbelian 2 (zpowers (DihedralGroup.sr i)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by simp [pow_two])
  refine ⟨zpowers z ⊔ zpowers (DihedralGroup.sr i),
    IsElementaryAbelian.sup_of_le_centralizer hc, ?_, mem_sup_right (mem_zpowers _)⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hc.trans (Subgroup.centralizer_le_normalizer _))
    (disjoint_zpowers_of_prime_order_not_mem _ _ (DihedralGroup.orderOf_sr i) hout),
    Nat.card_zpowers, Nat.card_zpowers, hz, DihedralGroup.orderOf_sr]

/-- Maximum elementary subgroups of a dihedral two-group have order four. -/
theorem dihedral_maxFamily_iff_card_four {n : ℕ} (hn : 2 ≤ n)
    (E : Subgroup (DihedralGroup (2 ^ n))) :
    E ∈ elementaryAbelianMaxSubgroups ⊤ ↔ IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  constructor
  · intro hE
    obtain ⟨F, hF, hc, _⟩ := dihedral_reflection_four hn 0
    have hlo := hE.2.2 F le_top hF
    let := hE.2.1
    have hhi := DihedralGroup.card_le_four_of_square_eq_one E
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E))
    exact ⟨hE.2.1, by omega⟩
  · rintro ⟨hE, hc⟩
    refine ⟨le_top, hE, ?_⟩
    intro F _ hF
    rw [hc]
    let := hF
    exact DihedralGroup.card_le_four_of_square_eq_one F
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 F))

/-- The maximum elementary four-groups generate a dihedral two-group. -/
theorem dihedral_maxJ_top {n : ℕ} (hn : 2 ≤ n) :
    elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup (2 ^ n))) = ⊤ := by
  apply top_unique
  have href (i : ZMod (2 ^ n)) : DihedralGroup.sr i ∈
      elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup (2 ^ n))) := by
    obtain ⟨E, hE, hc, hi⟩ := dihedral_reflection_four hn i
    exact (le_sSup ((dihedral_maxFamily_iff_card_four hn E).mpr ⟨hE, hc⟩)) hi
  rintro (i | i) _
  · have h := (elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup (2 ^ n)))).mul_mem
      (href 0) (href i)
    simpa only [DihedralGroup.sr_mul_sr, sub_zero] using h
  · exact href i

variable {G : Type*} [Group G]

/-- Ambient transport of maximum elementary generation in a dihedral two-group. -/
theorem dihedral_maxJ (R : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : R ≃* DihedralGroup (2 ^ n)) : elementaryAbelianMaxJ R = R := by
  let f := R.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := R.subtype_injective.comp e.symm.injective
  have hr : (⊤ : Subgroup (DihedralGroup (2 ^ n))).map f = R := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact (e.symm a).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, mem_top _, congrArg Subtype.val (e.symm_apply_apply _)⟩
  calc elementaryAbelianMaxJ R =
      (elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup (2 ^ n)))).map f := by
        rw [← elementaryAbelianMaxJ_map_injective f hf, hr]
    _ = R := by rw [dihedral_maxJ_top hn, hr]

/-- The maximum family of an ambient dihedral two-group consists of its fours. -/
theorem dihedral_maxFamily_iff (R : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : R ≃* DihedralGroup (2 ^ n)) (E : Subgroup G) :
    E ∈ elementaryAbelianMaxSubgroups R ↔
      E ≤ R ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  let f := R.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := R.subtype_injective.comp e.symm.injective
  constructor
  · intro hE
    obtain ⟨F, hF, hEF⟩ := (maxFamily_equiv_iff R e.symm E).mp hE
    refine ⟨hE.1, hE.2.1, ?_⟩
    rw [hEF, card_map_of_injective hf]
    exact ((dihedral_maxFamily_iff_card_four hn F).mp hF).2
  · rintro ⟨hER, hE, hc⟩
    refine ⟨hER, hE, ?_⟩
    intro F hFR hF
    let F' := (F.subgroupOf R).map e.toMonoidHom
    have helem : IsElementaryAbelian 2 F' := (hF.subgroupOf hFR).map _
    have hcard : Nat.card F' = Nat.card F := by
      rw [card_map_of_injective e.injective]
      exact Nat.card_congr (subgroupOfEquivOfLe hFR).toEquiv
    let := helem
    have hbound := DihedralGroup.card_le_four_of_square_eq_one F'
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 F'))
    omega
end Stellmacher
