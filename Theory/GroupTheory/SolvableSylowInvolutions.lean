module

public import Theory.GroupTheory.Fitting.Core
public import Mathlib.GroupTheory.Sylow

/-!
# Central involutions in solvable groups with vanishing odd cores

Suppose a finite solvable group has trivial odd prime cores and its Sylow
two-subgroup has at most one involution commuting with all its Sylow
conjugates. Then every central involution of that Sylow subgroup is central
in the whole group.

The Fitting subgroup is the nontrivial two-core. Its center is an abelian
normal subgroup and contains an involution. Every such involution commutes
with all its Sylow conjugates, so uniqueness identifies it with the given
involution. Normality then makes that involution fixed by the whole group.

This argument supplies the local exclusion used for PSL₃(3) in
Aschbacher–Smith 2.3.9(7)(d), printed pp.525–526; the theorem itself is an
intrinsic solvable-group statement.
-/

@[expose] public section

open Subgroup

namespace Theory.GroupTheory

/-- A central Sylow involution is central in the solvable group when all
odd prime cores vanish and involutions commuting with their Sylow conjugates
are unique. -/
theorem central_of_sylow_involution_uniqueness
    {K : Type*} [Group K] [Finite K] [Group.IsSolvable K]
    (R : Sylow 2 K)
    (hunique : ∀ x y : R, orderOf x = 2 → orderOf y = 2 →
      (∀ s : R, Commute x (s * x * s⁻¹)) →
      (∀ s : R, Commute y (s * y * s⁻¹)) → x = y)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → pCore p K = ⊥)
    (t : R) (ht : orderOf t = 2) (htc : t ∈ center R) :
    (t : K) ∈ center K := by
  have hfit : fittingSubgroup K = pCore 2 K := by
    apply le_antisymm _ (pCore_le_fitting K 2)
    rw [fitting_eq_sup_pCore]
    apply iSup_le
    intro p
    by_cases hp : p.1.1 = 2
    · rw [hp]
    · rw [hodd p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) hp]
      exact bot_le
  have hQne : pCore 2 K ≠ ⊥ := by
    intro hQ
    have hcard := (fitting_eq_bot_iff_card_eq_one_of_solvable K).mp (hfit.trans hQ)
    have horder : orderOf (t : K) = 2 := (Subgroup.orderOf_coe t).trans ht
    have hdvd := orderOf_dvd_natCard (t : K)
    rw [horder, hcard] at hdvd
    norm_num at hdvd
  let Q := pCore 2 K
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  let : Nontrivial (center Q) := (pCore_isPGroup (p := 2) (G := K)).center_nontrivial
  let Z := (center Q).map Q.subtype
  have hZQ : Z ≤ Q := map_subtype_le _
  have hQR : Q ≤ R := pCore_isPGroup.le_sylow_of_normal R
  have hZnormal : Z.Normal := inferInstance
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, Commute x y := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, _, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx y).symm
  have huniqueZ (x : K) (hx : x ∈ Z) (hx2 : orderOf x = 2) : x = t := by
    let xr : R := ⟨x, hQR (hZQ hx)⟩
    have hxord : orderOf xr = 2 := (Subgroup.orderOf_coe xr).symm.trans hx2
    have hxcomm : ∀ s : R, Commute xr (s * xr * s⁻¹) := by
      intro s
      exact Subtype.ext (hZcomm x hx _ (hZnormal.conj_mem x hx s)).eq
    have htcomm : ∀ s : R, Commute t (s * t * s⁻¹) := by
      intro s
      exact (mem_center_iff.mp htc _).symm
    exact congrArg Subtype.val (hunique xr t hxord ht hxcomm htcomm)
  have hdvd : 2 ∣ Nat.card (center Q) :=
    ((pCore_isPGroup (p := 2) (G := K)).to_subgroup (center Q)).card_eq_or_dvd.resolve_left
      (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2 hdvd
  have huZ : ((u : Q) : K) ∈ Z := mem_map_of_mem Q.subtype u.property
  have hu2 : orderOf ((u : Q) : K) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]
  have htZ : (t : K) ∈ Z := huniqueZ _ huZ hu2 ▸ huZ
  apply mem_center_iff.mpr
  intro k
  have hord : orderOf (k * (t : K) * k⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ht]
  have he := huniqueZ _ (hZnormal.conj_mem _ htZ k) hord
  exact mul_inv_eq_iff_eq_mul.mp he

end Theory.GroupTheory

end
