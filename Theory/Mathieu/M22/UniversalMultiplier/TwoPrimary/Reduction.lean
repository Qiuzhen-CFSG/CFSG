module

public import Theory.Mathieu.M22.UniversalMultiplier.PrimaryBounds
public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting

/-!
# Removing odd torsion from M₂₂ covering kernels

Quotient a finite perfect central cover by the cubic Sylow subgroup of its
central kernel. The resulting kernel has order equal to that Sylow subgroup's
index. The established odd-primary exclusions make it a two-group. Coprimality
shows that this operation preserves divisibility by every power of two.
Consequently a bound of four for two-group kernels suffices for all kernels.

This is a reduction for Aschbacher–Smith I.1.3(4), printed p.407, using the
covering convention I.1.1. It makes no two-primary multiplier assertion.
-/

public section
namespace Sporadic.Mathieu.M22UniversalMultiplier
open PerfectCentralCovering Subgroup
universe u

/-- Remove the odd central part without changing divisibility by powers of two. -/
theorem exists_twoPrimary_quotient
    {E : Type u} [Group E] [Finite E] (f : Cover E M22) :
    ∃ (D : Subgroup E) (_ : D.Normal) (hD : D ≤ f.toMonoidHom.ker),
      IsPGroup 2 (f.quotientKernelSubgroup D hD).toMonoidHom.ker ∧
      ∀ n : ℕ, 2 ^ n ∣ Nat.card f.toMonoidHom.ker ↔
        2 ^ n ∣ Nat.card (f.quotientKernelSubgroup D hD).toMonoidHom.ker := by
  let P : Sylow 3 f.toMonoidHom.ker := Classical.choice inferInstance
  let D : Subgroup E := (P : Subgroup f.toMonoidHom.ker).map f.toMonoidHom.ker.subtype
  have hD : D ≤ f.toMonoidHom.ker := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hDc : D ≤ center E := hD.trans f.ker_le_center
  let hDn : D.Normal := ⟨fun x hx y => by
    rw [mem_center_iff.mp (hDc hx) y, mul_inv_cancel_right]
    exact hx⟩
  have hcardD : Nat.card D = Nat.card P :=
    card_map_of_injective f.toMonoidHom.ker.subtype_injective
  let g := f.quotientKernelSubgroup D hD
  have hc : Nat.card f.toMonoidHom.ker = Nat.card P * Nat.card g.toMonoidHom.ker := by
    rw [f.card_kernel_quotientKernelSubgroup D hD, hcardD]
  have hgcard : Nat.card g.toMonoidHom.ker = (P : Subgroup f.toMonoidHom.ker).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := P))
    rw [← hc, card_mul_index]
  have hg3 : ¬ 3 ∣ Nat.card g.toMonoidHom.ker := by
    rw [hgcard]
    exact P.not_dvd_index
  have hg2 : IsPGroup 2 g.toMonoidHom.ker := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : (2 : ℕ) ≠ 0)).mpr
    intro p hp
    obtain ⟨hpprime, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have heq : p = 2 := by
      by_contra hp2
      by_cases hp3 : p = 3
      · exact hg3 (hp3 ▸ hpd)
      · exact not_dvd_kernel_of_ne_two_three g hpprime hp2 hp3 hpd
    subst p
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩
  refine ⟨D, hDn, hD, hg2, ?_⟩
  intro n
  rw [hc]
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hcop : (2 ^ n).Coprime (Nat.card P) := by
    rw [hk]
    exact (by decide : Nat.Coprime 2 3).pow n k
  exact hcop.dvd_mul_left

/-- It suffices to bound kernels which are already two-groups. -/
theorem not_eight_dvd_kernel_of_twoPrimary_bound
    (hbound : ∀ (Q : Type u) [Group Q] [Finite Q] (g : Cover Q M22),
      IsPGroup 2 g.toMonoidHom.ker → Nat.card g.toMonoidHom.ker ≤ 4)
    {E : Type u} [Group E] [Finite E] (f : Cover E M22) :
    ¬ 8 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨D, hDn, hD, hp, hd⟩ := exists_twoPrimary_quotient f
  let : D.Normal := hDn
  intro h8
  have h8' : 8 ∣ Nat.card (f.quotientKernelSubgroup D hD).toMonoidHom.ker :=
    (hd 3).mp h8
  have hle := hbound (E ⧸ D) (f.quotientKernelSubgroup D hD) hp
  have hge := Nat.le_of_dvd (Nat.card_pos (α :=
    (f.quotientKernelSubgroup D hD).toMonoidHom.ker)) h8'
  omega
end Sporadic.Mathieu.M22UniversalMultiplier
