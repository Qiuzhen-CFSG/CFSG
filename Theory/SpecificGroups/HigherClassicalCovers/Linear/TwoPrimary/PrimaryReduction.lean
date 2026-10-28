module

public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting

/-!
# Removing one primary part of a perfect central kernel

The image in E of a Sylow p-subgroup of the central kernel of E → G is
normal in E. The induced cover has kernel order equal to the Sylow index,
hence prime to p. Every other primary part of the original kernel divides
this new kernel order. Thus bounds for covers with prime-to-p kernel bound
the other primary parts without excluding p-torsion in the original cover.

This elementary reduction is used in the degree-four linear application of
Steinberg's Theorem 11, §7, printed pp.86–88, and Aschbacher–Smith I.1.4.
-/

public section
namespace PerfectCentralCovering
open Subgroup
universe u v
variable {E : Type u} {G : Type v} [Group E] [Finite E] [Group G] [Finite G]

/-- A central quotient removes the p-part and preserves divisibility by
every other primary part of the original, literal kernel. -/
theorem Cover.exists_coprime_kernel_quotient (c : Cover E G) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hrp : r ≠ p) (P : Sylow r c.toMonoidHom.ker) :
    ∃ (D : Subgroup E) (_hDn : D.Normal) (hD : D ≤ c.toMonoidHom.ker),
      (Nat.card (c.quotientKernelSubgroup D hD).toMonoidHom.ker).Coprime p ∧
      Nat.card P ∣ Nat.card (c.quotientKernelSubgroup D hD).toMonoidHom.ker := by
  classical
  let Q : Sylow p c.toMonoidHom.ker := default
  let D : Subgroup E := (Q : Subgroup c.toMonoidHom.ker).map c.toMonoidHom.ker.subtype
  have hD : D ≤ c.toMonoidHom.ker := map_subtype_le _
  have hDc : D ≤ center E := hD.trans c.ker_le_center
  let hDn : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hDc hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hcard : Nat.card D = Nat.card Q :=
    card_map_of_injective c.toMonoidHom.ker.subtype_injective
  have he := c.card_kernel_quotientKernelSubgroup D hD
  have hindex : Nat.card (c.quotientKernelSubgroup D hD).toMonoidHom.ker =
      (Q : Subgroup c.toMonoidHom.ker).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q))
    rw [← hcard, ← he, hcard]
    exact Q.card_mul_index.symm
  refine ⟨D, hDn, hD, ?_, ?_⟩
  · rw [hindex]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr Q.not_dvd_index).symm
  · have hcop : (Nat.card P).Coprime (Nat.card D) := by
      rw [hcard]
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp P.isPGroup'
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp Q.isPGroup'
      rw [ha, hb]
      exact ((Nat.coprime_primes Fact.out Fact.out).mpr hrp).pow a b
    apply hcop.dvd_of_dvd_mul_left
    rw [← he]
    exact (P : Subgroup c.toMonoidHom.ker).card_subgroup_dvd_card

/-- A uniform prime-to-p kernel bound controls the r-Sylow subgroup of
any perfect central kernel, for r distinct from p. -/
theorem Cover.sylow_card_le_of_coprime_kernel_bound (c : Cover E G) {p r b : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hrp : r ≠ p)
    (hb : ∀ (H : Type u) [Group H] [Finite H] (d : Cover H G),
      (Nat.card d.toMonoidHom.ker).Coprime p → Nat.card d.toMonoidHom.ker ≤ b)
    (P : Sylow r c.toMonoidHom.ker) : Nat.card P ≤ b := by
  obtain ⟨D, hDn, hD, hcop, hdvd⟩ := c.exists_coprime_kernel_quotient hrp P
  let : D.Normal := hDn
  exact (Nat.le_of_dvd Nat.card_pos hdvd).trans
    (hb (E ⧸ D) (c.quotientKernelSubgroup D hD) hcop)

end PerfectCentralCovering
