module

public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Retaining the full primary part of a perfect central kernel

For a specified Sylow p-subgroup P of a finite perfect central kernel,
Schur--Zassenhaus gives a complement in that abelian kernel. Its image is
central in the covering group, and quotienting by it leaves a perfect
central cover of the same base with kernel isomorphic to P. In particular,
every p-power divisor is retained, not just divisibility by p.

This extends the two-divisibility reduction in the ternary symplectic cover
calculation. The application to the exclusion of eight for PSU₄(3) is in
`HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary`.
Source: the perfect-cover conventions and central transfer of
Aschbacher--Smith I.1.1--2, printed p.407 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace PerfectCentralCovering
universe u v
variable {E : Type u} {G : Type v} [Group E] [Finite E] [Group G]

/-- Quotienting by a central complement preserves precisely the chosen Sylow
subgroup of the kernel, with the original base and projection retained. -/
theorem Cover.exists_quotient_kernel_equiv_sylow (f : Cover E G)
    {p : ℕ} [Fact p.Prime] (P : Sylow p f.toMonoidHom.ker) :
    ∃ (N : Subgroup E) (_ : N.Normal) (hN : N ≤ f.toMonoidHom.ker),
      Nonempty (P ≃* (f.quotientKernelSubgroup N hN).toMonoidHom.ker) := by
  classical
  let K := f.toMonoidHom.ker
  let : CommGroup K := { (inferInstance : Group K) with
    mul_comm x y := Subtype.ext (mem_center_iff.mp (f.ker_le_center y.property) x) }
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  let N : Subgroup E := Q.map K.subtype
  have hN : N ≤ K := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hNc : N ≤ center E := hN.trans f.ker_le_center
  let hNn : N.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hNc hx) g, mul_inv_cancel_right]
    exact hx⟩
  let c := f.quotientKernelSubgroup N hN
  let q := QuotientGroup.mk' N
  let r : K →* c.toMonoidHom.ker := (q.comp K.subtype).codRestrict
    c.toMonoidHom.ker (fun x => x.property)
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N y.val
    have hxK : x ∈ K := by
      change c.toMonoidHom (q x) = 1
      rw [hx]
      exact y.property
    exact ⟨⟨x, hxK⟩, Subtype.ext hx⟩
  have hrk : r.ker = Q := by
    ext x
    change (⟨q x, _⟩ : c.toMonoidHom.ker) = 1 ↔ x ∈ Q
    rw [Subtype.ext_iff]
    change (x : E) ∈ q.ker ↔ x ∈ Q
    rw [QuotientGroup.ker_mk']
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (Subtype.ext hxy : y = x) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  let e : K ⧸ Q ≃* c.toMonoidHom.ker :=
    (QuotientGroup.quotientMulEquivOfEq hrk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)
  exact ⟨N, hNn, hN, ⟨hQ.QuotientMulEquiv.symm.trans e⟩⟩

/-- A p-power upper bound proved for p-group kernels applies to arbitrary
finite perfect central kernels, including kernels with other prime factors. -/
theorem Cover.not_primePower_dvd_kernel_of_primary_case (f : Cover E G)
    {p n : ℕ} [Fact p.Prime]
    (hcase : ∀ {D : Type u} [Group D] [Finite D] (g : Cover D G),
      IsPGroup p g.toMonoidHom.ker → ¬ p ^ n ∣ Nat.card g.toMonoidHom.ker) :
    ¬ p ^ n ∣ Nat.card f.toMonoidHom.ker := by
  let P : Sylow p f.toMonoidHom.ker := Classical.choice inferInstance
  obtain ⟨N, hNn, hN, ⟨e⟩⟩ := f.exists_quotient_kernel_equiv_sylow P
  let : N.Normal := hNn
  intro hd
  apply hcase (f.quotientKernelSubgroup N hN) (P.isPGroup'.of_equiv e)
  rw [← Nat.card_congr e.toEquiv]
  exact P.pow_dvd_card_of_pow_dvd_card hd

end PerfectCentralCovering
