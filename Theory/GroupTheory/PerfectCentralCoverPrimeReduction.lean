module

public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting
public import Theory.GroupTheory.NilpotentNoPrimeIndex

/-!
# Detecting central covering kernels in quotients of prime degree

If a prime p divides the kernel of a finite perfect central cover E → G,
the abelian kernel has a subgroup of index p. This subgroup is central in E,
so quotienting E by it gives another perfect central cover of the same G,
now with kernel of order exactly p. The original projection factors through
this quotient by `Cover.quotientKernelSubgroup_comp`.

Consequently a local section over a subgroup of index prime to p need only
be constructed for covers of degree p. Transfer then excludes p from the
kernel of every finite perfect central cover. The actual Ree application is
`Theory.SpecificGroups.ReeF4.CentralCovers.PrimaryReduction`.

Source: the covering and central-transfer conventions of Aschbacher–Smith,
I.1.1–2, printed p.407 of `refs/quasithin.pdf`. This is a general reduction;
it does not supply any of the family-specific multiplier calculations in
GLS3, Section 6.1.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace PerfectCentralCovering

universe u v
variable {E : Type u} {G : Type v} [Group E] [Finite E] [Group G] [Finite G]

/-- Every prime divisor of a finite central covering kernel survives in a
central quotient cover with kernel of precisely that prime order. -/
theorem Cover.exists_prime_kernel_quotient (c : Cover E G) {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card c.toMonoidHom.ker) :
    ∃ (D : Subgroup E) (_hDn : D.Normal) (hD : D ≤ c.toMonoidHom.ker),
      Nat.card (c.quotientKernelSubgroup D hD).toMonoidHom.ker = p := by
  classical
  let : IsMulCommutative c.toMonoidHom.ker := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (c.ker_le_center x.property) y).symm⟩⟩
  have hex : ∃ N : Subgroup c.toMonoidHom.ker, N.Normal ∧ N.index = p := by
    by_contra h
    apply Group.not_dvd_card_of_nilpotent_of_no_normal_index_prime ?_ hp
    intro N hN hindex
    exact h ⟨N, hN, hindex⟩
  obtain ⟨N, _, hNindex⟩ := hex
  let D : Subgroup E := N.map c.toMonoidHom.ker.subtype
  have hD : D ≤ c.toMonoidHom.ker := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hDc : D ≤ center E := hD.trans c.ker_le_center
  let hDn : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hDc hx) g, mul_inv_cancel_right]
    exact hx⟩
  refine ⟨D, hDn, hD, ?_⟩
  have hcard : Nat.card c.toMonoidHom.ker = Nat.card D * p := by
    rw [show Nat.card D = Nat.card N from
      Subgroup.card_map_of_injective c.toMonoidHom.ker.subtype_injective]
    simpa only [hNindex] using N.card_mul_index.symm
  have he := c.card_kernel_quotientKernelSubgroup D hD
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D)) (he.symm.trans hcard)

/-- Excluding covers of prime degree excludes that prime from every finite
perfect central kernel, without a bound on its exponent or rank. -/
theorem Cover.not_dvd_card_kernel_of_no_prime_kernel (c : Cover E G)
    {p : ℕ} [Fact p.Prime]
    (hno : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F G),
      Nat.card d.toMonoidHom.ker ≠ p) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  intro hp
  obtain ⟨D, hDn, hD, hc⟩ := c.exists_prime_kernel_quotient hp
  let : D.Normal := hDn
  exact hno (E ⧸ D) (c.quotientKernelSubgroup D hD) hc

/-- It suffices to split prime-degree covers on one subgroup of index prime
to p. The local subgroup can depend on the quotient cover. -/
theorem Cover.not_dvd_card_kernel_of_prime_kernel_local_sections (c : Cover E G)
    {p : ℕ} [Fact p.Prime]
    (hsections : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F G),
      Nat.card d.toMonoidHom.ker = p →
        ∃ (P : Subgroup G) (s : P →* F),
          ¬ p ∣ P.index ∧ d.toMonoidHom.comp s = P.subtype) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  apply c.not_dvd_card_kernel_of_no_prime_kernel
  intro F _ _ d hd
  obtain ⟨P, s, hi, hs⟩ := hsections F d hd
  exact not_dvd_card_kernel_of_section d P hi s hs (hd ▸ dvd_rfl)

end PerfectCentralCovering
