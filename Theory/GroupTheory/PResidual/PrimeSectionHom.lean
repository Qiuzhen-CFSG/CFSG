module
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Homomorphisms from a perfect prime section

A p-perfect finite group with core quotient of prime order q is generated
by its p-core and one element of order q. In a target of order prime to q,
that element dies, so the whole image is a p-group and hence trivial.

Source application: Aschbacher--Smith 15.2.4, printed p.1106, the action
of the marked-five residual on an A₅ Sylow subgroup.
-/

public section
open Subgroup
namespace Subgroup
variable {E D : Type*} [Group E] [Finite E] [Group D]
theorem hom_eq_one_of_prime_core_quotient {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h : IsPPerfect p E) (hcop : p.Coprime q)
    (hc : Nat.card (E ⧸ pCore p E) = q) (hn : ¬ q ∣ Nat.card D)
    (f : E →* D) : f = 1 := by
  obtain ⟨x,hx,hgen⟩ := exists_prime_order_sup_pCore_eq_top hcop hc
  have hfx : f x = 1 := by
    have hd : orderOf (f x) ∣ q := hx ▸ orderOf_map_dvd f x
    have he : orderOf (f x) = 1 ∨ orderOf (f x) = q := (Nat.dvd_prime (Fact.out : q.Prime)).mp hd
    apply orderOf_eq_one_iff.mp
    rcases he with he | he
    · exact he
    · exact False.elim (hn (he ▸ _root_.orderOf_dvd_natCard (f x)))
  have hm : f.range = (pCore p E).map f := by
    have hh := congrArg (map f) hgen
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hfx,zpowers_one_eq_bot,bot_sup_eq,
      ←MonoidHom.range_eq_map] using hh.symm
  have hp : IsPGroup p f.range := hm ▸ (pCore_isPGroup (p := p) (G := E)).map f
  have hf := h.hom_eq_one_of_isPGroup hp f.rangeRestrict
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun hf x)

end Subgroup
