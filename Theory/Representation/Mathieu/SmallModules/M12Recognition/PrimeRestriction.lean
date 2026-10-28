module

public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.SubrepresentationLattice

/-!
# Order-eleven irreducibility in binary degree ten

An order-eleven actor moves at least ten dimensions. At degree at most ten
its fixed space therefore vanishes. On any nonzero invariant subspace its
prime-order subgroup acts faithfully, so that subspace already has dimension
ten. This proves irreducibility, also after restricting to any subgroup
whose order is divisible by eleven.

The application is the actual M₁₁ point restriction in the recognition of
the small M₁₂ module. It supplies the irreducibility premise of the smaller
module-classification problem; it does not identify that module.

Source: Aschbacher--Smith, G.7.1(1) and the James input in G.7.3(2),
combined manuscript (1 March 2004), printed pp.347--348.
-/

public section

namespace Representation.MathieuSmall.M12Recognition
open Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- An order-eleven subgroup has no fixed vectors in a faithful binary module
of dimension at most ten. -/
theorem eleven_fixedSpace_eq_bot (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10)
    (x : G) (hx : orderOf x = 11) : fixedSpace ρ (Subgroup.zpowers x) = ⊥ := by
  have hlo := ten_le_fixedCodim_of_order_eleven ρ hf x hx
  have heq := fixedCodim_add_finrank ρ (Subgroup.zpowers x)
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- A faithful binary module of dimension at most ten is irreducible as soon
as the group order is divisible by eleven. In particular this applies to
restrictions to subgroups containing an element of order eleven. -/
theorem irreducible_of_eleven_dvd (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10)
    (hdiv : 11 ∣ Nat.card G) : ρ.IsIrreducible := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 11 hdiv
  let P := Subgroup.zpowers x
  have hcard : Nat.card P = 11 := (Nat.card_zpowers x).trans hx
  let : IsSimpleGroup P := isSimpleGroup_of_prime_card hcard
  have hz : fixedSpace ρ P = ⊥ := eleven_fixedSpace_eq_bot ρ hf hd x hx
  have hlo : 10 ≤ Module.finrank (ZMod 2) V := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_eleven] using
      BinaryPrimeDegree.orderOf_le_finrank ρ hf (by decide : Nat.Prime 11)
        (by decide) hdiv
  let : Nontrivial V := Module.nontrivial_of_finrank_pos
    (by omega : 0 < Module.finrank (ZMod 2) V)
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hfaith : Function.Injective (N.toRepresentation.comp P.subtype) := by
    rcases (N.toRepresentation.comp P.subtype).normal_ker.eq_bot_or_eq_top with hk | hk
    · exact (N.toRepresentation.comp P.subtype).ker_eq_bot_iff.mp hk
    · have he : N.toRepresentation.comp P.subtype = 1 := MonoidHom.ker_eq_top_iff.mp hk
      have hle : N.toSubmodule ≤ fixedSpace ρ P := by
        intro v hv g
        have h := DFunLike.congr_fun (congrArg (fun σ => σ g) he) ⟨v, hv⟩
        exact congrArg Subtype.val h
      rw [hz] at hle
      exact (hN (Subrepresentation.toSubmodule_injective (le_bot_iff.mp hle))).elim
  have hloN := BinaryPrimeDegree.orderOf_le_finrank (N.toRepresentation.comp P.subtype)
    hfaith (by decide : Nat.Prime 11) (by decide) (by rw [hcard])
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hloN
  apply Subrepresentation.toSubmodule_injective
  by_contra hnt
  have hlt := Submodule.finrank_lt hnt
  omega

end Representation.MathieuSmall.M12Recognition
