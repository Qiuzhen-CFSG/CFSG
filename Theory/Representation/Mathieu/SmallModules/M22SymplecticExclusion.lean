module
public import Theory.Representation.OddSymplecticFixed
public import Theory.Representation.Mathieu.SmallModules.M22Recognition

/-!
# No small irreducible symplectic M₂₂ module

The native Todd module and its dual both have a one-dimensional fixed space
for a subgroup of order seven. Odd-order averaging forbids this for a
nondegenerate alternating form. James recognition extends the obstruction
to every faithful irreducible binary module of dimension at most twelve.

Source: Aschbacher–Smith G.7.3(2) and G.11.7, printed pp.348,367–368;
the native fixed-space calculation is H.13.1–2, pp.395–396.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
noncomputable section
namespace Representation.MathieuSmall
open Sporadic.Mathieu MathieuCode
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V]
/-- Neither native ten-dimensional M₂₂ module preserves a nondegenerate
alternating form, with the literal group marking retained. -/
theorem IsM22ToddOrDual.not_alternating (ρ : Representation (ZMod 2) D V)
    (h : IsM22ToddOrDual ρ)
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w) : False := by
  obtain ⟨e,hE⟩ := h
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,ha7⟩ := exists_prime_orderOf_dvd_card' (G := M22) 7
    (by rw [m22_order]; norm_num)
  let A : Subgroup D := zpowers (e.symm a)
  have hc : Nat.card A = 7 :=
    (Nat.card_zpowers (e.symm a)).trans ((e.symm.orderOf_eq a).trans ha7)
  have hmap : A.map e.toMonoidHom = zpowers a := by
    change (zpowers (e.symm a)).map e.toMonoidHom = zpowers a
    simp only [MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,e.apply_symm_apply]
  apply OddSymplecticFixed.fixed_finrank_ne_one ρ B ha hn hp A (hc ▸ (by decide))
  rcases hE with hE | hE
  all_goals obtain ⟨E⟩ := hE
  · have he := fixedSpace_map_equivariant ρ m22CocodeRepresentation e.toMonoidHom
      E.toLinearEquiv (fun g w => LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' g) w) A
    have hh := E.toLinearEquiv.finrank_map_eq (fixedSpace ρ A)
    rw [he,hmap,m22_cocode_fixed_finrank_seven _ ((Nat.card_zpowers a).trans ha7)] at hh
    exact hh.symm
  · have he := fixedSpace_map_equivariant ρ m22CodeRepresentation e.toMonoidHom
      E.toLinearEquiv (fun g w => LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' g) w) A
    have hh := E.toLinearEquiv.finrank_map_eq (fixedSpace ρ A)
    rw [he,hmap,m22_code_fixed_finrank_seven _ ((Nat.card_zpowers a).trans ha7)] at hh
    exact hh.symm
/-- The complete small faithful irreducible binary M₂₂ range has no
invariant nondegenerate alternating form. -/
theorem M22Recognition.not_alternating_of_small_degree
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M22 V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V ≤ 12)
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w) : False :=
  (M22Recognition.of_small_degree ρ hf hd).not_alternating ρ B ha hn hp
end Representation.MathieuSmall
