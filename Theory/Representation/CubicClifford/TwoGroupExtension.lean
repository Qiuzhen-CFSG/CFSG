module
public import Theory.Representation.CubicClifford.Extension
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
/-!
# Extending simple constituents across a two-group quotient

The space of component intertwiners is nonzero. A two-group quotient fixes a nonzero vector in this binary space, giving an ambient intertwiner. Schur’s lemma makes it an equivalence. This proves uniqueness of a simple extension without assuming homogeneity or absolute irreducibility. The seven-point consumer applies it to the literal natural core.

Source: Clifford extension argument in Aschbacher–Smith 13.8.24, printed pp.958–959.
-/

public section
namespace Representation.CubicClifford
variable {H V E : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

private abbrev action {Q F : Type*} [Group Q] [AddCommGroup F] [Module (ZMod 2) F]
    (ρ : Representation (ZMod 2) Q F) : MulAction Q F where
  smul g v := ρ g v
  one_smul v := by change ρ 1 v = v; simp
  mul_smul g h v := by change ρ (g*h) v = ρ g (ρ h v); simp [Module.End.mul_apply]

private theorem fixed_vector {Q F : Type*} [Group Q] [AddCommGroup F]
    [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F] [Nontrivial F]
    (ρ : Representation (ZMod 2) Q F) (hQ : IsPGroup 2 Q) :
    ∃ v : F, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  let := action ρ
  let : Finite F := Module.finite_of_finite (ZMod 2)
  have hd : 2 ∣ Nat.card F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  obtain ⟨v, hv, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    F hd (a := (0 : F)) (by intro g; exact map_zero (ρ g))
  exact ⟨v, Ne.symm hne, hv⟩

omit [Finite H] in
/-- An extending simple constituent determines a simple binary module above
it when the quotient is a two-group. The equivalence preserves the full actor. -/
theorem equiv_of_extending_constituent (K : Subgroup H) [K.Normal]
    (hQ : IsPGroup 2 (H ⧸ K))
    (τ : Representation (ZMod 2) H E) (ρ : Representation (ZMod 2) H V)
    [IsIrreducible τ] [IsIrreducible ρ]
    (A : Subrepresentation (ρ.comp K.subtype))
    (e : A.toRepresentation.Equiv (τ.comp K.subtype)) : Nonempty (τ.Equiv ρ) := by
  let f : E →ₗ[ZMod 2] V := A.toSubmodule.subtype.comp e.symm.toLinearEquiv.toLinearMap
  have hf : f ∈ homSpace K τ ρ := by
    intro k
    ext x
    change ρ k (f (τ (k : H)⁻¹ x)) = f x
    have hi := LinearMap.congr_fun (e.symm.isIntertwining' k) (τ (k : H)⁻¹ x)
    have he := congrArg Subtype.val hi
    change f (τ k (τ (k : H)⁻¹ x)) = ρ k (f (τ (k : H)⁻¹ x)) at he
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using he.symm
  have hi : Function.Injective f := Subtype.val_injective.comp e.symm.toLinearEquiv.injective
  let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial τ
  have hfn : f ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact hx (hi (by rw [hz]; rfl))
  let : Nontrivial (homSpace K τ ρ) := ⟨⟨⟨f,hf⟩, 0, fun h => hfn (congrArg Subtype.val h)⟩⟩
  obtain ⟨u, hu, hfix⟩ := fixed_vector (homQuotientRepresentation K τ ρ) hQ
  let i : τ.IntertwiningMap ρ := ⟨u.val, fun h => by
    ext x
    have he := congrArg Subtype.val (hfix (QuotientGroup.mk' K h))
    have hh := LinearMap.congr_fun he (τ h x)
    change ρ h (u.val (τ h⁻¹ (τ h x))) = u.val (τ h x) at hh
    simpa only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh.symm⟩
  have hin : i ≠ 0 := by
    intro hz
    apply hu
    apply Subtype.ext
    exact congrArg IntertwiningMap.toLinearMap hz
  exact ⟨i.ofBijective ⟨(IsIrreducible.injective_or_eq_zero i).resolve_right hin,
    (IsIrreducible.surjective_or_eq_zero i).resolve_right hin⟩⟩
end Representation.CubicClifford
