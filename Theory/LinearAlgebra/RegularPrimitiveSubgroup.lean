module

public import Theory.LinearAlgebra.RegularLinearAction
public import Theory.Representation.BinaryPrimeDegree

/-!
# Primitive-prime subgroups of regular binary linear groups

A nonzero invariant subspace inherits a faithful action from a group acting
regularly on nonzero vectors. The binary prime-degree bound forces this
subspace to be the whole space when the binary order of the prime is the
ambient dimension.

An irreducible subgroup of an abelian regular linear group has the same
centralizer as the whole group: match a commuting map with a regular actor
on one nonzero vector, and apply irreducibility to the kernel of their
difference. This supplies the full centralizer assertion without choosing
an isomorphism with a finite field.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.12, printed p.22.
-/

open Subgroup
namespace LinearGroup
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A primitive prime-order subgroup of a regular binary linear group acts irreducibly. -/
public theorem IsRegularOnNonzero.primitive_subgroup_invariant_eq_bot_or_top
    {X R : Subgroup (V ≃ₗ[ZMod 2] V)} (hreg : IsRegularOnNonzero X)
    (hRX : R ≤ X) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hR : Nat.card R = r) (hn : orderOf (2 : ZMod r) = Module.finrank (ZMod 2) V)
    (W : Submodule (ZMod 2) V)
    (hW : ∀ (a : R) (v : V), v ∈ W → (a : V ≃ₗ[ZMod 2] V) v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  let ρ : Representation (ZMod 2) R V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp R.subtype
  let σ := ρ.subrepresentation W hW
  have hσ : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply eq_bot_iff.mpr
    intro a ha
    have hvex : ∃ v : V, v ∈ W ∧ v ≠ 0 := by
      by_contra! h
      exact hb (eq_bot_iff.mpr fun v hv => (Submodule.mem_bot _).mpr (h v hv))
    obtain ⟨v, hv, hv0⟩ := hvex
    have hav : (a : V ≃ₗ[ZMod 2] V) v = v :=
      congrArg (fun f : Module.End (ZMod 2) W => (f ⟨v, hv⟩ : V)) ha
    have ha1 := hreg.eq_one_of_apply_eq_self (⟨a, hRX a.property⟩ : X) hv0 hav
    apply Subtype.ext
    exact congrArg (fun b : X => (b : V ≃ₗ[ZMod 2] V)) ha1
  have hle := Representation.BinaryPrimeDegree.orderOf_le_finrank σ hσ hr hr2
    (hR ▸ dvd_refl r)
  rw [hn] at hle
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) hle)

omit [FiniteDimensional (ZMod 2) V] in
/-- An irreducible subgroup of an abelian regular actor has that actor as its full centralizer. -/
public theorem IsRegularOnNonzero.centralizer_eq_of_irreducible_subgroup
    {X R : Subgroup (V ≃ₗ[ZMod 2] V)} [IsMulCommutative X]
    (hreg : IsRegularOnNonzero X) (hRX : R ≤ X)
    (hn : 0 < Module.finrank (ZMod 2) V)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ (a : R) (v : V), v ∈ W → (a : V ≃ₗ[ZMod 2] V) v ∈ W) →
      W = ⊥ ∨ W = ⊤) : centralizer (R : Set (V ≃ₗ[ZMod 2] V)) = X := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hn
  have hXC : X ≤ centralizer (R : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [← hreg.centralizer_eq]
    exact centralizer_le hRX
  apply le_antisymm ?_ hXC
  intro g hg
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hgv : g v ≠ 0 := fun h => hv (g.injective (h.trans (map_zero _).symm))
  obtain ⟨x, hx, _⟩ := hreg v (g v) hv hgv
  let f : V →ₗ[ZMod 2] V := g.toLinearMap - (x : V ≃ₗ[ZMod 2] V).toLinearMap
  have hinv : ∀ (a : R) (w : V), w ∈ f.ker → (a : V ≃ₗ[ZMod 2] V) w ∈ f.ker := by
    intro a w hw
    have hga := mem_centralizer_iff.mp hg a.val a.property
    have hxa := mem_centralizer_iff.mp (hXC x.property) a.val a.property
    change g ((a : V ≃ₗ[ZMod 2] V) w) -
      (x : V ≃ₗ[ZMod 2] V) ((a : V ≃ₗ[ZMod 2] V) w) = 0
    change g w - (x : V ≃ₗ[ZMod 2] V) w = 0 at hw
    have hga' := LinearEquiv.congr_fun hga w
    have hxa' := LinearEquiv.congr_fun hxa w
    simp only [LinearEquiv.mul_apply] at hga' hxa'
    rw [← hga', ← hxa', ← map_sub, hw, map_zero]
  have hvker : v ∈ f.ker := sub_eq_zero.mpr hx.symm
  have htop : f.ker = ⊤ := (hirr f.ker hinv).resolve_left (fun h => hv ((Submodule.mem_bot _).mp (h ▸ hvker)))
  have heq : g = (x : V ≃ₗ[ZMod 2] V) := by
    ext w
    have hw : w ∈ f.ker := by rw [htop]; trivial
    exact sub_eq_zero.mp hw
  exact heq ▸ x.property
end LinearGroup
