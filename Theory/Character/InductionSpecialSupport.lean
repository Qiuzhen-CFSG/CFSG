module

public import Theory.Character.Induction

/-!
# Induction on a special support

Suppose every transporter between two elements of a subset of H lies in H.
For a class function supported on that subset, the induced function agrees
with it on the subset: the only nonzero terms in the induction sum come
from H, and conjugacy invariance makes all those terms equal.
Frobenius reciprocity therefore shows that induction preserves scalar
products of supported class functions.

This is the special-set induction argument used in P. Fong,
*Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), 65–76, printed p. 72.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Fintype G]

/-- A supported class function agrees with its induction on a set whose
transporters all lie in the inducing subgroup. -/
theorem inducedClassFunction_eq_on_specialSupport (H : Subgroup G) (A : Set H)
    (hA : ∀ a b : H, a ∈ A → b ∈ A →
      ∀ g : G, g⁻¹ * (a : G) * g = (b : G) → g ∈ H)
    (φ : ClassFunction H) (hc : IsClassFunction φ) (hs : supportedOn φ A)
    (a : H) (ha : a ∈ A) : inducedClassFunction H φ a = φ a := by
  classical
  unfold inducedClassFunction
  have hsum : (∑ g : G, if h : g⁻¹ * (a : G) * g ∈ H then φ ⟨_, h⟩ else 0) =
      ∑ _g : H, φ a := by
    apply Finset.sum_congr_set (H : Set G)
    · intro g hg
      have hm := H.mul_mem (H.mul_mem (H.inv_mem hg) a.property) hg
      rw [dif_pos hm]
      have he : (⟨g⁻¹ * (a : G) * g, hm⟩ : H) =
          (⟨g, hg⟩ : H)⁻¹ * a * ⟨g, hg⟩ := Subtype.ext rfl
      rw [he]
      simpa only [inv_inv] using hc a (⟨g, hg⟩ : H)⁻¹
    · intro g hg
      split
      · next hm =>
        apply hs
        intro hb
        exact hg (hA a ⟨_, hm⟩ ha hb g rfl)
      · rfl
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hn : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card H ≠ 0)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Frobenius reciprocity makes induction an isometry on special support.
Only the second function needs conjugacy invariance for this identity. -/
theorem scalarProduct_inducedClassFunction_of_specialSupport (H : Subgroup G) (A : Set H)
    (hA : ∀ a b : H, a ∈ A → b ∈ A →
      ∀ g : G, g⁻¹ * (a : G) * g = (b : G) → g ∈ H)
    (φ ψ : ClassFunction H) (hψ : IsClassFunction ψ)
    (hφA : supportedOn φ A) (hψA : supportedOn ψ A) :
    scalarProduct G (inducedClassFunction H φ) (inducedClassFunction H ψ) =
      scalarProduct H φ ψ := by
  classical
  rw [scalarProduct_inducedClassFunction H φ (inducedClassFunction_isClassFunction H ψ)]
  unfold scalarProduct
  rw [Subsingleton.elim (Fintype.ofFinite H) (inferInstance : Fintype H)]
  congr 1
  apply Fintype.sum_congr
  intro a
  by_cases ha : a ∈ A
  · exact congrArg (fun z : ℂ => φ a * star z)
      (inducedClassFunction_eq_on_specialSupport H A hA ψ hψ hψA a ha)
  · rw [hφA a ha, zero_mul, zero_mul]
