module
public import Theory.FieldTheory.FrobeniusCoefficientSeparation
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Data.Nat.Find

/-!
# Positive root filtrations and invariant pairings

The finite Frobenius leading-term argument puts the highest vector in every
nonzero invariant subspace. A nondegenerate invariant pairing then proves
irreducibility: a proper subspace has a nonzero invariant annihilator, which
also contains that highest vector, contradicting its nonzero pairing with an
orbit translate already in the original subspace.

This form avoids a negative-remainder hypothesis: the native Ree correction
roots have larger degree in both chambers. It is used for exactly the finite
irreducibility clause of Steinberg (1963), Theorem 12.2.
-/

public section

open scoped BigOperators
namespace Representation.FrobeniusFiltered
variable {p : ℕ} [Fact p.Prime]
variable {E F G V I : Type*} [Field E] [Finite E] [Algebra (ZMod p) E]
  [Field F] [Group G] [AddCommGroup V] [Module F V]

theorem highest_mem
    (f : E →+* F) (ρ : Representation F G V)
    (C : ℤ → Submodule F V) (hmono : Monotone C)
    (N : ℕ) (htop : C N = ⊤)
    (v : V) (hzero : C 0 = Submodule.span F {v})
    (P : I → Fin (Module.finrank (ZMod p) E) → Module.End F V)
    (d : I → ℕ) (hd : ∀ i, 0 < d i)
    (positive : I → E → G)
    (hP : ∀ i k x, x ∈ C k → ∀ a, P i a x ∈ C (k - d i))
    (hpos : ∀ i k x, x ∈ C k → ∀ t,
      ρ (positive i t) x - x - ∑ a, f (t ^ (p ^ a.val)) • P i a x ∈ C (k - d i - 1))
    (hprimitive : ∀ k : ℕ, 0 < k → ∀ x, x ∈ C k →
      (∀ i a, P i a x ∈ C ((k : ℤ) - d i - 1)) → x ∈ C ((k : ℤ) - 1))
    (W : Subrepresentation ρ) (hne : W ≠ ⊥) : v ∈ W.toSubmodule := by
  classical
  have hex : ∃ k : ℕ, ∃ x ∈ W.toSubmodule ⊓ C k, x ≠ 0 := by
    have hn : W.toSubmodule ≠ ⊥ := fun h => hne (by ext x; exact SetLike.ext_iff.mp h x)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    exact ⟨N, x, ⟨hx, by rw [htop]; trivial⟩, hx0⟩
  let k := Nat.find hex
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ W.toSubmodule ⊓ C k, x ≠ 0 := Nat.find_spec hex
  have hk : k = 0 := by
    by_contra hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hkill (y : V) (hyW : y ∈ W) (hyC : y ∈ C ((k : ℤ) - 1)) : y = 0 := by
      by_contra hy0
      apply Nat.find_min' hex (show ∃ z ∈ W.toSubmodule ⊓ C ((k-1 : ℕ) : ℤ), z ≠ 0 from
        ⟨y, ⟨hyW, by simpa [Nat.cast_sub (by omega : 1 ≤ k)] using hyC⟩, hy0⟩) |>.not_gt
      exact Nat.sub_lt hk0 (by decide)
    have hcoeff (i : I) (a : Fin (Module.finrank (ZMod p) E)) :
        P i a x ∈ C ((k : ℤ) - d i - 1) := by
      apply FiniteField.frobenius_coefficients_mem f _ (P i · x) _ a
      intro t
      have hsum : (∑ a, f (t ^ (p ^ a.val)) • P i a x) ∈ C ((k : ℤ) - 1) := by
        apply Submodule.sum_mem
        intro a ha
        exact (hmono (by have := hd i; omega))
          ((C ((k : ℤ) - d i)).smul_mem _ (hP i k x hx.2 a))
      have htail := hpos i k x hx.2 t
      have ht : ρ (positive i t) x - x ∈ C ((k : ℤ) - 1) := by
        have hs := (C ((k : ℤ) - 1)).add_mem
          ((hmono (by have := hd i; omega)) htail) hsum
        simpa only [sub_add_cancel] using hs
      have hz := hkill (ρ (positive i t) x - x)
        (W.toSubmodule.sub_mem (W.apply_mem_toSubmodule _ hx.1) hx.1) ht
      simpa only [hz, zero_sub, Submodule.neg_mem_iff] using htail
    have hlower := hprimitive k hk0 x hx.2 hcoeff
    exact hx0 (hkill x hx.1 hlower)
  have hvW : v ∈ W.toSubmodule := by
    have hxC : x ∈ Submodule.span F {v} := by simpa [hk, hzero] using hx.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxC
    have hc0 : c ≠ 0 := by intro hz; exact hx0 (by simpa [hz] using hc.symm)
    have hm := W.toSubmodule.smul_mem c⁻¹ hx.1
    simpa only [← hc, inv_smul_smul₀ hc0] using hm
  exact hvW

end Representation.FrobeniusFiltered

namespace Representation
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

theorem irreducible_of_common_line_and_pairing (ρ : Representation F G V)
    (v : V) (e : V ≃ₗ[F] Module.Dual F V)
    (he : ∀ g x y, e (ρ g x) (ρ g y) = e x y)
    (g₀ : G) (hpair : e v (ρ g₀ v) ≠ 0)
    (hline : ∀ W : Subrepresentation ρ, W ≠ ⊥ → v ∈ W) : IsIrreducible ρ := by
  classical
  have hv : v ≠ 0 := by intro h; simp [h] at hpair
  have : Nontrivial V := ⟨⟨v,0,hv⟩⟩
  have : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥,⊤,?_⟩⟩
    intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  by_contra htop
  let D : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualAnnihilator.comap e.toLinearMap
      apply_mem_toSubmodule g x hx := by
        change e (ρ g x) ∈ W.toSubmodule.dualAnnihilator
        rw [Submodule.mem_dualAnnihilator]
        intro y hy
        have hi : ρ g (ρ g⁻¹ y) = y := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        rw [← hi, he]
        exact (Submodule.mem_dualAnnihilator _).mp hx _ (W.apply_mem_toSubmodule g⁻¹ hy) }
  have hDbot : D ≠ ⊥ := by
    have hAnn : W.toSubmodule.dualAnnihilator ≠ ⊥ := by
      intro h
      have hWtop := Submodule.dualAnnihilator_eq_bot_iff.mp h
      apply htop
      ext x
      exact SetLike.ext_iff.mp hWtop x
    obtain ⟨ℓ,hℓ,hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAnn
    obtain ⟨x,hx⟩ := e.surjective ℓ
    intro h
    have hxD : x ∈ D := by change e x ∈ W.toSubmodule.dualAnnihilator; rw [hx]; exact hℓ
    have hx0 : x = 0 := by
      have hh : x ∈ (⊥ : Subrepresentation ρ) := h ▸ hxD
      exact (show x ∈ (⊥ : Submodule F V) from hh)
    apply hℓ0
    rw [← hx, hx0, map_zero]
  have hvD : e v ∈ W.toSubmodule.dualAnnihilator := hline D hDbot
  exact hpair ((Submodule.mem_dualAnnihilator _).mp hvD _
    (W.apply_mem_toSubmodule g₀ (hline W hW)))

end Representation
