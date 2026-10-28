module
public import Theory.FieldTheory.FrobeniusCoefficientSeparation
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Data.Nat.Find

/-!
# Finite Frobenius actions on a highest-vector filtration

An invariant subspace has a nonzero vector of minimal filtration degree.
Frobenius coefficient separation makes its leading term primitive, hence the
highest vector lies in the subspace. Negative root expansions and induction
then recover every filtration layer. All hypotheses concern the original
operators, subspaces and finite group action; irreducibility is the conclusion.

Source: Steinberg, Representations of Algebraic Groups (1963), proof of 5.1(3)
and its finite twisted specialization in 12.2. The finite coefficient maps
are genuine distinct field embeddings, not formal independent variables.
-/

public section

open scoped BigOperators

namespace Representation.FrobeniusFiltered

variable {p : ℕ} [Fact p.Prime]
variable {E F G V I J : Type*} [Field E] [Finite E] [Algebra (ZMod p) E]
  [Field F] [Group G] [AddCommGroup V] [Module F V]

theorem isIrreducible [Nontrivial V]
    (f : E →+* F) (ρ : Representation F G V)
    (C : ℤ → Submodule F V) (hmono : Monotone C)
    (N : ℕ) (htop : C N = ⊤)
    (v : V) (hzero : C 0 = Submodule.span F {v})
    (P : I → Fin (Module.finrank (ZMod p) E) → Module.End F V)
    (Q : J → Fin (Module.finrank (ZMod p) E) → Module.End F V)
    (d : I → ℕ) (hd : ∀ i, 0 < d i) (e : J → ℕ) (he : ∀ j, 0 < e j)
    (positive : I → E → G) (negative : J → E → G)
    (hP : ∀ i k x, x ∈ C k → ∀ a, P i a x ∈ C (k - d i))
    (hpos : ∀ i k x, x ∈ C k → ∀ t,
      ρ (positive i t) x - x - ∑ a, f (t ^ (p ^ a.val)) • P i a x ∈ C (k - d i - 1))
    (hprimitive : ∀ k : ℕ, 0 < k → ∀ x, x ∈ C k →
      (∀ i a, P i a x ∈ C ((k : ℤ) - d i - 1)) → x ∈ C ((k : ℤ) - 1))
    (hneg : ∀ j k x, x ∈ C k → ∀ t,
      ρ (negative j t) x - x - ∑ a, f (t ^ (p ^ a.val)) • Q j a x ∈ C (k + e j - 1))
    (hgenerate : ∀ k : ℕ, 0 < k → C k ≤ C ((k : ℤ) - 1) ⊔
      ⨆ j, ⨆ a, (C ((k : ℤ) - e j)).map (Q j a))
    : IsSimpleOrder (Subrepresentation ρ) := by
  classical
  have : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hh
  apply IsSimpleOrder.of_forall_eq_top
  intro W hne
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
  have hall (k : ℕ) : C k ≤ W.toSubmodule := by
    induction k with
    | zero => rw [Nat.cast_zero, hzero]; exact (Submodule.span_singleton_le_iff_mem v _).mpr hvW
    | succ k ih =>
      have hprev : C ((k+1 : ℕ) - (1 : ℤ)) ≤ W.toSubmodule := by
        simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using ih
      apply (hgenerate (k+1) (by omega)).trans
      apply sup_le hprev
      refine iSup_le fun j => iSup_le fun a => ?_
      rintro y ⟨u, hu, rfl⟩
      have huW : u ∈ W := hprev ((hmono (by have := he j; omega)) hu)
      apply FiniteField.frobenius_coefficients_mem f W.toSubmodule (Q j · u) _ a
      intro t
      have ht := hneg j ((k+1 : ℕ) - (e j : ℤ)) u hu t
      have htW : ρ (negative j t) u - u - ∑ b, f (t ^ (p ^ b.val)) • Q j b u ∈ W := by
        apply hprev
        simpa only [sub_add_cancel] using ht
      have hdW := W.toSubmodule.sub_mem (W.apply_mem_toSubmodule (negative j t) huW) huW
      simpa only [sub_sub_cancel] using W.toSubmodule.sub_mem hdW htW
  apply top_unique
  intro z hz
  exact hall N (by rw [htop]; trivial)

end Representation.FrobeniusFiltered
