module

public import Mathlib.GroupTheory.Sylow

/-!
# Reducing the component case to a concrete Sylow center

In the component case of Aschbacher–Smith 15.4.20 (combined manuscript,
1 March 2004, printed p.1164), 1.1.5 supplies faithful inner actions of the
central four-group on the relevant linear component. If such an action fixes
a Sylow subgroup pointwise, its order is bounded by that Sylow subgroup's
center. Thus the model fact needed in this case is a bound on the actual
Sylow center; a classification of the entire automorphism group is unnecessary.

The proof uniquely lifts inner automorphisms through conjugation in a
centerless group. The image is a two-group centralizing the Sylow subgroup,
so Sylow maximality places it in that subgroup and then in its center.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
variable {K A : Type*} [Group K] [Group A] [Finite K]

/-- A faithful inner two-group action fixing a Sylow two-subgroup pointwise
embeds in its center. Every action and inner witness here is an actual map. -/
theorem faithful_inner_action_card_le_sylow_center (S : Sylow 2 K) (hcenter : center K = ⊥)
    (α : A →* MulAut K) (hinj : Function.Injective α)
    (hA : IsPGroup 2 A)
    (hinner : ∀ a : A, ∃ k : K, MulAut.conj k = α a)
    (hfixed : ∀ a : A, ∀ s : S, α a s = s) : Nat.card A ≤ Nat.card (center S) := by
  classical
  have hconj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    have hker : (MulAut.conj : K →* MulAut K).ker = center K := by
      ext k
      change MulAut.conj k = 1 ↔ k ∈ center K
      constructor
      · intro hk
        apply mem_center_iff.mpr
        intro x
        have hx := DFunLike.congr_fun hk x
        exact (mul_inv_eq_iff_eq_mul.mp hx).symm
      · intro hk
        ext x
        change k * x * k⁻¹ = x
        rw [← mem_center_iff.mp hk x, mul_inv_cancel_right]
    exact hker.trans hcenter
  choose f hf using hinner
  let φ : A →* K := {
    toFun := f
    map_one' := hconj (by rw [hf, map_one, map_one])
    map_mul' := fun a b => hconj (by rw [hf, map_mul, map_mul, hf, hf]) }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply hinj
    rw [← hf a, ← hf b]
    exact congrArg MulAut.conj hab
  have hPC : φ.range ≤ centralizer (S : Set K) := by
    rintro k ⟨a, rfl⟩
    apply mem_centralizer_iff.mpr
    intro s hs
    have hf' := hfixed a ⟨s, hs⟩
    rw [← hf] at hf'
    exact (mul_inv_eq_iff_eq_mul.mp hf').symm
  have hP : IsPGroup 2 φ.range := hA.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hPS : φ.range ≤ (S : Subgroup K) := by
    have hn : φ.range ≤ normalizer (S : Set K) := hPC.trans (Subgroup.centralizer_le_normalizer _)
    have heq := hP.inf_normalizer_sylow S
    rw [inf_of_le_left hn] at heq
    exact heq.le.trans inf_le_right
  let ψ : A → center S := fun a => ⟨⟨φ a, hPS ⟨a, rfl⟩⟩, by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hPC ⟨a, rfl⟩)) s s.property⟩
  exact Nat.card_le_card_of_injective ψ (fun a b hab =>
    hφ (congrArg (fun c : center S => ((c : S) : K)) hab))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
