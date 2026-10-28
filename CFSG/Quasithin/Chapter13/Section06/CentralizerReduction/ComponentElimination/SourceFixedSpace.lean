module

public import Theory.GroupTheory.CentralizerSupplementComparison
public import Theory.GroupAction.PPerfectCentralQuotientFixed
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Checked

/-!
# The last fixed-space deduction in 13.6.22

The model calculation gives C_{Ŭ}(Lᵥ) = C_{Ŭ}(K), and B.2.14 gives
F̌ = Ŭ C_{F̌}(K). The centralizing-supplement comparison therefore makes
the checked image of a fixed by K. Fixation lifts through the actual
central two-group kernel ⟨v⟩ because K is two-perfect: its displacement
homomorphism into that kernel is trivial.

The consumer uses the existing literal checked quotient and image maps.
The small-model owner must still prove the fixed-space equality and
construct the B.2.14 decomposition, and the containment owner must supply
Lᵥ ≤ K. These conclusions of the source case analysis remain explicit;
this module proves the common final deduction, not the model exclusions.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 13.6.22, printed p.933.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
open A5Module
variable {G : Type*} [Group G]

/-- Centralization in C_G(v)/⟨v⟩ lifts for a two-perfect subgroup when v² = 1. -/
theorem centralizes_of_checked_centralizes (K : Subgroup G) (v : G) (a : Gv v)
    (hK : K ≤ Gv v) (hpK : IsPPerfect 2 K) (hv : v ^ 2 = 1)
    (ha : checkedQuotientMap v a ∈ centralizer (checkedImage v K : Set (Gcheck v))) :
    K ≤ Gv (a : G) := by
  have hp : IsPGroup 2 (vLine v) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change Nat.card (zpowers (centralElement v)) ∣ 2 ^ 1
    rw [Nat.card_zpowers]
    have hv' : centralElement v ^ 2 = 1 := Subtype.ext hv
    simpa only [pow_one] using orderOf_dvd_of_pow_eq_one hv'
  have hpk : IsPPerfect 2 (K.subgroupOf (Gv v)) :=
    hpK.of_surjective (subgroupOfEquivOfLe hK).symm.toMonoidHom
      (subgroupOfEquivOfLe hK).symm.surjective
  have hfixed := MulAut.fixed_of_fixed_mod_central_p_kernel (checkedQuotientMap v)
    (MulAut.conj a) (K.subgroupOf (Gv v)) hpk
    (by rwa [checkedQuotientMap_kernel])
    (by rw [checkedQuotientMap_kernel]; exact vLine_le_center v) (by
      intro x hx
      change checkedQuotientMap v (a * x * a⁻¹) = checkedQuotientMap v x
      rw [map_mul, map_mul, map_inv,
        ← ha (checkedQuotientMap v x) (mem_map_of_mem _ hx), mul_inv_cancel_right])
  intro k hk
  have hf := congrArg Subtype.val (hfixed ⟨k, hK hk⟩ hk)
  change (a : G) * k * (a : G)⁻¹ = k at hf
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hf).symm

/-- Apply the source fixed-space equality and B.2.14 splitting, then lift
through the specified checked quotient. -/
theorem centralizes_of_checked_fixed_space_comparison
    (L K U : Subgroup G) (v : G) (a : Gv v) (F : Subgroup (Gcheck v))
    [IsMulCommutative F]
    (hK : K ≤ Gv v) (hpK : IsPPerfect 2 K) (hv : v ^ 2 = 1)
    (hLK : Lv L v ≤ K)
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v U ⊔ (F ⊓ centralizer (checkedImage v K : Set (Gcheck v))))
    (hfix : checkedImage v U ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v U ⊓ centralizer (checkedImage v K : Set (Gcheck v))) :
    K ≤ Gv (a : G) := by
  apply centralizes_of_checked_centralizes K v a hK hpK hv
  have hD : checkedImage v (Lv L v) ≤ checkedImage v K := map_mono (comap_mono hLK)
  have hU : checkedImage v U ≤ F := hsplit ▸ le_sup_left
  have hC : F ⊓ centralizer (checkedImage v K : Set (Gcheck v)) ≤
      normalizer (checkedImage v U : Set (Gcheck v)) :=
    ((inf_le_left.trans (le_centralizer F)).trans (centralizer_le hU)).trans
      (Subgroup.centralizer_le_normalizer _)
  have he := inf_centralizer_eq_of_normalizing_supplement
    (checkedImage v U) (F ⊓ centralizer (checkedImage v K : Set (Gcheck v)))
    (checkedImage v K) (checkedImage v (Lv L v)) hD inf_le_right hC hfix
  rw [← hsplit] at he
  apply (he.le ⟨haF, ?_⟩).2
  rintro _ ⟨x, hx, rfl⟩
  have hc : x * a = a * x := Subtype.ext (ha x hx)
  exact congrArg (checkedQuotientMap v) hc
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
