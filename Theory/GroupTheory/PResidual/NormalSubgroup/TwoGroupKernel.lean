module

public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Normal two-perfect subgroups modulo a two-group kernel

Equal images of normal two-perfect subgroups lift to equality: each subgroup
is the two-residual of its product with the kernel. The three-part of a
subgroup's order is also unchanged by passage through a two-group kernel.

Source application: Aschbacher--Smith, 15.3.40, printed p.1138, identifying
the two residual factors through the rank-two quotient.
-/

public section

open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Normal two-perfect subgroups are determined by their image through a
homomorphism with two-group kernel. -/
theorem eq_of_normal_twoPerfect_of_map_eq (f : G →* H)
    (hk : IsPGroup 2 f.ker) (A B : Subgroup G) [A.Normal] [B.Normal]
    (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B) (he : A.map f = B.map f) : A = B := by
  have hs : A ⊔ f.ker = B ⊔ f.ker := by
    simpa only [comap_map_eq] using congrArg (Subgroup.comap f) he
  have ha := embedded_pResidual_join_pGroup A f.ker hA hk
    (show f.ker ≤ normalizer (A : Set G) by rw [A.normalizer_eq_top]; exact le_top)
  have hb := embedded_pResidual_join_pGroup B f.ker hB hk
    (show f.ker ≤ normalizer (B : Set G) by rw [B.normalizer_eq_top]; exact le_top)
  rw [hs] at ha
  exact ha.symm.trans hb

/-- A two-group kernel preserves each subgroup's exact three-part. -/
theorem threePart_map_of_twoGroup_kernel [Finite G] (f : G →* H)
    (hk : IsPGroup 2 f.ker) (A : Subgroup G) :
    3 ^ (Nat.card (A.map f)).factorization 3 = 3 ^ (Nat.card A).factorization 3 := by
  let : Finite (A.map f) := Finite.of_surjective _ (f.subgroupMap_surjective A)
  let g := f.subgroupMap A
  have hkg : IsPGroup 2 g.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hkg
  have hc : Nat.card A = 2 ^ n * Nat.card (A.map f) := by
    rw [← g.ker.card_mul_index, index_ker, hn,
      g.range_eq_top_of_surjective (f.subgroupMap_surjective A), card_top]
  rw [hc, Nat.factorization_mul (pow_ne_zero n (by decide)) Nat.card_pos.ne']
  simp [Nat.factorization_pow, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]

end Subgroup
