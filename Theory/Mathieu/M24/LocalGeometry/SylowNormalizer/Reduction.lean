module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Centralizer
public import Theory.Mathieu.M24.Properties.Order
public import Theory.GroupTheory.SylowPGroupAutomizer

/-!+# Reduction of the M₂₄ Sylow normalizer to two local computations

The marked subgroup has two-group centralizer by the explicit permutation
calculation. If its order is 1024, the established order of M₂₄ makes it Sylow.
If its automorphism group is a two-group, its normalizer is the product of the
subgroup and its centralizer, hence a two-group and equal to the Sylow subgroup.
Sylow conjugacy then transports this equality to every Sylow two-subgroup.

The order and automorphism premises remain explicit mathematical obligations.
Source context: Aschbacher–Smith, printed p.511, and GLS3, Table 5.3e.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer

private theorem two_part : (Nat.card M24).factorization 2 = 10 := by
  rw [m24_order, Nat.factorization_def _ Nat.prime_two,
    show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 10]
  rw [padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))]

/-- The local cardinality identifies the marked subgroup as Sylow. -/
noncomputable def candidateSylow (hcard : Nat.card candidate = 1024) : Sylow 2 M24 :=
  Sylow.ofCard candidate (by rw [hcard, two_part]; norm_num)

/-- The only missing local inputs are the order and the automorphism two-group bound. -/
theorem candidate_normalizer_eq (hcard : Nat.card candidate = 1024)
    (haut : IsPGroup 2 (MulAut candidate)) :
    Subgroup.normalizer (candidate : Set M24) = candidate := by
  let S := candidateSylow hcard
  have he : Subgroup.normalizer (candidate : Set M24) =
      candidate ⊔ Subgroup.centralizer (candidate : Set M24) :=
    S.normalizer_eq_sup_centralizer_of_isPGroup_action (haut.to_subgroup _)
  have hp : IsPGroup 2 (Subgroup.normalizer (candidate : Set M24)) := by
    rw [he]
    exact S.isPGroup'.to_sup_of_normal_left' centralizer_isPGroup
      (Subgroup.centralizer_le_normalizer _)
  exact S.is_maximal' hp Subgroup.le_normalizer

/-- Conjugacy transports the marked normalizer calculation to every Sylow subgroup. -/
theorem sylow_normalizer_le (hcard : Nat.card candidate = 1024)
    (haut : IsPGroup 2 (MulAut candidate)) (S : Sylow 2 M24) :
    Subgroup.normalizer (S : Set M24) ≤ S.toSubgroup := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 (candidateSylow hcard) S
  have hmap : candidate.map (MulAut.conj g).toMonoidHom = S.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  change Subgroup.normalizer (S.toSubgroup : Set M24) ≤ S.toSubgroup
  rw [← hmap, ← Subgroup.map_equiv_normalizer_eq,
    candidate_normalizer_eq hcard haut]

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
