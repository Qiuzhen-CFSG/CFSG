module
public import Theory.GroupTheory.FrattiniConjugatorAdjustment

/-!
# Frattini rechoice in the common normalizer of a crossing pair

If x fixes R and x² fixes D, it normalizes N(D) ∩ N(Dˣ) ∩ N(R).
The Sylow--Frattini adjustment within that literal intersection preserves
both marked conjugates and R, while normalizing its selected Sylow subgroup.

Source application: Aschbacher--Smith 2.5.7, printed p.556.
-/
@[expose] public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

noncomputable def pairNormalizer (D R : Subgroup G) (x : G) : Subgroup G :=
  normalizer (D : Set G) ⊓ normalizer (D.conjBy x : Set G) ⊓ normalizer (R : Set G)

omit [Finite G] in
theorem mem_normalizer_pairNormalizer (D R : Subgroup G) (x : G)
    (hD : x ^ 2 ∈ normalizer (D : Set G)) (hR : x ∈ normalizer (R : Set G)) :
    x ∈ normalizer (pairNormalizer D R x : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hDD : (D.conjBy x).conjBy x = D := by
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp hD
  have hRR : R.conjBy x = R := mem_normalizer_iff_map_conj_eq.mp hR
  change ((normalizer (D : Set G) ⊓ normalizer (D.conjBy x : Set G)) ⊓
    normalizer (R : Set G)).map (MulAut.conj x).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj x).injective,
    map_inf _ _ _ (MulAut.conj x).injective,
    map_equiv_normalizer_eq, map_equiv_normalizer_eq, map_equiv_normalizer_eq]
  change (normalizer (D.conjBy x : Set G) ⊓
    normalizer ((D.conjBy x).conjBy x : Set G)) ⊓
    normalizer (R.conjBy x : Set G) = _
  rw [hDD, hRR, inf_comm (normalizer (D.conjBy x : Set G))]
  rfl

theorem pair_frattini_rechoice (D R : Subgroup G) (x : G)
    (hD : x ^ 2 ∈ normalizer (D : Set G)) (hR : x ∈ normalizer (R : Set G))
    {p : ℕ} [Fact p.Prime] (P : Sylow p (pairNormalizer D R x)) :
    ∃ y : G, y ∈ normalizer ((P : Subgroup (pairNormalizer D R x)).map
      (pairNormalizer D R x).subtype : Set G) ∧
      D.conjBy y = D.conjBy x ∧ (D.conjBy x).conjBy y = D ∧
      R.conjBy y = R := by
  obtain ⟨y, hy, _, hpres⟩ := exists_frattini_adjustment_preserving
    (pairNormalizer D R x) P x (mem_normalizer_pairNormalizer D R x hD hR)
  have hDD : (D.conjBy x).conjBy x = D := by
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp hD
  have hRR : R.conjBy x = R := mem_normalizer_iff_map_conj_eq.mp hR
  exact ⟨y, hy, hpres D (inf_le_left.trans inf_le_right),
    (hpres (D.conjBy x) (by rw [hDD]; exact inf_le_left.trans inf_le_left)).trans hDD,
    (hpres R (by rw [hRR]; exact inf_le_right)).trans hRR⟩
end Subgroup
