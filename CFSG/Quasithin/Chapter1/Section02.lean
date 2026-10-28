module

public import Theory.GroupTheory.TwoLocalUniqueness
public import Theory.GroupTheory.CommutatorSup
public import Theory.Order.MaximalUpward

/-!
# Nonsolvable uniqueness subgroups: elementary consequences

This module assembles the elementary steps for Aschbacher–Smith §1.2,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
printed pp. 503–507. The centralizer-intersection theorem below is the
implication from uniqueness in Theorem 1.2.7(3) to the conclusion of (4).
It applies with `L₀ = ⟨Lᵀ⟩` and `Z = Ω₁(Z(T))`.

The imported order lemmas give the maximal-element step in Lemma 1.2.9(2)
once upward closure is established by (1). The commutator lemma gives the
(2)–(3) equivalence of Lemma 1.2.10 for its actual family of two-reduced groups.
The SQTK component and module-action results needed to establish uniqueness
and upward closure are separate inputs to the full section results.
-/

namespace CFSG.Quasithin.Chapter1.Section02

/-- The centralizer-intersection consequence of uniqueness, with the elementary
properties of `Ω₁(Z(T))` stated explicitly. -/
public theorem centralizer_intersection_of_uniqueness
    {G : Type*} [Group G] [Finite G] {L₀ T Z M : Subgroup G}
    (hM : IsMaximalTwoLocal M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L₀ ⊔ T ≤ K → K = M)
    (hZT : Z ≤ Subgroup.centralizer (T : Set G))
    (hZ : ∀ z ∈ Z, z ^ 2 = 1) {g : G} (hg : g ∉ M) :
    (Z ⊓ Subgroup.centralizer (L₀ : Set G)) ⊓
      (Z ⊓ Subgroup.centralizer (L₀ : Set G)).map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply Theory.GroupTheory.inf_conjugate_eq_bot_of_unique_maximalTwoLocal
    (H := L₀ ⊔ T) (Z := Z ⊓ Subgroup.centralizer (L₀ : Set G)) hM hunique ?_ (fun z hz => hZ z hz.1) hg
  exact sup_le (Subgroup.le_centralizer_iff.mpr inf_le_right)
    (Subgroup.le_centralizer_iff.mpr (inf_le_left.trans hZT))

end CFSG.Quasithin.Chapter1.Section02
