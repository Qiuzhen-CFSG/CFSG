module

public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.FrattiniLocal
public import Theory.GroupTheory.PairwiseCommutingFamily

/-!
# Direct products of conjugate Sylow intersections

When `Φ(Q) ≠ 1`, distinct `H`-conjugates of `Q` contained in `S` commute.
The maximal-family normalizer argument applies inside the finite 2-group `S`:
I.7.4 supplies commutation under normalization, and the local Frattini
obstruction supplies commutation for a member permuting a commuting subfamily.
Together with the trivial intersections from I.7.2, this gives an internal
direct product, witnessed by an equivalence whose value is ambient multiplication.
The factors themselves need not be abelian.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.5, printed pp.426--427 (PDF pp.437--438).
Conjugation is left conjugation, as in `Intersection`.
-/

public section

namespace CFSG.Quasithin.ChapterI.Section06To08

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The commuting assertion in I.7.5, for the entire conjugate family. -/
theorem TightPGroupSetup.family_commuting_of_frattini_ne_bot
    {K H Q S : Subgroup G} (h : TightPGroupSetup K H Q S)
    (hΦ : frattini Q ≠ ⊥) :
    (tightConjugateFamily H Q S).Pairwise
      (fun A B => A ≤ centralizer (B : Set G)) := by
  let : Group.IsNilpotent S := h.hSp.isNilpotent
  apply Subgroup.pairwise_commuting_of_normalizer_centralizes
    (tightConjugateFamily H Q S) S
  · exact fun A hA => hA.1
  · exact fun A hA s hs => h.family_conjugate hA hs
  · exact fun A hA B hB hne hn => h.family_commuting_of_normalizes hA hB hne hn
  · intro Γ hΓ hc T hT ht A hA hne
    exact le_centralizer_iff.mp
      (h.family_commuting_of_permuting_of_frattini_ne_bot hΦ hΓ hc hT ht hA hne.symm)

/-- I.7.5: distinct members have trivial intersection and commute. -/
theorem lemma_I_7_5_commuting {K H Q S A B : Subgroup G}
    (h : TightPGroupSetup K H Q S) (hΦ : frattini Q ≠ ⊥)
    (hA : A ∈ tightConjugateFamily H Q S)
    (hB : B ∈ tightConjugateFamily H Q S) (hne : A ≠ B) :
    Disjoint A B ∧ A ≤ centralizer (B : Set G) :=
  ⟨h.family_disjoint hA hB hne, h.family_commuting_of_frattini_ne_bot hΦ hA hB hne⟩

/-- I.7.5: two distinct `H`-conjugates contained in `S` generate their
internal direct product, with multiplication as the isomorphism. -/
theorem lemma_I_7_5 {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) (hΦ : frattini Q ≠ ⊥)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (haS : conjSubgroup Q a ≤ S) (hbS : conjSubgroup Q b ≤ S)
    (hne : conjSubgroup Q a ≠ conjSubgroup Q b) :
    ∃ e : conjSubgroup Q a × conjSubgroup Q b ≃*
        ↥(conjSubgroup Q a ⊔ conjSubgroup Q b),
      ∀ u v, (e (u, v) : G) = (u : G) * (v : G) := by
  obtain ⟨hd, hc⟩ := lemma_I_7_5_commuting h hΦ
    ⟨haS, a, ha, rfl⟩ ⟨hbS, b, hb, rfl⟩ hne
  exact Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc

end CFSG.Quasithin.ChapterI.Section06To08
