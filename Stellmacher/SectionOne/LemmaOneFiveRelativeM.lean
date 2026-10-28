module

public import Stellmacher.SectionOne.LemmaOneFive

/-!
# The relative lower bound from Stellmacher (1.5)

This module exposes the relative form of (1.5)(e) used in Stellmacher's proof
of (1.7): every elementary abelian subgroup of the chosen Sylow `2`-subgroup
has `m ≥ 1`.  For a nontrivial subgroup, the relative induction developed in
`LemmaOneFive` supplies an order-two `oneAmax` subgroup.  The order-two bound
and the monotonicity field of `oneAmax` then give the result; the trivial case
follows directly from the definition of `m`.

Source: `refs/latex/stellmacher-n-group.tex`, lines 525--526, where (1.5)(e)
is applied to a member of `𝒜(V,S)`.
-/

namespace Stellmacher.SectionOne

universe u

/-- The relative form of Stellmacher (1.5)(e) for elementary abelian
subgroups of the chosen Sylow `2`-subgroup. -/
public theorem lemma_one_five_m_ge_one_relative
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G)) (hT : IsElementaryAbelian 2 T) :
    m (G := G) (V := V) T ≥ 1 := by
  by_cases hTbot : T = ⊥
  · subst T
    unfold m
    simp
  · obtain ⟨A, hAmax, hAcard⟩ :=
      lemma_one_five_exists_oneAmax_card_two_relative h S T hTS hT hTbot
    exact (lemma_one_five_m_ge_one_of_card_two h A hAcard).trans hAmax.2.1

end Stellmacher.SectionOne
