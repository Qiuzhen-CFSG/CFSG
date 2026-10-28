module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Endgame

/-!
# The local embedding argument for ZD

Failure of local strong embedding gives the full structural branch of ZD
by minimality. The centralizer selection replaces this failure by C_G(u)
and supplies a distinct commuting conjugate of u. The involution-coset
identifications then give the four-group obstruction, and the actual
Bender automorphism calculations in the odd-core quotient give the final
contradiction.

This proves the exact relative local-embedding clause of `SimpleReduction`.
Only minimality and the absence of nontrivial solvable normal subgroups
are needed from the preliminary reduction; ambient simplicity and ambient
strong embedding are not assumed.

Source: GLS, Volume 4, Chapter 2, Proposition 4.4 and Lemmas 4.6--4.8.
-/

namespace BenderSuzuki.ZD

/-- GLS Proposition 4.4: the distinguished subgroup is strongly embedded
in every eligible proper distinguished closure, with the original nested
relative subgroup convention. The solvable-normal-subgroup hypothesis is
source Lemma 4.5, discharged by the minimal-reduction assembly owner. -/
public theorem MinimalCounterexample.local_embedding_of_no_solvable_normal
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M)
    (hsol : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M →
      (∃ z ∈ Z, z ∈ H ∧ z ∈ M) →
      IsStronglyEmbedded
        ((M.comap H.subtype).comap
          (Subgroup.closure (H.subtype ⁻¹' Z)).subtype) := by
  intro H hH hHM hne
  by_contra hnot
  obtain ⟨u, v, hu, huM, huv, hconj, hcomm, _, hC, hmeet, huL, hs, _⟩ :=
    h.centralizer_choice H hH hHM hne hnot hsol
  exact local_centralizer_structure_false h.disconnected hu huM hC hmeet huL hs
    huv hconj hcomm

end BenderSuzuki.ZD
