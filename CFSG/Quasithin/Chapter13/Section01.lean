module

public import Theory.GroupTheory.CentralizerConjugateRigidity
public import Theory.GroupTheory.TwoLocalUniqueness
public import CFSG.Quasithin.ChapterI.Section06To08.Basic

/-!
# Eliminating nonquasisimple local components: the TI step

The target of Aschbacher--Smith §13.1 is Theorem 13.1.7: under Hypothesis
13.1.1 the family `L⁺(G,T)` is empty. This is the family of members of
`L_f(G,T)` whose quotient by their own two-core is not quasisimple, not just
the maximal members of that family.

This module currently proves the group-theoretic inference in 13.1.13 from
explicit centralizer and conjugate-rigidity inputs. Self-normalization of
maximal two-local subgroups supplies the remaining hypothesis. In the source,
`M = N_G(L)` and `U = [R₂(M), L]`. Lemmas 13.1.11 and 13.1.12 must still
establish the two displayed inputs for these actual subgroups; the theorem
below does not assert those lemmas or Theorem 13.1.7.

Source: *The Classification of Quasithin Groups*, combined 1 March 2004
manuscript, §13.1, printed pp. 865--876 (PDF pp. 882--893). The final proof
and the end of 13.1.14 are on p. 876, beyond the initial section page range.
-/

namespace CFSG.Quasithin.Chapter13.Section01

open CFSG.Quasithin.ChapterI.Section06To08

/-- The TI inference of 13.1.13, with its two earlier mathematical inputs
explicit. The second conclusion also supplies `N_G(U) = M`, used at the end
of the proof of 13.1.7. -/
public theorem ti_and_normalizer_of_centralizer_rigidity
    {G : Type*} [Group G] {U M : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hU : U ≠ ⊥)
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hcentral : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M)
    (hrigid : ∀ u ∈ U, u ≠ 1 → ∀ g : G,
      (M ⊓ Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom ≤ M →
      M.map (MulAut.conj g).toMonoidHom = M) :
    IsTISubgroup U ∧ Subgroup.normalizer (U : Set G) = M := by
  have hself := (Theory.GroupTheory.normalizer_eq_of_isMaximalTwoLocal hM).le
  refine ⟨?_, Subgroup.normalizer_eq_of_centralizer_conjugate_rigidity
    hself hcentral hrigid hU hMU⟩
  intro g hg x hx
  have hgM : g ∉ M := fun hgM => hg (hMU hgM)
  have hbot := Subgroup.inf_conjugate_eq_bot_of_centralizer_conjugate_rigidity
    hself hcentral hrigid hgM
  have hx' : x ∈ U ⊓ U.map (MulAut.conj g).toMonoidHom := by
    obtain ⟨hxU, u, hu, heq⟩ := hx
    exact ⟨hxU, u, hu, heq⟩
  change x = 1
  exact show x ∈ (⊥ : Subgroup G) from hbot ▸ hx'

end CFSG.Quasithin.Chapter13.Section01
