module

public import Theory.GroupTheory.CentralCommutatorQuotient
public import Theory.GroupTheory.PCoreRestriction

/-!+# Pushing up in the Fundamental Setup: terminal algebraic steps

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, §4.2, printed pp.608--612, PDF pp.625--629.

The terminal result is Theorem 4.2.13, including all five alternatives and
the additional centralizer conditions in (4) and (5). The results here
prove two algebraic steps with explicit inputs: the transfer of the local
two-core obstruction in (4), and the final commutator contradiction on
p.612. The latter constructs the surjective commutator map and lifts a
fixed value by coprime action before using normality in C_G(X).

These are conditional helpers, not assertions of Theorem 4.2.13. The
Hypotheses 4.2.1/4.2.3 setup, Theorem 4.2.5, Lemma 4.2.12, the reduction
to maximal pushing-up subgroups, and the concrete exceptional-group
calculations remain necessary. In particular, no classification alternative
or component-normality conclusion is hidden in a setup record here.

The PDF proof of (4) on p.611 prints V ≰ C_K(z). This cannot hold for
z ∈ V ≤ K with V abelian. The theorem's statement V ≰ O₂(C_G(z)) is
retained: the local input below concerns O₂(C_K(z)), not C_K(z).
-/

namespace CFSG.Quasithin.Chapter4.Section02

open Subgroup
open scoped commutatorElement

/-- The transfer in 4.2.13(4), after the exceptional-group calculation
has shown that V escapes the two-core of C_K(z). -/
public theorem ambient_centralizer_core_obstruction
    {G : Type*} [Group G] (K V : Subgroup G) [IsMulCommutative V]
    (hVK : V ≤ K) {z : G} (hz : z ∈ V)
    (hlocal : ¬ V ≤ (K ⊓ centralizer ({z} : Set G)).pCoreIn 2) :
    ¬ V ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  apply not_le_pCoreIn_of_subgroup 2 (H := K ⊓ centralizer ({z} : Set G))
    (le_inf hVK ?_) inf_le_right hlocal
  intro v hv
  exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hv hz)

/-- The last contradiction in 4.2.13, with Q = R₁, L = L_H and K = K_X.
The construction of these subgroups and the normalizer inclusion from
the source's J₄ case must still be supplied by the classification argument.
Only normality inside C_G(X) is used; ambient normality of K is unnecessary. -/
public theorem terminal_commutator_contradiction
    {G : Type*} [Group G] [Finite G] (Q V L X K : Subgroup G)
    (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V)
    (hLQ : L ≤ normalizer (Q : Set G)) (hLr : L ≤ centralizer ({r} : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ V → L ≤ normalizer (W : Set G) → W = ⊥ ∨ W = V)
    (hne : ∃ x ∈ Q, ¬ Commute r x)
    (hXQ : X ≤ normalizer (Q : Set G)) (hXr : X ≤ centralizer ({r} : Set G))
    (hsolv : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card X) (Nat.card Q))
    (hrK : r ∈ centralizer (K : Set G))
    (hK : centralizer (X : Set G) ≤ normalizer (K : Set G))
    (hv : ∃ v ∈ V, v ∈ centralizer (X : Set G) ∧ v ∉ centralizer (K : Set G)) :
    False := by
  obtain ⟨v, hvV, hvX, hvK⟩ := hv
  have hsurj := centralCommutatorHom_surjective_of_irreducible
    Q V L hV r hr hLQ hLr hirr hne
  obtain ⟨s, _, hsX, hcomm⟩ := centralCommutatorHom_exists_fixed_preimage
    Q V X hV r hr hXQ hXr hsolv hcop hsurj v hvV hvX
  exact hvK (hcomm ▸ commutator_mem_centralizer_of_normalizes K hrK (hK hsX))

end CFSG.Quasithin.Chapter4.Section02
