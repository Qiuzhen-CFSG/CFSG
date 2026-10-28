module

public import Theory.GroupTheory.ReducedNormal.CentralSeedClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# Reduced central-seed spans in Sylow overgroups

Let A contain the ambient Sylow two-subgroup T and have characteristic two.
For an elementary subgroup Z of Z(T), the literal span ⟨Z^A⟩, viewed inside
A, is two-reduced. Restrict T to A and identify the intrinsic normal closure
with the embedded conjugate span before applying the central-seed theorem.

Source: Aschbacher--Smith, B.2.14, printed p.78; used for the two distinct
orbit modules in 14.3.25 and 14.3.31, printed pp.1001 and 1003.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The quotient in reducedness is A/C_A(⟨Z^A⟩), with A's own centralizer. -/
theorem reduced_conjugateSpan_of_sylow_central (T : Sylow 2 G)
    (A Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hTA : (T : Subgroup G) ≤ A) (hZT : Z ≤ (T : Subgroup G))
    (hZC : Z ≤ centralizer (T : Set G))
    (hchar : centralizer (pCore 2 A : Set A) ≤ pCore 2 A) :
    IsPReduced 2 ((conjugateSpanBy Z A).subgroupOf A) := by
  let : IsElementaryAbelian 2 (Z.subgroupOf A) :=
    IsElementaryAbelian.subgroupOf (hZT.trans hTA)
  have hc : Z.subgroupOf A ≤ centralizer (T.subtype hTA : Set A) := by
    intro z hz t ht
    exact Subtype.ext (hZC hz t ht)
  have hh := centralSeed_normalClosure_reduced (T.subtype hTA) (Z.subgroupOf A)
    (comap_mono hZT) hc hchar
  rwa [normalClosure_subgroupOf_eq_conjugateSpanBy Z A (hZT.trans hTA)] at hh

end Theory.GroupTheory
