module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Collection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Detection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.CartanEntries
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges

/-!
# Split F4 coordinates from matrix exchanges and Cartan entries

Filtered adjacent exchanges give completeness of the ordered root product.
Triangular Cartan entries, together with nonzero F4 Cartan pairings in
characteristic two, give uniqueness. The proved matrix exchanges and Cartan
entry formulas discharge both premises, yielding unique coordinates in every
ordering for the positive support and both radical supports. Fixed-point
counts and radical orders require the separate fixed-coordinate calculation.

Source: the Chevalley root factorization used in Aschbacher–Smith,
F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`. All statements include
the binary endpoint `m = 0`.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates

open Theory.AlgebraicGroup StandardRootSystem

/-- The two independent matrix calculations suffice for unique split coordinates. -/
theorem wordInSubgroup_bijective_of_matrix_relations (m : ℕ) {k : Support}
    (e : RootOrder k)
    (hswap : ∀ (r s : Root k) (a b : CoefficientField m), r ≠ s →
      ∃ correction : List (Root k × CoefficientField m),
        (∀ z ∈ correction,
          max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
        rootGeneratorInGroup m r.val a * rootGeneratorInGroup m s.val b =
          rootGeneratorInGroup m s.val b * rootGeneratorInGroup m r.val a *
            FilteredCollection.wordProduct
              (fun q : Root k => rootGeneratorInGroup m q.val) correction)
    (hentries : ∀ (t u : Parameters m k) (r : Root k),
      (∀ s : Root k, rootDegree s.val < rootDegree r.val → t s = u s) →
      ∀ j : typeF4RootPairing_base.support,
        wordCartanEntry m e t r.val j - wordCartanEntry m e u r.val j =
          (t r - u r) * (typeF4RootPairing.pairingIn ℤ r.val j : CoefficientField m)) :
    Function.Bijective (wordInSubgroup m e) :=
  ⟨wordInSubgroup_injective_of_cartan_entries m e hentries,
    wordInSubgroup_surjective_of_exchange m hswap e⟩

/-- Every element of the root-generated split subgroup has unique parameters
in any ordering of the chosen support, including over the field at `m = 0`. -/
theorem wordInSubgroup_bijective (m : ℕ) {k : Support} (e : RootOrder k) :
    Function.Bijective (wordInSubgroup m e) :=
  wordInSubgroup_bijective_of_matrix_relations m e
    (rootGenerator_exchange m) (wordCartanEntry_sub_of_lower_eq m e)

end ReeF4.Parabolics.RadicalCoordinates
