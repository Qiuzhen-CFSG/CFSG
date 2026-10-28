module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Basic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.Columns

/-!
# Recovering split coordinates from Cartan columns

The root-coroot pairing detects every F4 root even in characteristic two.
Consequently, a triangular formula for the Cartan columns of an ordered
product recovers its parameters by induction on root height. The formula
required here is a concrete equality of matrix entries: when all lower
parameters agree, the difference in a root row is its parameter difference
times its Cartan pairing. Proving this formula for the actual divided-power
matrices remains a separate obligation.

This is the uniqueness step in the ordered Chevalley root construction
underlying Aschbacher–Smith F.1.12(I)(5), printed p.263 of
`refs/quasithin.pdf`. No group order or fixed-point calculation is used.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates

open Theory.AlgebraicGroup StandardRootSystem

/-- A root row and simple Cartan column of the actual ordered matrix product. -/
def wordCartanEntry (m : ℕ) {k : Support} (e : RootOrder k)
    (t : Parameters m k) (r : F4Chevalley.Root)
    (j : typeF4RootPairing_base.support) : CoefficientField m :=
  (word m e t).val.val (Sum.inr r) (Sum.inl j)

/-- The scalar multiplying each root parameter can be chosen nonzero. -/
theorem exists_detecting_coroot (m : ℕ) (r : F4Chevalley.Root) :
    ∃ j : typeF4RootPairing_base.support,
      (typeF4RootPairing.pairingIn ℤ r j : CoefficientField m) ≠ 0 :=
  WordRelations.Faithfulness.Adjoint.PositiveSimple.exists_pairingIn_cast_ne_zero m r

/-- Triangular Cartan entries recover all parameters, for any support and order. -/
theorem wordInSubgroup_injective_of_cartan_entries (m : ℕ) {k : Support}
    (e : RootOrder k)
    (hentries : ∀ (t u : Parameters m k) (r : Root k),
      (∀ s : Root k, rootDegree s.val < rootDegree r.val → t s = u s) →
      ∀ j : typeF4RootPairing_base.support,
        wordCartanEntry m e t r.val j - wordCartanEntry m e u r.val j =
          (t r - u r) * (typeF4RootPairing.pairingIn ℤ r.val j : CoefficientField m)) :
    Function.Injective (wordInSubgroup m e) := by
  intro t u htu
  have hw : word m e t = word m e u := congrArg Subtype.val htu
  have recover : ∀ n (r : Root k), rootDegree r.val = n → t r = u r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro r hr
        obtain ⟨j, hj⟩ := exists_detecting_coroot m r.val
        have hc := hentries t u r (fun s hs => ih (rootDegree s.val) (hr ▸ hs) s rfl) j
        have he : wordCartanEntry m e t r.val j = wordCartanEntry m e u r.val j :=
          congrArg (fun x : SplitGroup m => x.val.val (Sum.inr r.val) (Sum.inl j)) hw
        rw [he, sub_self] at hc
        exact sub_eq_zero.mp ((mul_eq_zero.mp hc.symm).resolve_right hj)
  exact funext (fun r => recover (rootDegree r.val) r rfl)

end ReeF4.Parabolics.RadicalCoordinates
