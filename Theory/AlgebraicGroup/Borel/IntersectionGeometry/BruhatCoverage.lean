module

public import Theory.AlgebraicGroup.BNPair.SimpleLiftCoverage
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Normalizer
public import Theory.AlgebraicGroup.Reductive.Defs

/-!
Conditional assembly of B–N–B coverage for a Borel–torus pair.

GLS3, Theorem 1.11.3, and Borel, §14.15, provide two geometric ingredients:
generation by the Borel and torus normalizer, and simple-reflection lifts
with the two-cell exchange law. The group-theoretic closure argument then
gives an explicit factorization. These ingredients remain explicit hypotheses
here; this module does not yet assert their existence for reductive groups.

This is the coverage needed for the common-torus application in Borel, §14.13.
No opposite Borel, normalizer quotient, or cell-uniqueness assertion is needed
in the conditional assembly.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] {G : Variety k} [AlgebraicGroup G]

/-- Assemble coverage from ambient generation and the geometric simple-lift
exchange package. The existence of that package is a separate prerequisite;
this conditional theorem is not the reductive Bruhat theorem. -/
public theorem exists_bruhat_factorization_of_generation_and_simple_lifts
    (B T : ClosedSubgroup G) (hTB : T ≤ B)
    (hBN : Subgroup.closure
      ((B.toSubgroup : Set (Variety.Point G)) ∪
        (T.normalizer.toSubgroup : Set (Variety.Point G))) = ⊤)
    (hlifts : ∃ S : Set (Variety.Point G),
      Subgroup.closure ((T.toSubgroup : Set (Variety.Point G)) ∪ S) =
          T.normalizer.toSubgroup ∧
        (∀ s ∈ S, s * s ∈ T.toSubgroup) ∧
        BruhatGeneration.SimpleLiftExchange B.toSubgroup T.normalizer.toSubgroup S)
    (g : Variety.Point G) :
    ∃ b n c : Variety.Point G, b ∈ B.toSubgroup ∧
      n ∈ T.normalizer.toSubgroup ∧ c ∈ B.toSubgroup ∧ g = b * n * c := by
  obtain ⟨S, hN, hsquare, hexchange⟩ := hlifts
  have hSN : S ⊆ (T.normalizer.toSubgroup : Set (Variety.Point G)) := by
    intro s hs
    rw [← hN]
    exact Subgroup.subset_closure (Or.inr hs)
  have hNle : T.normalizer.toSubgroup ≤
      Subgroup.closure ((B.toSubgroup : Set (Variety.Point G)) ∪ S) := by
    rw [← hN]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_closure (Or.inl (hTB hx))
    · exact Subgroup.subset_closure (Or.inr hx)
  exact BruhatGeneration.exists_factorization_of_simpleLiftExchange
    B.toSubgroup T.normalizer.toSubgroup S hBN hNle hSN
    (fun s hs => hTB (hsquare s hs)) hexchange g

end Theory.AlgebraicGroup.BorelIntersectionGeometry
