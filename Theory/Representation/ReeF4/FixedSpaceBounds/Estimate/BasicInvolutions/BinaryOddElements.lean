module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.SourceData
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.MiddlePairs
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusData
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle

/-!
# Basic-factor odd displacement from the binary Ree torus spectrum

The zero basic weight has trivial action; irreducibility forces its space to
have dimension one, excluding the dimension-at-least-26 input. Both larger
basic weights have displacement at least twenty on every nonidentity coroot
torus element by the disjoint weight-pair argument. For the end-node weight,
the twenty moving short characters supplied by `BinaryOddTorusCoverage`
give the same bound. Conjugacy uses the actual coefficient embedding.

The resulting theorem has exactly `BinaryOddDisplacement` as conclusion and
feeds the existing basic-involution assembly. It remains conditional on the
binary torus placement and spectrum; that group calculation is not proved by
this module or by the source's preliminary degree exclusion.

Source: Guralnick--Malle, Classification of 2F-modules II, Lemmas 8.7--8.8,
internal pp.57--58; GLS3, Sections 1.14 and 2.8.
-/

public section

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
variable {F : Type*} [Field F] [IsAlgClosed F]

theorem finrank_eq_one_of_trivial (B : AlgebraicFactor F) (hB : ¬ B.IsNontrivial) :
    Module.finrank F B.Space = 1 := by
  have ha : ∀ g, B.action.action g = 1 := by
    simpa [AlgebraicFactor.IsNontrivial] using hB
  obtain ⟨v, hv⟩ := exists_ne (0 : B.Space)
  have hinv : IsInvariantSubmodule B.action (Submodule.span F {v}) := by
    intro g w hw
    simpa [ha] using hw
  have ht : Submodule.span F {v} = ⊤ := by
    rcases B.irreducible.2 _ hinv with hb | ht
    · have hm : v ∈ Submodule.span F {v} := Submodule.subset_span (Set.mem_singleton v)
      rw [hb] at hm
      exact (hv (by simpa using hm)).elim
    · exact ht
  have hd := finrank_span_singleton (K := F) hv
  rw [ht] at hd
  simpa using hd

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions
open ReeF4.BinaryDegree.ExceptionalTensor
open BinaryOddElements
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The exact binary odd-element bound follows from the torus placement and
short-root spectrum. The zero and both larger basic weights are discharged here. -/
theorem binaryOddDisplacement_of_torusCoverage (hgeometry : BinaryOddTorusCoverage F) :
    BinaryOddDisplacement F := by
  intro B hB hd f x hx
  obtain ⟨c, t, he, ht⟩ := hgeometry f x hx
  rw [binary_fixedCodim_eq_torus_rank B f x c t he]
  obtain ⟨⟨a, b⟩, hw⟩ := B.isExceptionalBasic_iff.mp hB
  fin_cases a <;> fin_cases b
  · have hdim := finrank_eq_one_of_trivial B
      (zero_basicHighestWeight_not_isNontrivial B hw)
    omega
  · exact end_torus_displacement B hw t ht
  · exact middle_torus_displacement B 0 hw t ht.ne_one
  · exact middle_torus_displacement B 1 hw t ht.ne_one

end ReeF4.FixedSpaceEstimate.BasicInvolutions
