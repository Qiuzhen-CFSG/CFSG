module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOddControl
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.RankOneSections.Exclusion

/-!
# Removing the outer-section premise from both normalized rank-one reductions

The full Theorem B model inspection excludes the actual unitary and Suzuki
central quotient of the chosen orbit from every component outer group.
Applying it to each component of the literal odd normalizer removes `hno`
from both checked rank-two-component reductions. The residual-uniqueness
premise remains explicit for the ambient pushing-up assembly; no stronger
quasithin hypothesis or model callback is introduced.

Source: Aschbacher--Smith 4.4.10--11, printed p.621, applied to the chosen
module in Section 12.2. The quotient is by the center of the actual cover.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual unitary orbit quotient is no section of the outer group of
any B-model central cover, hence of any component of an odd normalizer. -/
theorem sourceOrbit_unitary_no_outer_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    {K : Type v} [Group K] [Finite K] [IsQuasisimple K]
    (hK : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (U : Subgroup (MulAut.Outer K))
    (f : U →* (D.orbitComponent ⧸ center D.orbitComponent)) : ¬ Function.Surjective f := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  exact cover_no_target_section hK
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    (.inl ⟨s,hs2,hq⟩) U f

/-- The independent actual Suzuki marking supplies the same complete
outer-section exclusion, retaining the quasisimple cover K. -/
theorem sourceOrbit_suzuki_no_outer_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {K : Type v} [Group K] [Finite K] [IsQuasisimple K]
    (hK : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (U : Subgroup (MulAut.Outer K))
    (f : U →* (D.orbitComponent ⧸ center D.orbitComponent)) : ¬ Function.Surjective f := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  exact cover_no_target_section hK
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    (.inr ⟨m,hm,⟨e⟩⟩) U f

/-- The unitary rank-two-component reduction with the complete outer-section
premise discharged. Residual uniqueness is the remaining ambient input. -/
theorem sourceOrbit_unitary_rankTwo_component_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) := by
  apply D.sourceOrbit_unitary_rankTwo_component_of_unique_no_outer
    h hV hs hs2 hq A hne hA ho hu hout
  intro K hcomp hK U f
  let : IsQuasisimple K := hcomp.2
  exact D.sourceOrbit_unitary_no_outer_section h.toHypothesis1221 hs2 hq hK U f

/-- The Suzuki reduction with the exact same residual-uniqueness premise
and no outstanding model or outer-automorphism input. -/
theorem sourceOrbit_suzuki_rankTwo_component_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) := by
  apply D.sourceOrbit_suzuki_rankTwo_component_of_unique_no_outer
    h hV hs hm e A hne hA ho hu hout
  intro K hcomp hK U f
  let : IsQuasisimple K := hcomp.2
  exact D.sourceOrbit_suzuki_no_outer_section h.toHypothesis1221 hm e hK U f

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
