module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneParabolicExclusion
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.MatchingParabolics

/-!
# The matching parabolic on each original chosen orbit

The original odd-actor residual covers L modulo its two-core, giving the
surjection onto the central quotient of the unchanged orbit component.
Using that map and the original commutator module, the unitary marking
removes all Ree components; the independent Suzuki marking removes PSU₅(4)
and places the residual in the actual full Suzuki-side Ree parabolic.
Residual uniqueness remains explicit. The centered-module contradiction
and final odd-normalizer and Hall conclusions are not asserted here.
Source: Aschbacher--Smith 4.4.11--12, pp.621--622, applied to Section 12.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem sourceOrbit_unitary_five_of_remaining
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hc : UnitaryFiveOrReeComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    s = 2 ∧ UnitaryFiveComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent) := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hdata := chosen_oddActorResidual_cover h D A hsect.1 hsect.2 ho hAV
  let eQ := Classical.choice (D.sourceOrbit_covering_central_quotient h
    ((oddActorResidual_le L A).trans inf_le_left) hdata.1.subset)
  let F := oddActorResidual L A
  let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) :=
    eQ.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
      (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := eQ.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hcase := unitary_five_component_of_remaining_case
    (G := G) (S := D.orbitComponent ⧸ center D.orbitComponent)
    (L := L) (W := D.sourceOrbit) (A := A) (hV ▸ hdata.2.2.1) (hV ▸ D.ne_bot) (hV ▸ hdata.2.1)
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    π hπ hs2 hq
    hc
  exact ⟨unitary_parameter_of_five_component_case
    (G := G) (S := D.orbitComponent ⧸ center D.orbitComponent)
    (L := L) (W := D.sourceOrbit) (A := A)
    (hV ▸ hdata.2.2.1) (hV ▸ D.ne_bot) (hV ▸ hdata.2.1)
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    π hπ hs2 hq hcase,hcase⟩

private theorem sourceOrbit_suzuki_ree_of_remaining
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hc : UnitaryFiveOrReeComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    ReeSuzukiComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent) := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hdata := chosen_oddActorResidual_cover h D A hsect.1 hsect.2 ho hAV
  let eQ := Classical.choice (D.sourceOrbit_covering_central_quotient h
    ((oddActorResidual_le L A).trans inf_le_left) hdata.1.subset)
  let F := oddActorResidual L A
  let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) :=
    eQ.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
      (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := eQ.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  exact ree_suzuki_component_of_remaining_case
    (G := G) (S := D.orbitComponent ⧸ center D.orbitComponent)
    (L := L) (W := D.sourceOrbit) (A := A) (hV ▸ hdata.2.2.1) (hV ▸ D.ne_bot) (hV ▸ hdata.2.1)
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    π hπ hm e hu
    hc

/-- The unitary chosen orbit forces the actual outside component to have
central quotient PSU₅(4), with no Ree row remaining. -/
theorem sourceOrbit_unitary_five_component_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    s = 2 ∧ UnitaryFiveComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent) :=
  D.sourceOrbit_unitary_five_of_remaining h.toHypothesis1221 hV hs2 hq A hA ho
    (D.sourceOrbit_unitary_remaining_component_of_unique h hV hs hs2 hq A hne hA ho hu hout)

/-- The Suzuki chosen orbit forces a Ree component, and the actual residual
quotient representation lands in a conjugate full Suzuki parabolic. -/
theorem sourceOrbit_suzuki_ree_parabolic_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ReeSuzukiComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent) :=
  D.sourceOrbit_suzuki_ree_of_remaining h.toHypothesis1221 hV hm e A hA ho hu
    (D.sourceOrbit_suzuki_remaining_component_of_unique h hV hs hm e A hne hA ho hu hout)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
