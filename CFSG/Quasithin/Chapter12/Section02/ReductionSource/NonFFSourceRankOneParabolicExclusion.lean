module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOuterSections
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.RankTwoResidualExclusions

/-!
# Linear-Levi exclusions on both original chosen rank-one modules

The inclusion-induced quotient of the fixed residual is the central quotient
of the original orbit component. Its unitary or Suzuki marking supplies the
nonidentity two-square. The actual residual and unchanged chosen module then
exclude the linear-Levi component parabolics and all small endpoints.

The output still requires residual uniqueness and retains the unresolved
PSU₅(4) and Ree component rows. It does not assert the final normalizer
or Hall-faithfulness conclusions.
Source: Aschbacher--Smith 4.4.11--12, pp.621--622, on the original Section 12.2
chosen orbit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem sourceOrbit_unitaryFiveOrRee_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hexp : ¬ ∀ P : Subgroup (D.orbitComponent ⧸ center D.orbitComponent),
      IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (hc : RankTwoComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    UnitaryFiveOrReeComponentCase L D.sourceOrbit A
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
  let e := Classical.choice (D.sourceOrbit_covering_central_quotient h
    ((oddActorResidual_le L A).trans inf_le_left) hdata.1.subset)
  let F := oddActorResidual L A
  let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
      (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  exact unitary_five_or_ree_component_of_rankTwo_case
    (G := G) (S := D.orbitComponent ⧸ center D.orbitComponent)
    (L := L) (W := D.sourceOrbit) (A := A) (hV ▸ hdata.2.2.1)
    (hV ▸ D.ne_bot) (hV ▸ hdata.2.1)
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    hexp π hπ hc

/-- Both the unitary family marking and the original residual embedding are
used to remove all five linear-Levi component rows. -/
theorem sourceOrbit_unitary_remaining_component_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    UnitaryFiveOrReeComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent) :=
  D.sourceOrbit_unitaryFiveOrRee_component h.toHypothesis1221 hV A hA ho
    (unitary_not_two_exponent hs2 hq)
    (D.sourceOrbit_unitary_rankTwo_component_of_unique h hV hs hs2 hq A hne hA ho hu hout)

/-- The independent Suzuki marking gives the same exclusion on its actual
fixed residual and original orbit, with uniqueness still explicit. -/
theorem sourceOrbit_suzuki_remaining_component_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    UnitaryFiveOrReeComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent) :=
  D.sourceOrbit_unitaryFiveOrRee_component h.toHypothesis1221 hV A hA ho
    (suzuki_not_two_exponent hm e)
    (D.sourceOrbit_suzuki_rankTwo_component_of_unique h hV hs hm e A hne hA ho hu hout)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
