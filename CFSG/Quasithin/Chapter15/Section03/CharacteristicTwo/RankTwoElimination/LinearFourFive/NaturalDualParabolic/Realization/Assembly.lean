module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.Ambient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Selection

/-!
# Conditional assembly of the natural-dual parabolic MS construction

The ambient construction uses the literal residual O²(P) and the original
Sylow subgroup S. The lemmas below discharge every BinaryMS.Input field
from an S-invariant point parabolic with nontrivial projected action,
then identify the mapped commutator core with the intrinsic core of O²(P).
The exact 15.3.11(12) implication is invoked only after transferring its
action premise from Z_L to V.

These are conditional assembly lemmas. Existence of a point with the
projected noncentrality, its S-invariance, and the comparison
[O₂(O²(P)),O²(P)] = [O₂(P),P] are still mathematical construction
obligations. In particular no source theorem or existence of MSData is
claimed without these calculations. Both choices of Hypothesis 15.3.10
are retained, and no rank-one condition on Y_C is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130; C.1.31–34, printed pp.135–137.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization

universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {d : LocalData G} {L I : Subgroup G}

/-- The exact remaining local calculations produce all intrinsic MS hypotheses.
This is an assembly implication; projected noncentrality and S-invariance must be constructed. -/
theorem exists_binaryInput_of_point_calculations [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) (plane : PlaneParabolic d L h.model)
    {x : Space 4} (hx : x ≠ 0) (hLI : L ≤ I)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hSL : Chapter1.IsSylowIn 2 (d.S ⊓ L) L)
    (hSP : d.S ⊓ L ≤ point h x)
    (hn : d.S ≤ normalizer (point h x : Set G))
    (hf : HasCharacteristicTwo I) (hq : IsSQTK κ I)
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L)
    (hact : ⁅projectedCenter d L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)⁆ ≠ ⊥)
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal) :
    Nonempty (ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) := by
  have he := residualOvergroup_eq_join h x hSL hSP
  have hPJ : point h x ≤ residualOvergroup h x := he ▸ le_sup_left
  have hc := residualComponent_isCComponent h hx hPJ hn
  have hs := residualOvergroup_sylow h x hLI hS
  obtain ⟨e⟩ := residualComponent_quotient h hx
  refine ⟨{
    sqtk := residualOvergroup_sqtk h x hLI (Chapter1.isSylowIn_iff.mp hS).2.1 hq
    fitting := residualOvergroup_fitting h x hLI hS hf
    product := residualComponent_product h x hn
    component := hc
    radical := sylowPart_oddIndexRadical h x hs hc
    characteristic := ?_
    quotientEquiv := e
  }⟩
  apply sylowPart_characteristic h x
  rw [he]
  exact characteristic_exclusion_of_projected_action hsplit (point_le h x)
    ((point_le h x).trans hLI) (point_not_le_M h plane hx) hact h11

/-- The ambient commutator core is the embedded intrinsic commutator core of O²(P).
The further comparison with [O₂(P),P] is a separate local calculation. -/
theorem mapped_commutatorCore (h : NaturalDual d L) (x : Space 4)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    (ChapterC.BinaryMS.commutatorCore (residualComponent h x)).map
        (residualOvergroup h x).subtype =
      ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆ := by
  let E := Stellmacher.twoResidualAmbient (point h x)
  let J := residualOvergroup h x
  let D := residualComponent h x
  let e : D ≃* E := subgroupOfEquivOfLe le_sup_left
  have hcore : (pCore 2 D).map (J.subtype.comp D.subtype) = E.pCoreIn 2 := by
    change (pCore 2 D).map (E.subtype.comp e.toMonoidHom) = _
    rw [← map_map, pCore_map_iso]
    rfl
  have hall : (⊤ : Subgroup D).map (J.subtype.comp D.subtype) = E := by
    rw [← map_map, ← MonoidHom.range_eq_map, range_subtype]
    exact map_subgroupOf_eq_of_le le_sup_left
  rw [input.commutatorCore_eq_internal, map_map, map_commutator, hcore, hall]

/-- Conditional final packaging, with all unresolved point calculations displayed.
Its caller must prove the action, invariance, and intrinsic core equality. -/
theorem exists_msData_of_point_calculations [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) (plane : PlaneParabolic d L h.model)
    {x : Space 4} (hx : x ≠ 0) (hLI : L ≤ I)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hSL : Chapter1.IsSylowIn 2 (d.S ⊓ L) L)
    (hSP : d.S ⊓ L ≤ point h x)
    (hn : d.S ≤ normalizer (point h x : Set G))
    (hf : HasCharacteristicTwo I) (hq : IsSQTK κ I)
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L)
    (hact : ⁅projectedCenter d L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)⁆ ≠ ⊥)
    (hcore : ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
      Stellmacher.twoResidualAmbient (point h x)⁆ = coreCommutator (point h x))
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal) :
    Nonempty (MSData κ h x) := by
  obtain ⟨input⟩ := exists_binaryInput_of_point_calculations h plane hx hLI hS hSL hSP
    hn hf hq hsplit hact h11
  exact ⟨{
    input := input
    sylow := residualOvergroup_sylow h x hLI hS
    overgroup_eq := residualOvergroup_eq_join h x hSL hSP
    core_eq := (mapped_commutatorCore h x input).trans hcore
  }⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization

end
