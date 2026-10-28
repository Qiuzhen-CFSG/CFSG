module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitCubic
public import Theory.GroupTheory.GeneralizedFitting.NormalComponentCentralizer
public import Theory.Representation.BinaryOffender.CubicOrbitSection

/-!
# Excluding faithful small cubic actors on the residual component

Transfer the original elementary cubic actor to a previously constructed
homogeneous orbit quotient. Its proved strict lower bound excludes
faithfulness on the PSL₃(4) component. Thus the actor has nontrivial
intersection with the component centralizer. Applying the generalized
Fitting argument to this intersection selects a component moved by that
intersection, and hence by the original actor.

The Chapter 12 application supplies both the orbit and its strict bound
from the original projection and diagram action. Middle-layer fixedness
and exclusion of the three-prime component remain source obligations.
Source: Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
variable {X W : Type*} [Group X] [Finite X]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem small_cubic_residual_centralizer_ne_bot
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [IsQuasisimple K]
    (hs : HasFaithfulHomogeneousOrbitSection ρ K P)
    (hb : ResidualOrbitCubicBound ρ K P)
    {E : Subgroup X} (hEP : E ≤ P) (hE : IsElementaryTwo E)
    (hc : IsCubic ρ E) (hr : actionRatio ρ E ≤ 2) :
    E ⊓ centralizer (K : Set X) ≠ ⊥ := by
  intro hz
  obtain ⟨I,hI,_⟩ := hs
  have hd : Disjoint E (centralizer (K : Set X)) := disjoint_iff.mpr hz
  exact not_le_of_gt (hb I hI)
    ((orbitSection_cubicRatio_le_actionRatio ρ hI hEP hE hc hd).trans hr)

theorem small_cubic_moves_centralizer_component
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X)
    [K.Normal] [IsQuasisimple K] (hcore : pCore 2 X = ⊥)
    (hs : HasFaithfulHomogeneousOrbitSection ρ K P)
    (hb : ResidualOrbitCubicBound ρ K P)
    {E : Subgroup X} (hEP : E ≤ P) (hE : IsElementaryTwo E)
    (hc : IsCubic ρ E) (hr : actionRatio ρ E ≤ 2)
    (hF : (fittingSubgroup (centralizer (K : Set X))).map
      (centralizer (K : Set X)).subtype ≤ centralizer (E : Set X)) :
    let Z := centralizer (K : Set X)
    E ⊓ Z ≠ ⊥ ∧ ∃ J : Subgroup Z,
      IsComponent Z J ∧ IsComponent X (J.map Z.subtype) ∧
      ⁅J.map Z.subtype,E ⊓ Z⁆ ≠ ⊥ ∧ ⁅J.map Z.subtype,E⁆ ≠ ⊥ := by
  let Z := centralizer (K : Set X)
  have hn := small_cubic_residual_centralizer_ne_bot ρ K P hs hb hEP hE hc hr
  let : IsElementaryAbelian 2 E := hE.2
  have hp : IsPGroup 2 (E ⊓ Z : Subgroup X) :=
    (IsElementaryAbelian.isPGroup 2 E).to_le inf_le_left
  have hFC : (fittingSubgroup Z).map Z.subtype ≤ centralizer (E ⊓ Z : Set X) :=
    hF.trans (centralizer_le inf_le_left)
  have hzero : ⁅K,E ⊓ Z⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  obtain hm | ⟨J,hJ,hJX,hmove⟩ :=
    moves_normal_component_or_centralizer_component K (E ⊓ Z) hp hn hcore hFC
  · exact (hm hzero).elim
  · refine ⟨hn,J,hJ,hJX,hmove,?_⟩
    intro he
    exact hmove (bot_unique ((commutator_mono le_rfl inf_le_left).trans_eq he))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
