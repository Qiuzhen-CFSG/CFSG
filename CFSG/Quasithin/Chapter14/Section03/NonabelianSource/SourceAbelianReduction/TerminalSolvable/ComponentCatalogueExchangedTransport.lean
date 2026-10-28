module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogue
public import Theory.Representation.NormalComponentConstituents
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
/-!
# Transport of recognized exchanged component models

If the ambient conjugate orbit of a component is isomorphic to A7, simplicity
makes its nontrivial subnormal component equal to the orbit. The component
is therefore normal in the actual ambient group, as required by the large
row of `ComponentImageCases`.

The source application combines this normality calculation with the existing
small-actor local lift and two-core quotient transport. It also accepts the
paired A5 alternative through the small row. Both concrete model
identifications remain explicit inputs: this module does not classify the
exchanged action.

Source: Aschbacher--Smith G.10.15(2)(III), G.11.6 and 14.3.15, printed
pp.361--363,365--366,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
private theorem component_eq_orbit_of_simple {D : Type*} [Group D]
    {L : Subgroup D} (hL : IsComponent D L)
    [IsSimpleGroup (componentOrbit L ⊤)] : L = componentOrbit L ⊤ := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hne : L ≠ ⊥ := (nontrivial_iff_ne_bot L).mp inferInstance
  have hLH := le_componentOrbit L (⊤ : Subgroup D)
  rcases hL.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup (componentOrbit L ⊤)) with hb | ht
  · have he := congrArg (Subgroup.map (componentOrbit L ⊤).subtype) hb
    rw [map_subgroupOf_eq_of_le hLH, Subgroup.map_bot] at he
    exact (hne he).elim
  · exact le_antisymm hLH (subgroupOf_eq_top.mp ht)

/-- An actual A7 identification of the orbit recognizes the original
component and proves its normality in the full dotted group. -/
theorem component_image_cases_of_orbit_alternating_seven
    {D : Type*} [Group D] {L : Subgroup D} (hL : IsComponent D L)
    (e : componentOrbit L ⊤ ≃* alternatingGroup (Fin 7)) :
    ComponentImageCases L := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (componentOrbit L ⊤) := e.isSimpleGroup
  have heq := component_eq_orbit_of_simple hL
  have hn : L.Normal := heq.symm ▸ componentOrbit_top_normal L
  exact Or.inl ⟨hn, Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr heq).trans e⟩)⟩

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative

/-- Conditional source application of the two exchanged models. Recognition
of the orbit as A7 supplies ambient normality; recognition of the component as
A5 enters the small row directly. The actual model isomorphisms remain inputs. -/
theorem source_component_catalogue_of_exchanged_models
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hmove : ⁅L, F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hmodels : Nonempty (componentOrbit L ⊤ ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 5))) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  apply source_component_catalogue_of_small_actor_image
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp hm hL hmove
  rcases hmodels with eH | eL
  · exact component_image_cases_of_orbit_alternating_seven hL (Classical.choice eH)
  · exact Or.inr (Or.inl (Or.inl eL))
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
