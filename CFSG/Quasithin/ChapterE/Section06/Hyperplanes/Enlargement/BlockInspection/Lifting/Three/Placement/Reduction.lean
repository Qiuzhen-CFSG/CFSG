module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.SymplecticParameters
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection

/-!
# Componentwise reduction of the solvable block placement

The layer centralizer is tested against the actual components of the relative
ambient group. Mapping these components into G preserves their relative
subnormality and ordinary quasisimplicity. Thus failure of layer-centralizing
placement is witnessed by one noncommuting ordinary component.

Hyperplane characteristic two forces every component of C_G(A), for A of
corank two, to have fixed space exactly A. The complete E.6.8 alternatives,
E.6.18 and E.6.21 then leave the parameter-four Borel models and the two
symplectic parameters. This reduction does not presume that the block lies
in the component. That mixed-group action question remains to be proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8 and
E.6.23, printed pp.247–248 and 254–255 (PDF pp.258–259 and 265–266).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
open ComponentBalance Components

variable {G : Type*} [Group G]

/-- Centralizing the actual layer is equivalent to centralizing each ordinary
component, with both the layer centralizer and the components mapped into G. -/
theorem le_layerKernel_iff {H L : Subgroup G} (hLH : L ≤ H) :
    L ≤ layerKernel H ↔ ∀ X : Subgroup H, IsComponent H X →
      ⁅L, X.map H.subtype⁆ = ⊥ := by
  constructor
  · intro hl X hx
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro l hll x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hl hll
    have hXE : X ≤ componentLayer H := le_sSup hx
    exact congrArg H.subtype (hz y (hXE hy))
  · intro hc l hl
    refine ⟨⟨l, hLH hl⟩, ?_, rfl⟩
    have hEL : componentLayer H ≤ centralizer (L.subgroupOf H : Set H) := by
      apply sSup_le
      intro X hx x hxx y hyy
      have hh := commutator_eq_bot_iff_le_centralizer.mp (hc X hx) hyy x
        (mem_map_of_mem H.subtype hxx)
      exact Subtype.ext hh.symm
    exact le_centralizer_iff.mp hEL hl

/-- A failure to centralize the relative layer detects an actual component
of the centralizer, rather than a C-component or an ambient-normal subgroup. -/
theorem exists_noncommuting_component {A L : Subgroup G}
    (hLH : L ≤ centralizer (A : Set G))
    (hn : ¬ L ≤ layerKernel (centralizer (A : Set G))) :
    ∃ X : Subgroup G, CentralizerComponent A X ∧ ⁅L, X⁆ ≠ ⊥ := by
  classical
  obtain ⟨X, hx⟩ := not_forall.mp (mt (le_layerKernel_iff hLH).mpr hn)
  obtain ⟨hX, hc⟩ := Classical.not_imp.mp hx
  refine ⟨X.map (centralizer (A : Set G)).subtype, ⟨map_subtype_le _, ?_⟩, hc⟩
  change IsComponent (centralizer (A : Set G))
    ((X.map (centralizer (A : Set G)).subtype).comap (centralizer (A : Set G)).subtype)
  rwa [comap_map_eq_self_of_injective (centralizer (A : Set G)).subtype_injective]

/-- Solvability here follows from the literal quotient of order three.
No identification of the whole block with A₄ is assumed. -/
theorem alternating_three_solvable {D : Type*} [Group D]
    (h : ChapterC.IsAlternatingBlock D 3) : Group.IsSolvable D := by
  let := h.2.1.finite
  obtain ⟨e⟩ := h.2.2.quotient_iso
  have hc : Nat.card (D ⧸ pCore 2 D) = 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  let := (IsPGroup.of_card (p := 3) (n := 1) (by simpa only [pow_one] using hc)).isNilpotent
  let : Group.IsNilpotent (pCore 2 D) := pCore_isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 D)).mpr
    ⟨inferInstance, inferInstance⟩

variable [Finite G] {M V : Subgroup G}

/-- All components of the corank-two centralizer are reduced simultaneously.
There is no hypothesis placing the original small block in X. -/
theorem component_models [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (h8 : OddObstruction.EarlierComponentAlternatives M V
      (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    {A X : Subgroup G} (hA : A ∈ obstructionFamily M V)
    (hc : subgroupCorank V A = 2) (hX : CentralizerComponent A X) :
    V ⊓ centralizer (X : Set G) = A ∧
      (BorelAlternative M V A X 2 ∨
        SymplecticAlternative M V A X 1 ∨
          (SymplecticAlternative M V A X 2 ∧
            MaximalParabolic X (X ⊓ M) ∧ SymplecticRootAction X V 2)) := by
  obtain ⟨he, ha⟩ := h8 A hA X hX
  have hr := ComponentCase.component_actionCorank_two h hchar hA.1 hc hX he
  refine ⟨ComponentCase.component_fixedSpace_eq h hchar hA.1 hc hX he, ?_⟩
  rcases ComponentCase.remaining_alternatives h18 h21 hA hc hX hr ha with b | ⟨n, b⟩
  · exact Or.inl b
  · rcases ComponentCase.symplectic_parameters hr b with hn | ⟨hn, hp, ha⟩
    · exact Or.inr (Or.inl (hn ▸ b))
    · exact Or.inr (Or.inr ⟨hn ▸ b, hp, ha⟩)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
