module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ComponentInputs

/-!
# The complete C.2.7 inputs for a single contrary component

The normal closure K is normal in H. Consequently the source radical
R=O₂(XU) normalizes K directly. The actual CPU theorem supplies radicality,
characteristic control and the normal-closure Sylow condition; the outside
Y-factor and H=KU prevent K from lying in M₁. Characteristic two transports
through the literal subgroup inclusion.

Thus C.2.7 applies to K itself, with no embedding witness or quotient-model
restriction. In particular this covers the retained Held case of the adequate
intrinsic reduction. The full earlier C.2.7 remains its source owner's input;
no output of that theorem is part of the hypothesis construction.
Source: Aschbacher--Smith, C.2.2--7 and 15.4.20, printed pp.144--147,1164.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
open BlockSieve BlockSieve.ExchangedCases BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- A normal single C-component needs no split-complement witness to satisfy
every hypothesis of the complete C.2.7. -/
theorem single_component_hypotheses (hG : IsSimpleQTKE κ G)
    (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K)) :
    ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K.subgroupOf H) := by
  let R := sourceRadical d U
  let M := H ⊓ d.M₁
  have hUH : U ≤ H := h.placed.sylow_image ▸ map_subtype_le (h.placed.sylow : Subgroup H)
  have hUM : U ≤ d.M₁ := h.placed.upper.le.trans h.placed.T_normalizes
  obtain ⟨hsq, hne, hRH, hRp, hrad, hcontrol, hsylow⟩ :=
    contrary_pushing_up_inputs hG d.T h.placed.overgroup.1 h.placed.whole_le
      h.placed.upper.le h.placed.upper_index h.placed.T_normalizes
      h.placed.core_nontrivial unique h.placed.sylow h.placed.sylow_image
  change R ≤ H at hRH
  change R ≠ ⊥ at hne
  have hRne : R.subgroupOf H ≠ ⊥ := by
    intro hb
    have he := congrArg (Subgroup.map H.subtype) hb
    exact hne (by simpa only [map_subgroupOf_eq_of_le hRH, Subgroup.map_bot] using he)
  have hsylow' : Chapter1.IsSylowIn 2 (R.subgroupOf H)
      (conjugateModule (M.subgroupOf H) (R.subgroupOf H)) := by
    apply (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hRH, conjugateModule_subgroupOf_map inf_le_left hRH]
    exact hsylow
  have hcpu : ComponentInputs.PushingUpHypotheses κ (R.subgroupOf H) (M.subgroupOf H) :=
    ⟨hsq, hRne, hRp.comap_subtype, hrad, hcontrol, hsylow'⟩
  have hKH : K ≤ H := h.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  have hKn : (K.subgroupOf H).Normal :=
    h.closure ▸ EmbeddingReduction.normalClosureIn_normal _ _
  have hHK : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  obtain ⟨_, _, hKF⟩ := source_core_inputs hKH hHK h.placed.sylow
    h.placed.sylow_image h.generation h.characteristic_two
  let eqv := (subgroupOfEquivOfLe hKH).symm
  let _ := hq
  have hKq : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ eqv (pCore_map_iso 2 eqv))
  have houtside : ¬ K ≤ M := by
    intro hKM
    have hHM : H ≤ d.M₁ := h.generation ▸ sup_le (hKM.trans inf_le_right) hUM
    exact h.placed.outside ((d.Y_le_I i j).trans (h.placed.overgroup.2.trans hHM))
  have hc : ComponentInputs.Hypotheses κ (R.subgroupOf H) (M.subgroupOf H)
      (K.subgroupOf H) := by
    refine ⟨hcpu, hK, hKq, hKF, ?_, ?_⟩
    · intro hle
      apply houtside
      have hm := map_mono (f := H.subtype) hle
      simpa only [map_subgroupOf_eq_of_le hKH,
        map_subgroupOf_eq_of_le (show M ≤ H from inf_le_left)] using hm
    · intro r hr
      rw [← subgroupOf_normalizer_eq hKH]
      exact hHK (hRH hr)
  simpa only [M, inf_subgroupOf_left] using componentHypotheses_of_source hc

/-- C.2.7 is applied on the actual single component, retaining its complete
kernel, offender and eight-case output on the literal local star quotient. -/
theorem single_component_source_cases (c27 : UniversalC27.{u})
    (hG : IsSimpleQTKE κ G) (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K)) :
    CoreConclusion (K.subgroupOf H) ((sourceRadical d U).subgroupOf H) ∧
      OffenderConclusion (K.subgroupOf H) ((sourceRadical d U).subgroupOf H) ∧
      Alternatives κ (K.subgroupOf H) ((sourceRadical d U).subgroupOf H)
        (d.M₁.subgroupOf H) :=
  c27 κ H _ _ _ (single_component_hypotheses hG h unique hK hq)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
