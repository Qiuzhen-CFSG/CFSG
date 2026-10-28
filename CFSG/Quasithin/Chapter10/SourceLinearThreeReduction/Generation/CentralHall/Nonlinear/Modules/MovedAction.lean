module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.Preparation
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import Theory.Representation.BinaryConjugationSection.Irreducible
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Faithful recognition actions on the original moved central quotient

All four genuine nonnormal component models have simple two-core quotient.
The original component therefore acts faithfully on W/C_W(L), where
W = [D.fullModule,L]: a trivial quotient action contradicts full commutator
generation and W ≠ 1. Moved-subgroup minimality gives irreducibility of
this exact action, with the literal quotient map retained as coordinates.

The component two-core is also the kernel on the central quotient.
Full commutator generation identifies the kernels on W and W/C_W(L) for
every common normalizer. Crossed geometry then applies this to the entire
M-induced automizer of W, including outer actors. These are the faithful
action inputs for B.4 recognition; no module model is asserted here.
The seed analysis and model classification remain with
qt-d-10-nona5-central-hall-orders.

Source: Aschbacher--Smith 1.2.1(3), 3.2.6 and 10.1.1, pp.504,581,741;
normalizer-kernel argument as used in 10.2.12, p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem simple_of_linear {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] {q : ℕ} (h : ClassicalGroup.IsPSL Q 2 q) : IsSimpleGroup Q := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  have hz : center Q = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨x, hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

include D in
/-- Every model in the genuine nonnormal catalogue has simple two-core quotient. -/
theorem component_simple (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsSimpleGroup (L ⧸ pCore 2 L) := by
  let := D.quasisimple
  cases component_model D hn with
  | linear_even n hn he => exact simple_of_linear he
  | linear_prime p hp ho he => exact simple_of_linear he
  | suzuki m hm he =>
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    exact he.some.isSimpleGroup
  | janko he => exact he.some.isSimpleGroup

private theorem component_le_maximal : L ≤ D.maximalLocal :=
  (le_componentOrbit L T).trans (localOrbit T L).le_normalizer

local instance movedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The central quotient has its literal coordinate map and a faithful component action. -/
theorem exists_moved_quotient_action
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let W := ⁅D.fullModule,L⁆
    let Z := sourceMovedFixed D
    letI := source_original_full_moved_elementary D
    ∃ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L)
        (Additive (W ⧸ Z.subgroupOf W)))
      (c : Representation.BinaryConjugationSection L W Z
        (ρ.comp (QuotientGroup.mk' (pCore 2 L)))),
      Function.Injective ρ ∧
      ∀ w : W, (c.coordinates w).toAdd =
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w) := by
  dsimp only
  let W := ⁅D.fullModule,L⁆
  let Z := sourceMovedFixed D
  let := source_original_full_moved_elementary D
  have hLW : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  have hLZ : L ≤ normalizer (Z : Set G) :=
    (le_inf hLW (L.le_normalizer.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  let q := QuotientGroup.mk' (pCore 2 L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  obtain ⟨ρ,c,hc⟩ := Representation.BinaryConjugationSection.exists_descended_actor
    L W Z (source_full_moved_le_component D) inf_le_left hLW hLZ q hq (by
      intro l hl w hw
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        hl
      have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
        ((component_le_maximal D).trans D.maximalLocal_normalizes_fullModule)
      have hh := source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp) w (hWV hw)
      have he : ⁅(l : G),w⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).mpr hh.symm
      rw [he]
      exact Z.one_mem)
  refine ⟨ρ,c,?_,hc⟩
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D hn
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top.resolve_right
  intro hk
  have hcentral : ⁅W,L⁆ ≤ centralizer (L : Set G) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl w hw
    let w' : W := ⟨l*w*l⁻¹,(mem_normalizer_iff.mp (hLW hl) w).mp hw⟩
    have hi : ρ (q ⟨l,hl⟩) = 1 := MonoidHom.mem_ker.mp (hk ▸ mem_top _)
    have he := c.equivariant ⟨l,hl⟩ ⟨w,hw⟩
    change (c.coordinates w').toAdd = ρ (q ⟨l,hl⟩) (c.coordinates ⟨w,hw⟩).toAdd at he
    rw [hi] at he
    have he' : c.coordinates w' = c.coordinates ⟨w,hw⟩ := he
    have hm : c.coordinates (w' * (⟨w,hw⟩ : W)⁻¹) = 1 := by
      rw [map_mul,map_inv,he',mul_inv_cancel]
    have hz := (c.coordinates_eq_one_iff _).mp hm
    exact hz.2
  have hWC : W ≤ centralizer (L : Set G) :=
    (source_full_moved_eq_commutator D).symm.le.trans hcentral
  have hz : ⁅W,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hWC
  rw [source_full_moved_eq_commutator D] at hz
  exact source_full_moved_ne_bot D hz


/-- The literal central quotient representation, before any choice of model. -/
def movedQuotientAction
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Representation (ZMod 2) (L ⧸ pCore 2 L)
      (Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
        (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆)) :=
  (exists_moved_quotient_action D hn).choose

/-- Its coordinates are on the original moved subgroup and centralizer. -/
def movedQuotientSection
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((movedQuotientAction D hn).comp (QuotientGroup.mk' (pCore 2 L))) :=
  (exists_moved_quotient_action D hn).choose_spec.choose

theorem movedQuotientAction_faithful
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Function.Injective (movedQuotientAction D hn) :=
  (exists_moved_quotient_action D hn).choose_spec.choose_spec.1

/-- No marking changes the literal projection to W/C_W(L). -/
theorem movedQuotientSection_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : (⁅D.fullModule,L⁆ : Subgroup G)) :
    ((movedQuotientSection D hn).coordinates w).toAdd =
      Additive.ofMul (QuotientGroup.mk'
        ((sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆) w) :=
  (exists_moved_quotient_action D hn).choose_spec.choose_spec.2 w

/-- The actual subgroup minimality proves irreducibility of this fixed action. -/
theorem movedQuotientAction_irreducible
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmin : MovedMinimal D) : (movedQuotientAction D hn).IsIrreducible := by
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆)
  let := component_simple D hn
  have : Nontrivial Q := by
    by_contra h
    let : Subsingleton Q := not_nontrivial_iff_subsingleton.mp h
    let : Subsingleton (L ⧸ pCore 2 L) :=
      Function.Injective.subsingleton (movedQuotientAction_faithful D hn)
    exact false_of_nontrivial_of_subsingleton (L ⧸ pCore 2 L)
  apply (Representation.irreducible_comp_surjective_iff (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) _).mp
  apply (movedQuotientSection D hn).irreducible_of_subgroup_minimal
  intro J hJW hLJ
  rcases hmin J hJW hLJ with he | hc
  · exact Or.inl he
  · exact Or.inr (le_inf hJW hc)

/-- The component kernel on the central quotient is its intrinsic two-core. -/
theorem moved_quotient_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    commutatorPreimage L ⁅D.fullModule,L⁆ (sourceMovedFixed D) = L.pCoreIn 2 := by
  have hLZ : L ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)).trans
      (source_original_moved_fixed_normalizer D)
  have he := (movedQuotientSection D hn).action_kernel_map hLZ
  change (((movedQuotientAction D hn).comp (QuotientGroup.mk' (pCore 2 L))).ker).map
    L.subtype = _ at he
  rw [MonoidHom.ker_comp_of_injective _ _ (movedQuotientAction_faithful D hn),
    QuotientGroup.ker_mk'] at he
  exact he.symm

/-- Every common normalizer has the same kernel on W and its central quotient.
No simplicity or faithfulness assumption is imposed on that larger actor. -/
theorem moved_normalizer_quotient_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    commutatorPreimage
      (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (sourceMovedFixed D) =
    (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let H := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hAH : L ≤ H := le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)
  have hker : commutatorPreimage L W (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    rw [moved_quotient_kernel D hn]
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      ((component_le_maximal D).trans D.maximalLocal_normalizes_fullModule)
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le hWV)
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _)
      (commutatorPreimage_le_centralizer_of_fully_moved H L W (sourceMovedFixed D)
        hAH inf_le_left inf_le_right (source_original_moved_fixed_normalizer D)
        inf_le_right (source_full_moved_eq_commutator D) hker)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

/-- The actual local stabilizer has faithful central-quotient action after
crossed centralization has identified which component it normalizes. -/
theorem moved_local_quotient_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (geometry : ModuleGeometry D) :
    commutatorPreimage
      (D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (sourceMovedFixed D) =
    (D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  have hNL := source_original_moved_stabilizer_le_component_normalizer D ht htn
    (geometry.crossed t ht htn)
  let W := ⁅D.fullModule,L⁆
  let H := D.maximalLocal ⊓ normalizer (W : Set G)
  let N := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hHN : H ≤ N := le_inf hNL inf_le_right
  have hHZ : H ≤ normalizer (sourceMovedFixed D : Set G) :=
    hHN.trans (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage H W (sourceMovedFixed D) ≤
      commutatorPreimage N W (sourceMovedFixed D) :=
    le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans hHN)
      (commutator_commutatorPreimage_le _ _ _ hHZ)
  rw [moved_normalizer_quotient_kernel D hn] at hk
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _) (hk.trans inf_le_right)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

open ChapterE Representation.BinaryOffender in
/-- The entire original local automizer embeds in the linear normalizer of
this same component action, with its literal coordinate formula. -/
theorem exists_moved_local_normalizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (geometry : ModuleGeometry D) :
    let W := ⁅D.fullModule,L⁆
    let Q := Additive (W ⧸ (sourceMovedFixed D).subgroupOf W)
    ∃ (τ : Representation (ZMod 2) (inducedAutomizer W D.maximalLocal) Q)
      (f : inducedAutomizer W D.maximalLocal →* linearNormalizer (movedQuotientAction D hn)),
      Function.Injective f ∧
      (∀ a v, normalizerRepresentation (movedQuotientAction D hn) (f a) v = τ a v) ∧
      (∀ (n : (D.maximalLocal ⊓ normalizer (W : Set G) : Subgroup G)) (w : W),
        τ (localNormalizerAction W D.maximalLocal n)
            ((movedQuotientSection D hn).coordinates w).toAdd =
          ((movedQuotientSection D hn).coordinates ⟨(n : G)*w*(n : G)⁻¹,
            (mem_normalizer_iff.mp n.property.2 w).mp w.property⟩).toAdd) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  have hNL := source_original_moved_stabilizer_le_component_normalizer D ht htn
    (geometry.crossed t ht htn)
  have hNZ := (le_inf hNL (show D.maximalLocal ⊓
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) from inf_le_right)).trans
    (source_original_moved_fixed_normalizer D)
  apply exists_local_section_normalizer L ⁅D.fullModule,L⁆ (sourceMovedFixed D) D.maximalLocal
    (movedQuotientAction D hn) (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) (movedQuotientSection D hn)
    (component_le_maximal D) hNL hNZ
  rw [moved_local_quotient_kernel D hn geometry]
  exact inf_le_right

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
