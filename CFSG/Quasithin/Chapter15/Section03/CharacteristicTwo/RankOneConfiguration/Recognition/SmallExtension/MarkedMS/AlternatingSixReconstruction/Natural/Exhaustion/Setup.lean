module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Inputs
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Reduction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSeed
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Characteristic reduction of the original alternating-six pair

Choose the minimum characteristic subgroup of the original odd-index radical
containing the two-core of its product with the component. The product is
normal in the original group, inherits characteristic two and MS3, and retains
the entire commutator core through its literal inclusion. The initial moved
central-omega subgroup lies in the unchanged component and hence in every
such replacement. No four-dimensional complement or Sylow radical is used.

Source: MS93 Section 7, printed pp.932--933; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
namespace AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

/-- The original moved layer, including its possible central fixed line. -/
abbrev initialMoved (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  ⁅centralOmega L R, L.subgroupOf (L ⊔ R)⁆

/-- Replacement refers to the original radical, without a Sylow assumption. -/
abbrev Replacement (L R : Subgroup G) :=
  CharacteristicReduction (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R))

omit [Finite G] in
theorem relative_sup : K ⊔ T = ⊤ :=
  (codisjoint_subgroupOf_sup L R).eq_top

/-- The minimum exists from MS2(a)'s original two-core containment. -/
def replacement : Replacement L R :=
  Classical.choice (NaturalSixControl.SymplecticSetup.exists_reduction
    (relative_sup (L := L) (R := R)) h.relative_radical.twoCore_le)

variable (d : Replacement L R)

include h in
theorem replacement_normal : d.overgroup.Normal :=
  NaturalSixControl.SymplecticSetup.Reduction.overgroup_normal d h.relative_normal relative_sup

include h in
theorem replacement_core :
    pCore 2 d.overgroup = (pCore 2 M).comap d.overgroup.subtype :=
  NaturalSixControl.SymplecticSetup.Reduction.core_eq d h.relative_normal relative_sup

include h in
/-- Characteristic two survives restriction to this normal overgroup. -/
theorem replacement_self_centralizing :
    centralizer (pCore 2 d.overgroup : Set d.overgroup) ≤ pCore 2 d.overgroup := by
  let := replacement_normal h d
  exact normal_core_selfCentralizing h.relative_self_centralizing d.overgroup

include h in
omit [Finite G] in
theorem replacement_radical_isPGroup : IsPGroup 2 d.radical :=
  ((h.relative_radical.isPGroup.to_subgroup d.subgroup).map (T).subtype).comap_subtype

include h in
theorem replacement_core_le_radical : pCore 2 d.overgroup ≤ d.radical :=
  NaturalSixControl.SymplecticSetup.Reduction.core_le_radical d h.relative_normal relative_sup

include h in
omit [Finite G] in
theorem replacement_characteristic : MSCharacteristicCondition d.radical :=
  NaturalSixControl.SymplecticSetup.Reduction.msCharacteristic d relative_sup
    h.relative_characteristic

include h in
/-- The actual Section 7 minimality clause on the new carriers. -/
theorem replacement_minimal : CharacteristicMinimal ((K).subgroupOf d.overgroup) d.radical :=
  NaturalSixControl.SymplecticSetup.Reduction.reduced_minimal d h.relative_normal relative_sup

include h in
theorem replacement_product :
    ∀ g : d.overgroup, ∃ k ∈ (K).subgroupOf d.overgroup, ∃ t ∈ d.radical, k * t = g := by
  let := h.relative_normal
  intro g
  obtain ⟨k, hk, t, ht, he⟩ := mem_sup_of_normal_left.mp g.property
  exact ⟨⟨k, mem_sup_left hk⟩, hk, ⟨t, mem_sup_right ht⟩, ht, Subtype.ext he⟩

include h in
theorem replacement_residual : pResidual 2 d.overgroup = (K).subgroupOf d.overgroup := by
  let f := subgroupOfEquivOfLe (show K ≤ d.overgroup from le_sup_left)
  have hp := h.relative_twoPerfect.of_surjective f.symm.toMonoidHom f.symm.surjective
  let := h.relative_normal
  exact pResidual_eq_of_isPPerfect_sup _ _ hp (replacement_radical_isPGroup h d)
    (codisjoint_subgroupOf_sup K d.ambient).eq_top

include h in
/-- The original and replacement commutators are the same entire subgroup. -/
theorem replacement_commutator :
    (⁅pCore 2 d.overgroup, (K).subgroupOf d.overgroup⁆).map d.overgroup.subtype =
      ⁅pCore 2 M, K⁆ :=
  NaturalSixControl.SymplecticSetup.Reduction.commutatorCore_eq d h.relative_normal
    relative_sup h.ambient_commutator_eq_relative_core

include h in
theorem replacement_radical_ne_bot : d.radical ≠ ⊥ := by
  intro hz
  have hq : pCore 2 d.overgroup = ⊥ :=
    bot_unique (hz ▸ replacement_core_le_radical h d)
  have hc := replacement_commutator h d
  rw [hq, commutator_bot_left, Subgroup.map_bot] at hc
  apply initial_moved_ne_bot h
  apply bot_unique
  exact (commutator_mono (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1)
    le_rfl).trans_eq hc.symm

include h in
theorem initialMoved_le_replacement : initialMoved L R ≤ d.overgroup := by
  let := h.relative_normal
  exact (commutator_le_right _ _).trans le_sup_left

/-- The initial layer on the replacement carrier, with its central attachment. -/
abbrev replacementMoved : Subgroup d.overgroup := (initialMoved L R).subgroupOf d.overgroup

include h in
theorem replacementMoved_map : (replacementMoved d).map d.overgroup.subtype = initialMoved L R :=
  map_subgroupOf_eq_of_le (initialMoved_le_replacement h d)

include h in
/-- A containment on the actual replacement suffices for original exhaustion. -/
theorem exhaustion_of_replacement_commutator_le
    (hc : ⁅pCore 2 d.overgroup, (K).subgroupOf d.overgroup⁆ ≤ replacementMoved d) :
    ⁅pCore 2 M, K⁆ = initialMoved L R := by
  apply le_antisymm
  · rw [← replacement_commutator h d, ← replacementMoved_map h d]
    exact map_mono hc
  · exact commutator_mono (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) le_rfl

include h in
/-- The actual free-holomorph tree and critical pairs of every replacement. -/
theorem replacementGeometry : Geometry d.radical :=
  geometry d.radical (replacement_radical_isPGroup h d) (replacement_radical_ne_bot h d)
    (replacement_characteristic h d)

/-- Critical distance uses the original MS93 minimization over both colors. -/
def replacementDistance : ℕ := (replacementGeometry h d).b d.radical

include h in
/-- Characteristic two excludes critical distance zero before natural recognition. -/
theorem replacementDistance_pos : 0 < replacementDistance h d := by
  have hs : omegaCenter d.radical ≤ pCore 2 d.overgroup := by
    intro x hx
    have hc := (mem_omegaCenter_iff.mp hx).2.2
    exact replacement_self_centralizing h d
      (centralizer_le (replacement_core_le_radical h d) hc)
  have hZ : Z d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) := by
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    exact NaturalSixControl.SymplecticSeed.Z_le_map_of_seed_le _ _ hs
  obtain ⟨a, hc⟩ := criticalPair_exists d.radical (alpha d.radical)
    ((replacementGeometry h d).exists_critical (alpha d.radical) rfl)
  by_contra! hz
  have hd : (cosetGraph d.radical).dist (alpha d.radical) a = 0 := by
    rw [hc.1]
    change replacementDistance h d = 0
    omega
  have he : alpha d.radical = a :=
    (cosetGraph_connected d.radical).dist_eq_zero_iff.mp hd
  exact hc.2 (he ▸ hZ)

include h in
theorem replacementDistance_even : Even (replacementDistance h d) :=
  (replacementGeometry h d).even (alpha d.radical) rfl

include h in
/-- Only the genuinely large-distance cases remain to force distance two. -/
theorem replacementDistance_eq_two (hb : replacementDistance h d ≤ 2) :
    replacementDistance h d = 2 := by
  have hp := replacementDistance_pos h d
  have he := replacementDistance_even h d
  rw [Nat.even_iff] at he
  omega

include h in
/-- The graph commutator pulls back through both unchanged subgroup maps. -/
theorem replacement_graph_core_pullback :
    ((core d.radical (alpha d.radical)).comap (embedM d.radical)).map
      d.overgroup.subtype = ⁅pCore 2 M, K⁆ := by
  rw [core_alpha _ (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    (replacement_residual h d), comap_map_eq_self_of_injective (embedM_injective _)]
  exact replacement_commutator h d

include h in
/-- The literal consumer of the distance-two graph containment. -/
theorem exhaustion_of_graph_core_le
    (hc : core d.radical (alpha d.radical) ≤
      (replacementMoved d).map (embedM d.radical)) :
    ⁅pCore 2 M, K⁆ = initialMoved L R := by
  apply exhaustion_of_replacement_commutator_le h d
  have hh := comap_mono (f := embedM d.radical) hc
  rw [core_alpha _ (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    (replacement_residual h d), comap_map_eq_self_of_injective (embedM_injective _),
    comap_map_eq_self_of_injective (embedM_injective _)] at hh
  exact hh

end AlternatingSixReconstruction.Natural.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
