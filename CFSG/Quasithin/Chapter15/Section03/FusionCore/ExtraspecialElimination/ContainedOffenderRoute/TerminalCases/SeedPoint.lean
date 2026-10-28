module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalPoint
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.SeedSplitting
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Transport

/-!
# Constructing the component vector from the source seed

B.2.14 gives the sum of the literal component commutator and the global
fixed space. Some element of Z_S has nonfixed image: otherwise H normalizes
Z_S and hence lies in M, a contradiction. Decompose this element to obtain
a nonzero component vector with proper stabilizer containing Y₀*T*.

This proves existence of the vector and its fixed supplement without a
direct-sum assumption. The equality of its stabilizer with Y₀*T* remains a
separate obligation; `SeedPoint.mark` records precisely that last step.
The only extra local inputs here are Z_S ≤ T and [Z_S,T] ≤ Z from 15.3.48(2).
The universal B.5.5 component-section and B.2.14 splitting implications
remain explicit, to be discharged by the source assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
preceding 15.3.49(k), printed p.1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases

open Subgroup Representation Representation.BinaryOffender ModelExclusions
open ReducedModels ComponentReduction ModelReduction BinaryModels LargerFields
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)

/-- A constructed source vector before the final stabilizer marking.
Both its proper stabilizer and containment of the source parabolic are proved. -/
structure SeedPoint where
  space : Subrepresentation r.placed.action.representation
  component_space : space.toSubmodule =
    Coinvariants.ker (r.placed.action.representation.comp (starImage H (localSpan L T)).subtype)
  supplement : space.toSubmodule ⊔ r.placed.action.representation.invariants = ⊤
  seed : ZS
  point : space.toSubmodule
  fixed_difference :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
      ⟨(seed : G), le_conjugateSpanBy ZS H seed.property⟩) - point.val ∈
        fixedSpace r.placed.action.representation ⊤
  base_le : starImage H Y0 ⊔ starImage H T ≤ pointStabilizer space.toRepresentation point
  proper : pointStabilizer space.toRepresentation point ≠ ⊤

namespace SeedPoint
variable {r}

/-- The vector and the original quotient seed have the same stabilizer. -/
theorem source_stabilizer (p : SeedPoint r) :
    pointStabilizer p.space.toRepresentation p.point =
      pointStabilizer r.placed.action.representation
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
          ⟨(p.seed : G), le_conjugateSpanBy ZS H p.seed.property⟩)) := by
  ext g
  have hf := p.fixed_difference ⟨g, mem_top g⟩
  change r.placed.action.representation g (_ - p.point.val) = _ - p.point.val at hf
  rw [map_sub] at hf
  constructor
  · intro hg
    have he := congrArg Subtype.val hg
    change r.placed.action.representation g p.point.val = p.point.val at he
    change r.placed.action.representation g _ = _
    simpa only [he, sub_left_inj] using hf
  · intro hg
    apply Subtype.ext
    change r.placed.action.representation g p.point.val = p.point.val
    change r.placed.action.representation g _ = _ at hg
    simpa only [hg, sub_right_inj] using hf

/-- Properness forces the constructed component vector to be nonzero. -/
theorem point_ne_zero (p : SeedPoint r) : p.point ≠ 0 := by
  intro hz
  apply p.proper
  rw [hz]
  exact top_unique (fun _ _ => map_zero _)

/-- The exact remaining marking step, after the component closure collapses.
This constructor is not an assertion that the marking has been proved. -/
def mark (p : SeedPoint r) (hclosed : localSpan L T = L)
    (hmark : pointStabilizer p.space.toRepresentation p.point ≤
      starImage H Y0 ⊔ starImage H T) : TerminalPoint r where
  space := p.space
  component_space := p.component_space.trans
    (congrArg (fun A : Subgroup G => Coinvariants.ker
      (r.placed.action.representation.comp (starImage H A).subtype)) hclosed)
  supplement := p.supplement
  seed := p.seed
  point := p.point
  fixed_difference := p.fixed_difference
  stabilizer := le_antisymm p.base_le hmark
  proper := by
    intro ht
    exact p.proper (top_unique (ht ▸ p.base_le))

end SeedPoint

private theorem fixedSpace_top_eq_invariants {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W) :
    fixedSpace ρ ⊤ = ρ.invariants := by
  ext w
  exact ⟨fun h g => h ⟨g, mem_top g⟩, fun h g => h g.val⟩

private theorem moved_eq_ker {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (A : Subgroup D) :
    subspaceCommutator ρ ⊤ A = Coinvariants.ker (ρ.comp A.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, v, _, rfl⟩
    exact ⟨(⟨a, ha⟩, v), rfl⟩
  · rintro ⟨⟨a, v⟩, rfl⟩
    exact ⟨a, a.property, v, Submodule.mem_top, rfl⟩

/-- The source Sylow subgroup fixes every seed image by 15.3.48(2). -/
theorem seed_fixed_by_sylow (h48 : ⁅ZS, T⁆ ≤ Z) (z : ZS) :
    starImage H T ≤ pointStabilizer r.placed.action.representation
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩)) := by
  rintro a ⟨t, ht, rfl⟩
  change r.placed.action.representation (QuotientGroup.mk' (pCore 2 H) t) _ = _
  rw [r.placed.action.on_representatives]
  apply congrArg Additive.ofMul
  apply QuotientGroup.eq_iff_div_mem.mpr
  change ((t : G) * (z : G) * (t : G)⁻¹) / (z : G) ∈ Z
  rw [commutator_comm] at h48
  have hc := h48 (commutator_mem_commutator (show (t : G) ∈ T from ht) z.property)
  change (t : G) * (z : G) * (t : G)⁻¹ * (z : G)⁻¹ ∈ Z at hc
  simpa only [div_eq_mul_inv] using hc

/-- B.2.14 constructs a nonzero component point and its proper stabilizer.
The final equality with the source parabolic is not assumed or asserted. -/
theorem exists_seedPoint [Finite G]
    (sections : EarlierComponentSections κ)
    (hB214 : CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) : Nonempty (SeedPoint r) := by
  classical
  let W : Subrepresentation r.placed.action.representation :=
    ⟨componentSection Z H ZS L T, fun g v hv =>
      componentSection_invariant Z H ZS L Y0 T r.placed.action r.replacement
        r.component.commutator_eq r.normalizes g ⟨v, hv⟩⟩
  have hw : W.toSubmodule = Coinvariants.ker
      (r.placed.action.representation.comp (starImage H (localSpan L T)).subtype) := by
    exact (NaturalCoordinates.componentSection_eq_moved Z H ZS L T
      r.placed.action r.closure_le).trans (moved_eq_ker _ _)
  have hsplit := r.component_section_split hB214 (r.y_le_closure sections) hZST h48
  have hz : ∃ z : ZS, Additive.ofMul
      (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∉
      fixedSpace r.placed.action.representation ⊤ := by
    by_contra! hf
    apply r.minimal.outside
    apply (FactorGeneration.normalizes_seed_of_fixed_image H ZS Z H r.placed.action
      r.placed.line_le_seed le_rfl ?_).trans r.placed.seed_normalizer
    intro z g
    exact hf z ⟨g.val, mem_top g.val⟩
  obtain ⟨z, hz⟩ := hz
  let v := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
    ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩)
  obtain ⟨w, hwW, f, hf, he⟩ := Submodule.mem_sup.mp
    (show v ∈ componentSection Z H ZS L T ⊔ fixedSpace r.placed.action.representation ⊤
      from hsplit.symm ▸ Submodule.mem_top)
  let p : W.toSubmodule := ⟨w, hwW⟩
  have hd : v - p.val ∈ fixedSpace r.placed.action.representation ⊤ := by
    change v - w ∈ _
    rw [← he, add_sub_cancel_left]
    exact hf
  have hs : pointStabilizer W.toRepresentation p =
      pointStabilizer r.placed.action.representation v := by
    ext g
    have hh := hd ⟨g, mem_top g⟩
    change r.placed.action.representation g (v - p.val) = v - p.val at hh
    rw [map_sub] at hh
    constructor
    · intro hg
      have hg' : r.placed.action.representation g p.val = p.val := congrArg Subtype.val hg
      change r.placed.action.representation g v = v
      simpa only [hg', sub_left_inj] using hh
    · intro hg
      apply Subtype.ext
      change r.placed.action.representation g p.val = p.val
      change r.placed.action.representation g v = v at hg
      simpa only [hg, sub_right_inj] using hh
  refine ⟨⟨W, hw, ?_, z, p, hd, ?_, ?_⟩⟩
  · exact (congrArg (W.toSubmodule ⊔ ·)
      (fixedSpace_top_eq_invariants r.placed.action.representation)).symm.trans hsplit
  · rw [hs]
    apply sup_le
    · intro g hg
      exact r.placed.toLocalInput.seed_fixed z ⟨g, hg⟩
    · exact seed_fixed_by_sylow r h48 z
  · rw [hs]
    intro ht
    apply hz
    intro g
    exact (ht.symm ▸ mem_top g.val : g.val ∈ pointStabilizer r.placed.action.representation v)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases
