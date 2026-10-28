module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The original subgroup supplement and central quotient in 13.5.21

If T normalizes B and T ≤ P ≤ BT, then [P:T] is the index of
T ∩ B in P ∩ B. This keeps every element of the original T, including
actors outside the concrete model B. An equivariant central projection
preserves the dimension of a seed disjoint from its kernel.

The central projection below uses the literal quotient by K*-fixed vectors
in Action.Space. It does not identify the full module with that quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21(3),(5), printed p.924 (PDF p.941).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics

/-- The index in the whole supplement equals the index in its model intersection. -/
theorem supplement_index {G : Type*} [Group G] [Finite G] (B T P : Subgroup G)
    (hn : T ≤ normalizer (B : Set G)) (hTP : T ≤ P) (hP : P ≤ B ⊔ T) :
    T.relIndex P = (T.subgroupOf B).relIndex (P.subgroupOf B) := by
  have hprod : (B ⊓ P) ⊔ T = P := by
    apply le_antisymm (sup_le inf_le_right hTP)
    intro x hx
    have hx' : x ∈ (B : Set G) * (T : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left B T hn]
      exact hP hx
    obtain ⟨b, hb, t, ht, rfl⟩ := hx'
    have hbP : b ∈ P := by
      simpa only [mul_inv_cancel_right] using P.mul_mem hx (P.inv_mem (hTP ht))
    exact mul_mem_sup ⟨hb, hbP⟩ ht
  have hn' : T ≤ normalizer ((B ⊓ P : Subgroup G) : Set G) :=
    (le_inf hn (hTP.trans P.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  calc
    T.relIndex P = T.relIndex ((B ⊓ P) ⊔ T) := by rw [hprod]
    _ = T.relIndex (B ⊓ P) := relIndex_sup_of_normalizes _ _ hn'
    _ = (T.subgroupOf B).relIndex (P.subgroupOf B) := by
      rw [← relIndex_subgroupOf (inf_le_left : B ⊓ P ≤ B)]
      congr 1
      ext x
      simp


/-- Projection preserves seed dimension when only the seed avoids the kernel. -/
theorem image_plane_dimension {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    (E : Submodule (ZMod 2) U) (p : U →ₗ[ZMod 2] W)
    (h : Disjoint E p.ker) : Module.finrank (ZMod 2) (E.map p) = Module.finrank (ZMod 2) E := by
  rw [← LinearMap.range_domRestrict]
  apply LinearMap.finrank_range_of_inj
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Subtype.ext
  exact Submodule.disjoint_def.mp h v v.property hv

open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) {K : Subgroup G}
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The natural coordinates are imposed only after the literal quotient by
K*-fixed vectors. -/
noncomputable def centralProjection {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] W) : Action.Space D →ₗ[ZMod 2] W :=
  e.toLinearMap.comp (fixedSpace (Action.starRepresentation D h) (starImage D.H K)).mkQ

theorem centralProjection_ker {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] W) :
    (centralProjection D h e).ker = fixedSpace (Action.starRepresentation D h)
      (starImage D.H K) := by
  ext u
  change e ((fixedSpace (Action.starRepresentation D h) (starImage D.H K)).mkQ u) = 0 ↔ _
  rw [e.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _


end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
