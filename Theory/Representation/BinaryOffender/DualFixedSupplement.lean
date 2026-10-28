module
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.DualCommutator
/-!
# Dual quadratic bounds across a fixed supplement

If an invariant subspace spans the module together with fixed vectors,
restriction preserves its commutator space and quadraticity. Duality then
transfers the numerical bound from the dual of that actual subspace to the
dual of the whole module. The final theorem starts with the literal dual
of the original representation, so applications need no bidual marking.

Source: Aschbacher–Smith B.5.13, printed pp.110–111, removing the central
summand and applying the bound on the actual moved module.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Quadraticity is preserved and reflected by the literal contragredient. -/
theorem isQuadratic_dual_iff (A : Subgroup G) :
    IsQuadratic ρ.dual A ↔ IsQuadratic ρ A := by
  have h := Representation.quadratic_dual_iff (ρ.comp A.subtype)
  rw [commutator_le_invariants_iff, commutator_le_invariants_iff] at h
  constructor
  · intro hq a ha b hb v
    exact h.mp (fun a b f => hq a a.property b b.property f) ⟨a,ha⟩ ⟨b,hb⟩ v
  · intro hq a ha b hb f
    exact h.mpr (fun a b v => hq a a.property b b.property v) ⟨a,ha⟩ ⟨b,hb⟩ f

/-- Fixed vectors add no quadratic displacement. -/
theorem quadratic_of_fixed_supplement (U : Subrepresentation ρ) (A : Subgroup G)
    (hs : U.toSubmodule ⊔ fixedSpace ρ A = ⊤)
    (hq : IsQuadratic U.toRepresentation A) : IsQuadratic ρ A := by
  intro a ha b hb v
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp (hs ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
  have hq' := congrArg Subtype.val (hq a ha b hb ⟨u,hu⟩)
  have hbz : ρ b z = z := hz ⟨b,hb⟩
  change ρ a (ρ b u - u) = ρ b u - u at hq'
  simpa only [map_add, hbz, add_sub_add_right_eq_sub] using hq'

/-- The moved spaces agree under the literal inclusion. -/
theorem moved_map_eq_of_fixed_supplement (U : Subrepresentation ρ) (A : Subgroup G)
    (hs : U.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    (subspaceCommutator U.toRepresentation ⊤ A).map U.toSubmodule.subtype =
      subspaceCommutator ρ ⊤ A := by
  have hmap := subspaceCommutator_map_embedding ρ U.toRepresentation (MonoidHom.id G)
    U.toSubmodule.subtype (fun _ _ => rfl) A ⊤
  simp only [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id] at hmap
  rw [← hmap]
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨a,ha,v,hv,rfl⟩; exact ⟨a,ha,v,Submodule.mem_top,rfl⟩)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,v,_,rfl⟩
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp (hs ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
  have haz : ρ a z = z := hz ⟨a,ha⟩
  simpa only [map_add, haz, add_sub_add_right_eq_sub, subspaceCommutator] using
    (Submodule.subset_span ⟨a,ha,u,hu,rfl⟩ : ρ a u - u ∈ subspaceCommutator ρ U.toSubmodule A)

/-- Restriction preserves the dual fixed codimension when fixed vectors supplement it. -/
theorem dual_fixedCodim_eq_of_fixed_supplement (U : Subrepresentation ρ) (A : Subgroup G)
    (hs : U.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    fixedCodim U.toRepresentation.dual A = fixedCodim ρ.dual A := by
  rw [fixedCodim_dual_eq_moved_finrank, fixedCodim_dual_eq_moved_finrank]
  exact (Submodule.equivMapOfInjective U.toSubmodule.subtype Subtype.val_injective
    (subspaceCommutator U.toRepresentation ⊤ A)).finrank_eq.trans
      (congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W) (moved_map_eq_of_fixed_supplement ρ U A hs))

/-- A bound on the dual of the spanning submodule bounds the whole dual action. -/
theorem dual_quadraticRatio_le_two_of_fixed_supplement [Finite G]
    (U : Subrepresentation ρ) (hs : U.toSubmodule ⊔ ρ.invariants = ⊤)
    (hq : quadraticRatio U.toRepresentation.dual ≤ 2) : quadraticRatio ρ.dual ≤ 2 := by
  obtain ⟨A,hA,ha,hb⟩ := (quadraticRatio_le_two_iff _).mp hq
  have hsA : U.toSubmodule ⊔ fixedSpace ρ A = ⊤ := by
    apply top_unique
    rw [← hs]
    exact sup_le_sup_left (fun v hv a => hv a) _
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨A,hA,(isQuadratic_dual_iff ρ A).mpr
    (quadratic_of_fixed_supplement ρ U A hsA ((isQuadratic_dual_iff U.toRepresentation A).mp ha)),?_⟩
  rwa [← dual_fixedCodim_eq_of_fixed_supplement ρ U A hsA]

/-- Apply the bound to a literal submodule of the dual of the original representation. -/
theorem quadraticRatio_le_two_of_dual_fixed_supplement [Finite G]
    [FiniteDimensional (ZMod 2) V]
    (U : Subrepresentation ρ.dual) (hs : U.toSubmodule ⊔ ρ.dual.invariants = ⊤)
    (hq : quadraticRatio U.toRepresentation.dual ≤ 2) : quadraticRatio ρ ≤ 2 := by
  have hd := dual_quadraticRatio_le_two_of_fixed_supplement ρ.dual U hs hq
  obtain ⟨A,hA,ha,hb⟩ := (quadraticRatio_le_two_iff _).mp hd
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨A,hA,(isQuadratic_dual_iff ρ A).mp ((isQuadratic_dual_iff ρ.dual A).mp ha),?_⟩
  have he : fixedCodim ρ.dual.dual A = fixedCodim ρ A := by
    rw [fixedCodim_dual_eq_moved_finrank,subspaceCommutator_top_eq_coinvariants]
    exact (finrank_quotient_invariants_eq_dual_commutator (ρ.comp A.subtype)).symm
  rwa [he] at hb
end Representation.BinaryOffender
