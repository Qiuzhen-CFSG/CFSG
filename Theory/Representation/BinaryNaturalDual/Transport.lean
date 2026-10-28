module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers
public import Theory.Representation.BinaryNaturalDual.GeneratedCore
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Geometry
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Transport of binary module stabilizers and generated subspaces

An equivariant group and linear equivalence transports the actual point
stabilizer, relative residual, fixed space, commutator space and generated
core. All subgroup maps retain their ambient embeddings. These identities
supply the change of model in Aschbacher–Smith H.9 and its Section 12.1 use.
-/

public section
namespace BinaryNaturalDual.Transport
open VectorStabilizers
open Representation.BinaryOffender
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
variable (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
  (e : G ≃* H) (E : V ≃ₗ[ZMod 2] W)
  (hE : ∀ g v, E (ρ g v) = σ (e g) (E v))

include hE in
/-- Point stabilizers transport under the actual equivariant maps. -/
theorem stabilizer_map (v : V) :
    (representationStabilizer ρ v).map e.toMonoidHom = representationStabilizer σ (E v) := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    change σ (e g) (E v) = E v
    rw [← hE, hg]
  · intro hh
    refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
    apply E.injective
    rw [hE, e.apply_symm_apply]
    exact hh

/-- The restriction of the given group equivalence to point stabilizers. -/
noncomputable def stabilizerEquiv (v : V) :
    representationStabilizer ρ v ≃* representationStabilizer σ (E v) :=
  ((representationStabilizer ρ v).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (stabilizer_map ρ σ e E hE v))

/-- The stabilizer equivalence is the restriction of the ambient map. -/
@[simp] theorem stabilizerEquiv_apply (v : V) (g : representationStabilizer ρ v) :
    (stabilizerEquiv ρ σ e E hE v g).val = e g := by rfl

include hE in
/-- Fixed spaces transport with both the actor and module coordinates. -/
theorem fixed_map (A : Subgroup G) :
    (Representation.BinaryOffender.fixedSpace ρ A).map E.toLinearMap = Representation.BinaryOffender.fixedSpace σ (A.map e.toMonoidHom) :=
  fixedSpace_map_equivariant ρ σ e.toMonoidHom E hE A

include hE in
/-- Commutator spaces are spans of the literal displacements of the actor. -/
theorem commutator_map (A : Subgroup G) :
    (Representation.Coinvariants.ker (ρ.comp A.subtype)).map E.toLinearMap =
      Representation.Coinvariants.ker (σ.comp (A.map e.toMonoidHom).subtype) := by
  rw [Representation.Coinvariants.ker, Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨⟨g,v⟩, rfl⟩, rfl⟩
    change E (ρ g v - v) ∈ _
    rw [map_sub, hE]
    exact Representation.Coinvariants.sub_mem_ker
      (ρ := σ.comp (A.map e.toMonoidHom).subtype)
      ⟨e g, Subgroup.mem_map_of_mem _ g.property⟩ (E v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨_,g,hg,rfl⟩,w⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨ρ g (E.symm w) - E.symm w, ⟨(⟨g,hg⟩, E.symm w), rfl⟩, ?_⟩
    change E (ρ g (E.symm w) - E.symm w) = σ (e g) w - w
    rw [map_sub, hE, E.apply_symm_apply]

include hE in
/-- The actual corank-generated core transports through the restricted actor equivalence. -/
theorem core_map [Finite G] (A : Subgroup G) (k : ℕ) :
    (generatedCore (ρ.comp A.subtype) k).map E.toLinearMap =
      generatedCore (σ.comp (A.map e.toMonoidHom).subtype) k := by
  let f := A.equivMapOfInjective e.toMonoidHom e.injective
  exact generatedCore_map_surjective (ρ.comp A.subtype)
    (σ.comp (A.map e.toMonoidHom).subtype) f.toMonoidHom f.surjective E
    (fun a v => hE a v) k

include hE in
/-- Dimension of the fixed space is independent of the chosen model. -/
theorem fixed_finrank (A : Subgroup G) :
    Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace ρ A) =
      Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace σ (A.map e.toMonoidHom)) := by
  rw [← fixed_map ρ σ e E hE A]
  exact (Submodule.equivMapOfInjective _ E.injective _).finrank_eq

include hE in
/-- Pull back a Sylow of the point stabilizer, retaining its intersection with
an already specified ambient Sylow. -/
theorem sylow_stabilizer_pullback [Finite G] (T : Sylow 2 G) (v : V)
    (P : Sylow 2 (representationStabilizer σ (E v)))
    (hP : (P : Subgroup _).map (representationStabilizer σ (E v)).subtype =
      (T : Subgroup G).map e.toMonoidHom ⊓ representationStabilizer σ (E v)) :
    ∃ Q : Sylow 2 (representationStabilizer ρ v),
      (Q : Subgroup _).map (representationStabilizer ρ v).subtype =
        (T : Subgroup G) ⊓ representationStabilizer ρ v := by
  let : Finite H := Finite.of_equiv G e.toEquiv
  let c := stabilizerEquiv ρ σ e E hE v
  let Q := P.mapSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  refine ⟨Q, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_inf _ _ _ e.injective, stabilizer_map ρ σ e E hE, ← hP]
  change (((P : Subgroup _).map c.symm.toMonoidHom).map
    (representationStabilizer ρ v).subtype).map e.toMonoidHom = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  change e (c.symm a).val = a.val
  rw [← stabilizerEquiv_apply ρ σ e E hE v (c.symm a)]
  exact congrArg Subtype.val (c.apply_symm_apply a)

end BinaryNaturalDual.Transport
