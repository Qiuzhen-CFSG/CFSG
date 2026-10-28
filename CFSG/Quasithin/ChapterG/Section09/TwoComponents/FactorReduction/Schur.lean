module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.TensorData
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Identifying the tensor factor's Schur degree

The scalar description of all binary intertwining endomorphisms in
`TensorData` gives a linear isomorphism from its common field to the actual
binary commutant. This remains true after transport along any group
isomorphism. Thus highest-weight theorems about the commutant use precisely
the field degree of the tensor construction.

Source: Aschbacher--Smith, G.9.3, printed p.356, the field
`F = End_L(I)` in the first paragraph.
-/

public noncomputable section

open scoped MonoidAlgebra

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.TensorData

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}
  (T : TensorData ρ L L₂)

/-- The scalar commutant is the actual endomorphism field, also after
transporting the actor through an isomorphism. -/
theorem left_schur_degree_comp {D : Type*} [Group D] (e : D ≃* L) :
    Module.finrank (ZMod 2)
      (Module.End (ZMod 2)[D]
        (Representation.asModule ((Representation.restrictScalars (k := ZMod 2) T.left).comp e.toMonoidHom))) = T.n := by
  let σ := (Representation.restrictScalars (k := ZMod 2) T.left).comp e.toMonoidHom
  let τ := Representation.restrictScalars (k := ZMod 2) T.left
  let : Representation.IsIrreducible τ := T.left_irreducible
  let : Nontrivial τ.asModule := IsSimpleModule.nontrivial (ZMod 2)[L] τ.asModule
  let : Nontrivial T.I := τ.asModuleEquiv.injective.nontrivial
  let f : T.F →ₗ[ZMod 2] Representation.IntertwiningMap σ σ := {
    toFun c := {
      toLinearMap := (c • (LinearMap.id : T.I →ₗ[T.F] T.I)).restrictScalars (ZMod 2)
      isIntertwining' g := by ext x; exact (map_smul (T.left (e g)) c x).symm }
    map_add' c d := by ext x; exact add_smul c d x
    map_smul' c d := by ext x; exact smul_assoc c d x }
  have hfi : Function.Injective f := by
    intro c d h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := T.I)
    intro x
    exact congrArg (fun a : Representation.IntertwiningMap σ σ => a x) h
  have hfs : Function.Surjective f := by
    intro a
    let b : Representation.IntertwiningMap τ τ := {
      toLinearMap := a.toLinearMap
      isIntertwining' l := by
        obtain ⟨g, rfl⟩ := e.surjective l
        exact a.isIntertwining' g }
    obtain ⟨c, hc⟩ := T.left_schur b
    refine ⟨c, ?_⟩
    ext x
    exact (hc x).symm
  exact ((LinearEquiv.ofBijective f ⟨hfi, hfs⟩).trans
    (Representation.IntertwiningMap.equivLinearMapAsModule σ σ)).finrank_eq.symm

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.TensorData
