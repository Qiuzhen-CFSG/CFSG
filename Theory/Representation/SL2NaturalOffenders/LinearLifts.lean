module
public import Theory.Representation.SL2NaturalOffenders.OuterSemilinear

/-!
# Linear lifts of binary SL₂ automorphisms

An automorphism admitting a field-linear lift on the natural plane is inner.
The proved outer-intertwiner theorem gives a nontrivial coefficient for an
outer automorphism; field-linearity contradicts that coefficient on a nonzero
vector. This is the natural-row field-factor step in Aschbacher--Smith,
10.2.3, printed p.745.
-/

public noncomputable section
namespace Representation.SL2NaturalOffenders
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  [Algebra (ZMod 2) F]

theorem linear_intertwiner_inner
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v)) :
    ∃ g, a = MulAut.conj g := by
  by_contra houter
  obtain ⟨σ,hσne,hσ⟩ := outer_intertwiner_semilinear a
    (E.restrictScalars (ZMod 2)) he houter
  apply hσne
  ext c
  have h := hσ c (E.symm ![1,0])
  change E (c • E.symm ![1,0]) = σ c • E (E.symm ![1,0]) at h
  rw [E.map_smul,E.apply_symm_apply] at h
  have h0 := congrFun h 0
  simpa using h0.symm
end Representation.SL2NaturalOffenders
