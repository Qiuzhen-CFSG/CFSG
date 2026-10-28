module
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient

/-!
# The fixed quotient of a whole Irr⁺ module

The quotient of the top subspace by its central subspace and the quotient
of the original carrier by its fixed space are canonically equivalent.
The equivalence intertwines the restricted action, so the source Irr⁺
condition gives irreducibility on the literal fixed quotient, retaining any
ambient normalizing action.

Source: Aschbacher–Smith, A.1.40, printed p.31; applied to the concluding
argument of 14.7.40, printed p.1063.
-/

public noncomputable section
namespace Representation.BinaryOffender
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) G W) (X : Subgroup G) [X.Normal]

/-- The canonical identification of the central quotient of the whole subspace
with the fixed quotient of its original carrier. -/
def topCentralQuotientEquiv : centralQuotient σ X ⊤ ≃ₗ[ZMod 2] W ⧸ fixedSpace σ X :=
  Submodule.Quotient.equiv _ _
    (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) W) ≃ₗ[ZMod 2] W)
    (by
      ext w
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact hv
      · intro hw
        exact ⟨⟨w,Submodule.mem_top⟩,hw,rfl⟩)

theorem topCentralQuotientEquiv_intertwines
    (hs : X ≤ subspaceStabilizer σ ⊤) (a : X) (v : centralQuotient σ X ⊤) :
    topCentralQuotientEquiv σ X (centralQuotientRepresentation σ X ⊤ hs a v) =
      fixedQuotient σ X a (topCentralQuotientEquiv σ X v) := by
  obtain ⟨w,rfl⟩ := ((fixedSpace σ X).comap (⊤ : Submodule (ZMod 2) W).subtype).mkQ_surjective v
  rfl

/-- Irr⁺ on the whole space gives irreducibility on the literal fixed quotient.
The top-subspace carrier is transported by the canonical quotient equivalence. -/
theorem IsIrrPlus.fixedQuotient_irreducible (hi : IsIrrPlus σ X ⊤) :
    IsIrreducible ((fixedQuotient σ X).comp X.subtype) := by
  obtain ⟨hs,_,hirr⟩ := hi
  apply irreducible_of_surjective_equivariant _
    (centralQuotientRepresentation σ X ⊤ hs) (MonoidHom.id X) Function.surjective_id
    (topCentralQuotientEquiv σ X).symm _ hirr
  intro a v
  apply (topCentralQuotientEquiv σ X).injective
  rw [LinearEquiv.apply_symm_apply, topCentralQuotientEquiv_intertwines,
    LinearEquiv.apply_symm_apply]
  rfl

end Representation.BinaryOffender
