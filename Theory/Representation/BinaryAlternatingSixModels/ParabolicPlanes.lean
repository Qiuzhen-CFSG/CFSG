module
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-!
# Steinberg recognition at the literal endgame parabolics

The catalogue fixes the duad {0,1}, while the original Section 13.8
coordinates fix {4,5}. Transport an invariant projective line through
conjugation by (0 4)(1 5), then apply the proved binary S₆ catalogue.
Two invariant planes at the actual duad and syntheme stabilizers therefore
identify a simple module with the tensor, retaining its S₆ marking.

Source: Aschbacher--Smith, G.5.2 and 13.8.6(4), printed pp.343,948.
The source application is Chapter13.Section08.SourceCompletion.CaseOne.
-/

public section
open Subgroup Representation
namespace BinaryAlternatingSix
open Theory.SpecificGroups.SymmetricSix

/-- Conjugating a subgroup transports its invariant projective line. -/
theorem hasInvariantLine_conjugate {B X : Type*} [Group B]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) B X) (P : Subgroup B) (c : B)
    (h : HasInvariantLine ρ P) :
    HasInvariantLine ρ (P.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨W,hd,hW⟩ := h
  let F := LinearEquiv.ofBijective (ρ c) (ρ.apply_bijective c)
  refine ⟨W.map (ρ c), (F.finrank_map_eq W).trans hd, ?_⟩
  rintro _ ⟨g,hg,rfl⟩ _ ⟨v,hv,rfl⟩
  refine ⟨ρ g v,hW g hg v hv,?_⟩
  change ρ c (ρ g v) = ρ (c*g*c⁻¹) (ρ c v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- The two endgame parabolics recognize the tensor with their literal marking.
The first fixes {4,5}; it is not the catalogue's stabilizer of {0,1}. -/
theorem tensor_of_parabolic_planes {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) S6 X) [IsIrreducible ρ]
    (h₁ : HasInvariantLine ρ BinaryFlags.H1)
    (h₂ : HasInvariantLine ρ BinaryFlags.H2) : Nonempty (ρ.Equiv tensorAction) := by
  let c : S6 := Equiv.swap 0 4 * Equiv.swap 1 5
  have hc : BinaryFlags.H1.map (MulAut.conj c).toMonoidHom = duadStabilizer := by
    change (MulAction.stabilizer S6 (pair 4 5)).map _ = _
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have hp : c • pair 4 5 = pair 0 1 := by decide
    rw [hp]
    rfl
  obtain ⟨W₁,hd₁,hW₁⟩ := hc ▸ hasInvariantLine_conjugate ρ BinaryFlags.H1 c h₁
  obtain ⟨W₂,hd₂,hW₂⟩ := h₂
  exact SymmetricCatalogue.tensor_recognition alternatingTensor_irreducible ρ
    ⟨W₁,hd₁,fun g hg v hv => hW₁ g.val hg v hv⟩
    ⟨W₂,hd₂,fun g hg v hv => hW₂ g.val hg v hv⟩

end BinaryAlternatingSix
