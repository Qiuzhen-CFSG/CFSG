module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Literal central sections and the original rank-one Borel

For an invariant space W the lower layer is exactly W ∩ C_U(K).
Its quotient is identified with W/C_W(K). If W = [U,K], the quotient
U/W is centralized by K. Recognizing the inverter-fixed multiplicity
space as natural then constructs the tensor layer on this literal section.

Sylow conjugacy aligns the original Borel with the standard matrix Borel.
Conjugating the group coordinates and the natural module coordinates by
the same matrix preserves equivariance. Both field parities are retained.

The moved-space equality and the natural recognition remain explicit in
this conditional construction; they are not asserted as source conclusions.
No Borel centralization or equality of fixed spaces is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20, printed pp.954–955, and B.4.2(1), printed p.86.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) G U) (K : Subgroup G) [K.Normal]
    (W : Subrepresentation ρ)

/-- The actual central bottom of the chosen invariant upper space. -/
def centralBottom : Subrepresentation ρ where
  toSubmodule := W.toSubmodule ⊓ fixedSpace ρ K
  apply_mem_toSubmodule g u hu :=
    ⟨W.apply_mem_toSubmodule g hu.1,
      (fixedSpace_stable_of_normal ρ K (mem_top g) u).mpr hu.2⟩

/-- The literal intersection is contained in the upper space. -/
theorem centralBottom_le : centralBottom ρ K W ≤ W := by
  intro u hu
  exact hu.1

/-- The component fixes the bottom pointwise. -/
theorem centralBottom_central :
    (centralBottom ρ K W).toSubmodule ≤ Representation.invariants (ρ.comp K.subtype) := by
  intro u hu k
  exact hu.2 k

/-- Restricting the bottom to W gives exactly C_W(K). -/
theorem centralBottom_comap :
    (centralBottom ρ K W).toSubmodule.comap W.toSubmodule.subtype =
      (fixedSpace ρ K).comap W.toSubmodule.subtype := by
  change (W.toSubmodule ⊓ fixedSpace ρ K).comap W.toSubmodule.subtype = _
  rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]

/-- Identify the literal section with its central quotient. -/
def centralSectionEquiv :
    SectionSpace ρ (centralBottom ρ K W) W ≃ₗ[ZMod 2]
      centralQuotient ρ K W.toSubmodule :=
  Submodule.quotEquivOfEq _ _ (centralBottom_comap ρ K W)

omit [K.Normal] in
/-- All action differences lie in the moved space, so the upper quotient is central. -/
theorem central_quotient_of_moved_eq
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ K) :
    ∀ (g : K) (u : U), (ρ.comp K.subtype) g u - u ∈ W.toSubmodule := by
  intro g u
  rw [hW]
  exact Submodule.subset_span ⟨g, g.property, u, Submodule.mem_top, rfl⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [K.Normal] in
/-- Align a specified Sylow normalizer, without changing the chosen Borel. -/
theorem align_borel [Finite K] (e : K ≃* SL(2,F)) (S : Sylow 2 K) :
    ∃ g : SL(2,F),
      (normalizer (S : Set K)).map
          (e.trans (MulAut.conj g)).toMonoidHom =
        Matrix.SpecialLinearGroup.rankOneBorel F := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 SL(2,F) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2,F) P
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  refine ⟨g, ?_⟩
  have hm : ((S : Subgroup K).map e.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = Matrix.SpecialLinearGroup.upperUnipotent F :=
    congrArg Sylow.toSubgroup hg
  change (normalizer (S : Set K)).map
    ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← S.coe_coe, ← Subgroup.map_map,
    map_equiv_normalizer_eq (S : Subgroup K) e,
    map_equiv_normalizer_eq _ (MulAut.conj g), hm]

variable {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]

private def actionEquiv (σ : Representation (ZMod 2) E N) (g : E) : N ≃ₗ[ZMod 2] N where
  toLinearMap := σ g
  invFun := σ g⁻¹
  left_inv v := by
    change σ g⁻¹ (σ g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change σ g (σ g⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

omit [K.Normal] in
private theorem conjugated_coordinates
    (τ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) E N)
    (e : K ≃* E) (a : U ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (τ k v) = σ (e k) (a v)) (g : E) :
    ∀ k v, (a.trans (actionEquiv σ g)) (τ k v) =
      σ ((e.trans (MulAut.conj g)) k) ((a.trans (actionEquiv σ g)) v) := by
  intro k v
  change σ g (a (τ k v)) = σ (g * e k * g⁻¹) (σ g (a v))
  rw [ha]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

variable (s : S₃ →* G) (hs : ∀ (k : K) g, Commute (k : G) (s g))
    [Algebra (ZMod 2) F]

/-- The Borel and module coordinates are changed by the same inner automorphism. -/
theorem natural_layer [Finite K]
    (S : Sylow 2 K) (B : Subgroup K) (hB : B = normalizer (S : Set K))
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ K)
    (e : K ≃* SL(2,F))
    (a : SectionMultiplicity ρ s (centralBottom ρ K W) W ≃ₗ[ZMod 2] (Fin 2 → F))
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ K.subtype s hs (centralBottom ρ K W) W k v) =
        HigherFieldBorelFixedSpaces.binaryNatural 2 (e k) (a v)) :
    ∃ e' : K ≃* SL(2,F),
      B.map e'.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F ∧
      (centralBottom ρ K W).toSubmodule ≤ Representation.invariants (ρ.comp K.subtype) ∧
      (∀ (g : K) (u : U), (ρ.comp K.subtype) g u - u ∈ W.toSubmodule) ∧
      Nonempty (NaturalLayers.TensorLayer (ρ.comp K.subtype)
        (HigherFieldBorelFixedSpaces.binaryNatural 2) e'
        (centralBottom ρ K W).toSubmodule W.toSubmodule) := by
  obtain ⟨g, hg⟩ := align_borel K e S
  let e' := e.trans (MulAut.conj g)
  let a' := a.trans (actionEquiv (HigherFieldBorelFixedSpaces.binaryNatural 2) g)
  refine ⟨e', hB ▸ hg, centralBottom_central ρ K W,
    central_quotient_of_moved_eq ρ K W hW, ?_⟩
  refine ⟨tensorLayer ρ K.subtype s hs (centralBottom ρ K W) W
    (HigherFieldBorelFixedSpaces.binaryNatural 2) e' a'
    (centralBottom_le ρ K W) hgen ?_⟩
  exact conjugated_coordinates K _ _ e a ha g

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

end
