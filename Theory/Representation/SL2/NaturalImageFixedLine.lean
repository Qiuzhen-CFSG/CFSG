module
public import Theory.Representation.SL2.NaturalFixedLine
public import Theory.Representation.SL2.NaturalImageDegree
/-!
# Fixed lines on the faithful natural action image

The marked natural quotient and constituent descend to the literal image of
the ambient representation. A nonzero component-invariant subspace with a
binary fixed line for an elementary image actor therefore forces the same
field-size bound as before passage to the image. No elementary lift of the
actor or faithfulness of its automorphism action is assumed.

Source: Aschbacher--Smith D.3.9(2) and D.3.21(3), pp.200--201,205--206.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2AutomorphismNatural
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance naturalImageFixedLineAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The fixed-line obstruction retains the original component marking through
the faithful ambient action image. -/
theorem card_le_four_of_homogeneous_image_fixed_line
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v))
    (X : Submodule (ZMod 2) V) (hX : X ≠ ⊥)
    (hKX : K ≤ subspaceStabilizer ρ X)
    (A : Subgroup (actionImage ρ)) [IsElementaryAbelian 2 A]
    (hAX : A ≤ subspaceStabilizer (imageRepresentation ρ) X)
    (hline : Module.finrank (ZMod 2)
      (X ⊓ fixedSpace (imageRepresentation ρ) A : Submodule (ZMod 2) V) = 1) :
    Nat.card F ≤ 4 := by
  let σ := imageRepresentation ρ
  let f0 := (actionHom ρ).comp K.subtype
  let B := f0.range
  have hB : B = K.map (actionHom ρ) := by
    change ((actionHom ρ).comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let : B.Normal := hB ▸ Subgroup.Normal.map inferInstance (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective
  let f : K →* B := f0.rangeRestrict
  have hf0 : Function.Surjective f := f0.rangeRestrict_surjective
  have hk : f.ker ≤ q.ker := by
    intro k hk
    apply natural_constituent_detects_component_kernel ρ K q I E hE
    exact congrArg (fun b : B => (b : actionImage ρ)) hk
  let qb : B →* SL(2,F) := f.liftOfSurjective hf0 ⟨q,hk⟩
  have hqb (k : K) : qb (f k) = q k := f.liftOfRightInverse_comp_apply _ _ _ k
  have hqb_surj : Function.Surjective qb := by
    intro g
    obtain ⟨k,rfl⟩ := hq g
    exact ⟨f k,hqb k⟩
  let αb := naturalImageQuotientAction ρ K q hq α hα I E hE
  have hαb (a : actionImage ρ) (b : B) :
      qb (MulAut.conjNormal a b) = αb a (qb b) := by
    obtain ⟨g,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective a
    obtain ⟨k,rfl⟩ := hf0 b
    have hc : MulAut.conjNormal (actionHom ρ g) (f k) = f (MulAut.conjNormal g k) := by
      apply Subtype.ext
      change actionHom ρ g * actionHom ρ (k : G) * (actionHom ρ g)⁻¹ =
        actionHom ρ (g * (k : G) * g⁻¹)
      simp only [map_mul,map_inv]
    change qb (MulAut.conjNormal (actionHom ρ g) (f k)) = αb (actionHom ρ g) (qb (f k))
    rw [hc,hqb,hqb]
    exact (hα g k).trans (congrArg (fun z : MulAut (SL(2,F)) => z (q k))
      (naturalImageQuotientAction_apply ρ K q hq α hα I E hE g).symm)
  let J : Subrepresentation (σ.comp B.subtype) := {
    toSubmodule := I.toSubmodule
    apply_mem_toSubmodule b v hv := by
      obtain ⟨k,rfl⟩ := hf0 b
      exact I.apply_mem_toSubmodule k hv }
  have hJ : J.toRepresentation.IsIrreducible :=
    (irreducible_comp_surjective_iff f hf0 J.toRepresentation).mp hI
  let E' : (Fin 2 → F) ≃ₗ[ZMod 2] J.toSubmodule := E
  have hE' (b : B) v : E' ((qb b).val.mulVec v) = J.toRepresentation b (E' v) := by
    obtain ⟨k,rfl⟩ := hf0 b
    rw [hqb]
    exact hE k v
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp (inferInstance : ρ.IsIrreducible)
  let R : Subrepresentation (σ.comp B.subtype) := {
    toSubmodule := X
    apply_mem_toSubmodule b v hv := by
      obtain ⟨k,rfl⟩ := hf0 b
      exact (hKX k.property v).2 hv }
  have hRn : R ≠ ⊥ := fun hz => hX (congrArg Subrepresentation.toSubmodule hz)
  exact card_le_four_of_homogeneous_fixed_line σ B qb hqb_surj αb hαb J hJ
    E' hE' A R hRn hAX hline
end Representation.SL2AutomorphismNatural
