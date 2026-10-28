module
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.FieldLifts
public import Theory.Representation.SL2.NaturalHomogeneous
public import Theory.Representation.SL2.BinaryHermitianIrreducibility

/-!
# Hermitian type under the full component normalizer

Every automorphism of the binary SL₂ group lifts to the Hermitian module:
field automorphisms act entrywise and inner automorphisms act through the
representation. Consequently every ambient conjugate of a marked Hermitian
constituent has the same normal-subgroup type. Clifford generation then makes
an irreducible ambient action homogeneous of that type, including outer
field actors and arbitrary kernels in the component marking.

Source: Aschbacher--Smith D.3.9(1), printed pp.199--200.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups MonoidAlgebra
namespace Representation.SL2Hermitian
open OrthogonalFourMinus.FiniteModel OrthogonalFourMinus.RankOne.AmbientActions
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

theorem exists_automorphism_intertwiner (a : MulAut SL(2,Field s)) :
    ∃ b : Space s ≃ₗ[ZMod 2] Space s, ∀ g v,
      b (SL2.BinarySmall.hermitian s g v) =
        SL2.BinarySmall.hermitian s (a g) (b v) := by
  obtain ⟨g,δ,ha⟩ := Theory.PSL2.sl2_semilinear_coverage a
  let b₀ : Space s ≃+ Space s := (fieldLift s δ).trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv ((action s).asGroupHom g)).toAddEquiv
  let b : Space s ≃ₗ[ZMod 2] Space s :=
    LinearEquiv.ofBijective (b₀.toAddMonoidHom.toZModLinearMap 2) b₀.bijective
  refine ⟨b,?_⟩
  intro x v
  change action s g (fieldLift s δ (action s x v)) =
    action s (a x) (action s g (fieldLift s δ v))
  rw [ha,fieldLift_action]
  change action s g (action s (Theory.PSL2.sl2FieldAut δ x) _) =
    action s (g * Theory.PSL2.sl2FieldAut δ x * g⁻¹) (action s g _)
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
theorem sameModule_conjugate
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    (q : N →* SL(2,Field s)) (α : G → MulAut SL(2,Field s))
    (hα : ∀ (a : G) (k : N), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp N.subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v))
    (a : G) : SameModule I (conjugateSubrepresentationOrderIso ρ N a I) := by
  obtain ⟨b,hb⟩ := exists_automorphism_intertwiner s (α a⁻¹)
  let J := conjugateSubrepresentationOrderIso ρ N a I
  let f := (I.toSubmodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective).trans
    (LinearEquiv.ofEq _ _ (conjugateSubrepresentationOrderIso_toSubmodule ρ N a I).symm)
  have hf (v : I.toSubmodule) : (f v : V) = ρ a v := rfl
  have hEs (k : N) (v : I.toSubmodule) :
      E.symm (I.toRepresentation k v) = SL2.BinarySmall.hermitian s (q k) (E.symm v) := by
    apply E.injective
    rw [E.apply_symm_apply,hE,E.apply_symm_apply]
  refine ⟨E.symm.trans (b.trans (E.trans f)),?_⟩
  intro k v
  apply Subtype.ext
  change (f (E (b (E.symm (I.toRepresentation k v)))) : V) =
    ρ (k : G) (f (E (b (E.symm v))))
  rw [hEs,hb,←hα a⁻¹ k,hE,hf,hf]
  change ρ a (ρ (a⁻¹ * (k : G) * (a⁻¹)⁻¹) _) = _
  simp only [inv_inv,←Module.End.mul_apply,←map_mul,←mul_assoc,mul_inv_cancel,one_mul]
  rfl

theorem homogeneous_of_irreducible
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal]
    (q : N →* SL(2,Field s)) (α : G → MulAut SL(2,Field s))
    (hα : ∀ (a : G) (k : N), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp N.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v)) :
    homogeneousPart I ⊤ = ⊤ := by
  apply top_unique
  have hgen := iSup_conjugateSubrepresentations_eq_top ρ N inferInstance I hI
  have hh := congrArg Subrepresentation.toSubmodule hgen
  rw [toSubmodule_iSup] at hh
  change (⨆ a, (conjugateSubrepresentation ρ N I a).toSubmodule) = ⊤ at hh
  conv_lhs => rw [←hh]
  apply iSup_le
  intro a
  have ha : conjugateSubrepresentation ρ N I a =
      conjugateSubrepresentationOrderIso ρ N a⁻¹ I := by
    simp only [conjugateSubrepresentationOrderIso_apply,inv_inv]
  rw [ha]
  exact le_iSup_of_le (conjugateSubrepresentationOrderIso ρ N a⁻¹ I)
    (le_iSup_of_le ⟨le_top,sameModule_conjugate s ρ N q α hα I E hE a⁻¹⟩ le_rfl)
end Representation.SL2Hermitian
