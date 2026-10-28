module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Plane
public import Theory.Representation.EndFieldInvariants
public import Theory.Representation.InvariantsBaseChange

/-!
# Descent of the symplectic tensor geometry

Use the actual Schur field and the published tensor intertwiner. The original
module embeds additively into its scalar extension, so cubic identities descend.
For every subgroup of the matrix model, modular invariant base change and the
Schur-field scalar tower compute the original binary fixed dimension. In
particular, the plane radical fixes exactly 4s binary dimensions.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457.
-/

@[expose] public section
open scoped TensorProduct
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

noncomputable def TensorIdentification.tensorEmbedding {s : ℕ}
    (h : TensorIdentification ρ F s) : V →+ (Vector F ⊗[F] Vector F) where
  toFun v := h.linearEquiv (1 ⊗ₜ[SchurField ρ] ρ.asModuleEquiv.symm v)
  map_zero' := by simp
  map_add' v w := by simp [TensorProduct.tmul_add]

theorem TensorIdentification.tensorEmbedding_injective {s : ℕ}
    (h : TensorIdentification ρ F s) : Function.Injective (h.tensorEmbedding ρ) := by
  intro v w hvw
  apply ρ.asModuleEquiv.symm.injective
  exact (Module.FaithfullyFlat.tensorProduct_mk_injective _)
    (h.linearEquiv.injective hvw)

theorem TensorIdentification.tensorEmbedding_intertwines {s : ℕ}
    (h : TensorIdentification ρ F s) (g : D) (v : V) :
    h.tensorEmbedding ρ (ρ g v) = twistedTensor h.sigma.toRingEquiv (h.groupEquiv g)
      (h.tensorEmbedding ρ v) := by
  simpa [TensorIdentification.tensorEmbedding, extendScalars_apply,
    LinearMap.baseChange_tmul, endFieldRep_apply] using
    h.intertwines g (1 ⊗ₜ[SchurField ρ] ρ.asModuleEquiv.symm v)

theorem TensorIdentification.plane_cubic {s : ℕ} (h : TensorIdentification ρ F s) :
    IsCubic ρ (planeRadical.map h.groupEquiv.symm.toMonoidHom) := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rintro a ⟨a', ha, rfl⟩ b ⟨b', hb, rfl⟩ c ⟨c', hc, rfl⟩ v
  apply h.tensorEmbedding_injective ρ
  simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_sub, map_zero,
    h.tensorEmbedding_intertwines, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  simpa only [LinearMap.sub_apply, LinearMap.id_apply, map_sub] using
    TensorGeometry.plane_tensor_cubic h.sigma.toRingEquiv a' ha b' hb c' hc (h.tensorEmbedding ρ v)
end CFSG.Quasithin.ChapterK.Symplectic

namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation Representation.BinaryOffender
variable {D V F : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

noncomputable def TensorIdentification.fixedTensorEquiv {s : ℕ}
    (h : TensorIdentification ρ F s) (B : Subgroup (Sp F)) :
    (extendScalars F (ρ.endFieldRep.comp (B.map h.groupEquiv.symm.toMonoidHom).subtype)).invariants ≃ₗ[F]
    (Representation.invariants ((twistedTensor h.sigma.toRingEquiv).comp B.subtype)) where
  toFun v := ⟨h.linearEquiv v.val, by
    intro g
    change twistedTensor h.sigma.toRingEquiv g.val (h.linearEquiv v.val) = h.linearEquiv v.val
    have hv := v.property ⟨h.groupEquiv.symm g.val,
      Subgroup.mem_map_of_mem _ g.property⟩
    have hh := h.intertwines (h.groupEquiv.symm g.val) v.val
    rw [MulEquiv.apply_symm_apply] at hh
    exact hh.symm.trans (congrArg h.linearEquiv hv)⟩
  invFun X := ⟨h.linearEquiv.symm X.val, by
    intro g
    change extendScalars F ρ.endFieldRep g.val (h.linearEquiv.symm X.val) = h.linearEquiv.symm X.val
    apply h.linearEquiv.injective
    rw [h.intertwines, LinearEquiv.apply_symm_apply]
    obtain ⟨b, hb, he⟩ := g.property
    rw [← he, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact X.property ⟨b, hb⟩⟩
  left_inv v := Subtype.ext (h.linearEquiv.symm_apply_apply v.val)
  right_inv X := Subtype.ext (h.linearEquiv.apply_symm_apply X.val)
  map_add' v w := Subtype.ext (map_add h.linearEquiv v.val w.val)
  map_smul' c v := Subtype.ext (map_smul h.linearEquiv c v.val)

theorem TensorIdentification.fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) (B : Subgroup (Sp F)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (B.map h.groupEquiv.symm.toMonoidHom)) =
      s * Module.finrank F ((Representation.invariants ((twistedTensor h.sigma.toRingEquiv).comp B.subtype))) := by
  let : Module.Finite (SchurField ρ) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (SchurField ρ) ρ.asModule
  change Module.finrank (ZMod 2) (Representation.invariants (ρ.comp (B.map h.groupEquiv.symm.toMonoidHom).subtype)) = _
  rw [finrank_invariants_eq_endField_mul ρ,
    OneCohomology.coefficient_finrank_of_card 2 s h.schur_card]
  congr 1
  rw [← finrank_invariants_extendScalars_eq_of_finite (E := F)]
  exact (h.fixedTensorEquiv ρ B).finrank_eq

theorem TensorIdentification.plane_fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) :
    Module.finrank (ZMod 2) (fixedSpace ρ (planeRadical.map h.groupEquiv.symm.toMonoidHom)) = 4 * s := by
  have hne : h.sigma.toRingEquiv ≠ RingEquiv.refl F := by
    intro he
    apply h.sigma_ne
    ext t
    exact DFunLike.congr_fun he t
  rw [h.fixed_finrank ρ, TensorGeometry.plane_tensor_fixed_finrank h.sigma.toRingEquiv hne]
  omega
end CFSG.Quasithin.ChapterK.Symplectic
