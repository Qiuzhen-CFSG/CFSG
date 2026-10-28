module
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Module.ZMod

/-!
# Fixed-field extraction from coherent natural-module markings

Suppose an ambient group automorphism β transports α to the entrywise
field automorphism σ, while a binary linear coordinate change B transports
E to coordinatewise σ. Their restrictions identify the fixed actors with
SL₂ over the actual fixed subfield and the fixed vectors with its natural
plane. The coordinate formulas retain the specified β and B, and hence
preserve the marked natural action.

The vector construction works for an arbitrary coordinate index. Its
inverse applies B⁻¹ to the inclusion of fixed-field coordinates. The actor
construction similarly restricts β and descends each matrix entry; the
determinant identity follows under the injective fixed-field inclusion.

This is the fixed-field extraction in Aschbacher--Smith, Lemma 2.4.12(2),
printed p.532. The coherent ambient marking is an explicit input, supplied
separately by semilinear descent; no choice of a second marking is made here.
-/

public section
noncomputable section
namespace Representation.SL2NaturalOffenders.FixedField
open Matrix
variable {F : Type*} [Field F]

private def entrywiseFixedEquiv (σ : F ≃+* F) :
    (Theory.PSL2.sl2FieldAut σ).fixedSubgroup ≃*
      SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) where
  toFun g := by
    let A : Matrix (Fin 2) (Fin 2) (FixedBy.subfield F σ) := fun i j =>
      ⟨g.val i j, by
        have hh := (MulAut.mem_fixedSubgroup _ _).mp g.property
        exact congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val i j) hh⟩
    refine ⟨A, ?_⟩
    apply (FixedBy.subfield F σ).subtype.injective
    change (FixedBy.subfield F σ).subtype A.det = 1
    exact ((FixedBy.subfield F σ).subtype.map_det A).trans g.val.property
  invFun g := ⟨SpecialLinearGroup.map (FixedBy.subfield F σ).subtype g, by
    rw [MulAut.mem_fixedSubgroup]
    ext i j
    exact (g.val i j).property⟩
  left_inv g := by rfl
  right_inv g := by rfl
  map_mul' g h := by
    apply Subtype.ext
    ext i j
    change (g.val.val * h.val.val) i j =
      (((∑ k : Fin 2, (⟨g.val i k, by
        exact congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val i k)
          ((MulAut.mem_fixedSubgroup _ _).mp g.property)⟩ : FixedBy.subfield F σ) *
        (⟨h.val k j, by
          exact congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val k j)
            ((MulAut.mem_fixedSubgroup _ _).mp h.property)⟩ : FixedBy.subfield F σ)) :
        FixedBy.subfield F σ) : F)
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The fixed actor marking uses the original ambient automorphism β. -/
def fixedActorEquiv (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (σ : F ≃+* F) (β : MulAut (SpecialLinearGroup (Fin 2) F))
    (hβ : ∀ g, β (α g) = Theory.PSL2.sl2FieldAut σ (β g)) :
    α.fixedSubgroup ≃* SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
  (MulAut.fixedSubgroupEquivOfCompatible β α (Theory.PSL2.sl2FieldAut σ) hβ).trans
    (entrywiseFixedEquiv σ)

@[simp] theorem fixedActorEquiv_apply_coe
    (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (σ : F ≃+* F) (β : MulAut (SpecialLinearGroup (Fin 2) F))
    (hβ : ∀ g, β (α g) = Theory.PSL2.sl2FieldAut σ (β g))
    (g : α.fixedSubgroup) (i j : Fin 2) :
    ((fixedActorEquiv α σ β hβ g).val i j : F) = (β g).val i j := by
  change ((MulAut.fixedSubgroupEquivOfCompatible β α
    (Theory.PSL2.sl2FieldAut σ) hβ g : SpecialLinearGroup (Fin 2) F).val i j) = _
  rw [MulAut.fixedSubgroupEquivOfCompatible_apply]

variable [Algebra (ZMod 2) F] {ι : Type*}

/-- The literal additive fixed subgroup of the binary linear automorphism. -/
abbrev fixedVectors (E : (ι → F) ≃ₗ[ZMod 2] (ι → F)) :
    AddSubgroup (ι → F) :=
  E.toAddEquiv.toAddMonoidHom.eqLocus (AddMonoidHom.id _)

/-- Fixed vectors are the fixed-field plane in the original coordinates B. -/
@[expose] def fixedVectorEquiv (σ : F ≃+* F)
    (E B : (ι → F) ≃ₗ[ZMod 2] (ι → F))
    (hB : ∀ v, B (E v) = fun i => σ (B v i)) :
    fixedVectors E ≃+ (ι → FixedBy.subfield F σ) where
  toFun v i := ⟨B v i, by
    have hh := congrFun (hB v) i
    have hv : E (v : ι → F) = v := v.property
    rw [hv] at hh
    exact hh.symm⟩
  invFun v := ⟨B.symm (fun i => (v i : F)), by
    change E (B.symm (fun i => (v i : F))) = B.symm (fun i => (v i : F))
    apply B.injective
    rw [hB, B.apply_symm_apply]
    exact funext fun i => (v i).property⟩
  left_inv v := by
    apply Subtype.ext
    exact B.symm_apply_apply v
  right_inv v := by
    ext i
    exact congrFun (B.apply_symm_apply (fun i => (v i : F))) i
  map_add' v w := by
    ext i
    exact congrFun (B.map_add v w) i

@[simp] theorem fixedVectorEquiv_apply_coe (σ : F ≃+* F)
    (E B : (ι → F) ≃ₗ[ZMod 2] (ι → F))
    (hB : ∀ v, B (E v) = fun i => σ (B v i))
    (v : fixedVectors E) (i : ι) :
    (fixedVectorEquiv σ E B hB v i : F) = B v i := rfl

/-- The marked fixed vectors are preserved by the marked fixed actors. -/
theorem fixed_action_mem
    (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (σ : F ≃+* F) (β : MulAut (SpecialLinearGroup (Fin 2) F))
    (E B : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hβ : ∀ g, β (α g) = Theory.PSL2.sl2FieldAut σ (β g))
    (hB : ∀ v, B (E v) = fun i => σ (B v i))
    (hnat : ∀ g v, B (g.val.mulVec v) = (β g).val.mulVec (B v))
    (g : α.fixedSubgroup) (v : fixedVectors E) :
    g.val.val.mulVec (v : Fin 2 → F) ∈ fixedVectors E := by
  change E (g.val.val.mulVec (v : Fin 2 → F)) = g.val.val.mulVec (v : Fin 2 → F)
  apply B.injective
  rw [hB, hnat]
  have hg : α (g : SpecialLinearGroup (Fin 2) F) = g :=
    (MulAut.mem_fixedSubgroup _ _).mp g.property
  have ha : Theory.PSL2.sl2FieldAut σ (β g) = β g :=
    (hβ g).symm.trans (congrArg β hg)
  have hentry (i j : Fin 2) : σ ((β g).val i j) = (β g).val i j :=
    congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val i j) ha
  have hv : E (v : Fin 2 → F) = v := v.property
  have hcoord (i : Fin 2) : σ (B v i) = B v i := by
    have hh := congrFun (hB v) i
    rw [hv] at hh
    exact hh.symm
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul, hentry, hcoord]

/-- Fixed-field descent intertwines the same actor and vector markings. -/
theorem fixed_equivariance
    (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (σ : F ≃+* F) (β : MulAut (SpecialLinearGroup (Fin 2) F))
    (E B : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hβ : ∀ g, β (α g) = Theory.PSL2.sl2FieldAut σ (β g))
    (hB : ∀ v, B (E v) = fun i => σ (B v i))
    (hnat : ∀ g v, B (g.val.mulVec v) = (β g).val.mulVec (B v))
    (g : α.fixedSubgroup) (v : fixedVectors E) :
    fixedVectorEquiv σ E B hB
      ⟨g.val.val.mulVec (v : Fin 2 → F), fixed_action_mem α σ β E B hβ hB hnat g v⟩ =
    (fixedActorEquiv α σ β hβ g).val.mulVec (fixedVectorEquiv σ E B hB v) := by
  ext i
  rw [fixedVectorEquiv_apply_coe]
  rw [hnat]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subfield.coe_add,
    Subfield.coe_mul, fixedActorEquiv_apply_coe, fixedVectorEquiv_apply_coe]

end Representation.SL2NaturalOffenders.FixedField
