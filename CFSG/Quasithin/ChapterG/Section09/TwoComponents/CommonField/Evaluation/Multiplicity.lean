module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Evaluation.ScalarData

/-!
# Multiplicity action and tensor evaluation over compatible scalars

Once the two Schur-field actions have been aligned, the left multiplicity
space is the actual space of common-field intertwiners from the specified
left constituent to the ambient module. The commuting right subgroup acts
by postcomposition. Evaluation intertwines both actions and is surjective:
its range is a nonzero subrepresentation of the irreducibly acting join.

Injectivity of tensor evaluation and identification of this multiplicity
space with the specified right constituent remain separate obligations.
In particular, surjectivity here does not assert a tensor decomposition.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356,
first paragraph; the usual homogeneous-module evaluation construction.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.CommonScalarData

universe u v

variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}
  {C : ConstituentData ρ L} {D : ConstituentData ρ L₂}
  (S : CommonScalarData C D)

/-- The actual common-field multiplicity space of the left constituent. -/
abbrev Multiplicity := IntertwiningMap S.left S.ambientLeft

instance multiplicity_finite [FiniteDimensional (ZMod 2) V] :
    FiniteDimensional S.F S.Multiplicity := inferInstance

/-- Evaluating at a fixed constituent vector is a linear map into the ambient module. -/
def evaluationAt (x : C.space.toSubmodule) : S.Multiplicity →ₗ[S.F] V where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluationAt_apply (x : C.space.toSubmodule) (f : S.Multiplicity) :
    S.evaluationAt x f = f x := rfl

/-- A nonzero vector detects every intertwiner from the irreducible left
constituent. This embeds the multiplicity space in the ambient right action. -/
theorem evaluationAt_injective {x : C.space.toSubmodule} (hx : x ≠ 0) :
    Function.Injective (S.evaluationAt x) := by
  let : Representation.IsIrreducible C.space.toRepresentation := C.irreducible
  have hzero (f : S.Multiplicity) (hf : f x = 0) : f = 0 := by
    rcases Representation.IsIrreducible.injective_or_eq_zero (S.restrictLeftMap f) with hi | hz
    · exact (hx (hi (show S.restrictLeftMap f x = S.restrictLeftMap f 0 by
        simpa only [restrictLeftMap_apply, map_zero] using hf))).elim
    · ext y
      exact congrArg (fun g : IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype) => g y) hz
  intro f g hfg
  apply sub_eq_zero.mp
  apply hzero
  change f x - g x = 0
  exact sub_eq_zero.mpr hfg

/-- The right factor acts on multiplicities by postcomposition. -/
def multiplicityRepresentation (hc : ⁅L, L₂⁆ = ⊥) : Representation S.F L₂ S.Multiplicity where
  toFun j :=
    { toFun := fun f =>
        { toLinearMap := (S.ambientRight j).comp f.toLinearMap
          isIntertwining' l := by
            ext x
            change S.ambientRight j (f (S.left l x)) =
              S.ambientLeft l (S.ambientRight j (f x))
            rw [f.isIntertwining]
            exact (S.ambient_commute hc l j (f x)).symm }
      map_add' := by intro f g; ext x; exact map_add (S.ambientRight j) (f x) (g x)
      map_smul' := by intro c f; ext x; exact map_smul (S.ambientRight j) c (f x) }
  map_one' := by ext f x; exact congrArg (fun t : Module.End S.F V => t (f x)) S.ambientRight.map_one
  map_mul' j k := by
    ext f x
    exact congrArg (fun t : Module.End S.F V => t (f x)) (S.ambientRight.map_mul j k)

@[simp] theorem multiplicityRepresentation_apply (hc : ⁅L, L₂⁆ = ⊥)
    (j : L₂) (f : S.Multiplicity) (x : C.space.toSubmodule) :
    S.multiplicityRepresentation hc j f x = ρ j (f x) := rfl

/-- Evaluation of an actual intertwiner on a vector of the left constituent. -/
def evaluation : C.space.toSubmodule ⊗[S.F] S.Multiplicity →ₗ[S.F] V :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun f => f x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := by intro x y; ext f; exact map_add f x y
      map_smul' := by intro c x; ext f; exact map_smul f c x }

@[simp] theorem evaluation_tmul (x : C.space.toSubmodule) (f : S.Multiplicity) :
    S.evaluation (x ⊗ₜ[S.F] f) = f x := rfl

/-- The left factor acts on the first argument of evaluation. -/
theorem evaluation_left (l : L) (z : C.space.toSubmodule ⊗[S.F] S.Multiplicity) :
    S.evaluation (TensorProduct.map (S.left l) 1 z) = ρ l (S.evaluation z) := by
  have he : S.evaluation.comp (TensorProduct.map (S.left l) 1) =
      (S.ambientLeft l).comp S.evaluation := by
    apply TensorProduct.ext'
    intro x f
    simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, Module.End.one_apply,
      evaluation_tmul, IntertwiningMap.toLinearMap_apply] using
        congrArg (fun t : C.space.toSubmodule →ₗ[S.F] V => t x) (f.isIntertwining' l)
  exact congrArg (fun t : C.space.toSubmodule ⊗[S.F] S.Multiplicity →ₗ[S.F] V => t z) he

/-- The right factor acts on the multiplicity argument of evaluation. -/
theorem evaluation_right (hc : ⁅L, L₂⁆ = ⊥) (j : L₂)
    (z : C.space.toSubmodule ⊗[S.F] S.Multiplicity) :
    S.evaluation (TensorProduct.map 1 (S.multiplicityRepresentation hc j) z) =
      ρ j (S.evaluation z) := by
  have he : S.evaluation.comp (TensorProduct.map 1 (S.multiplicityRepresentation hc j)) =
      (S.ambientRight j).comp S.evaluation := by
    apply TensorProduct.ext'
    intro x f
    rfl
  exact congrArg (fun t : C.space.toSubmodule ⊗[S.F] S.Multiplicity →ₗ[S.F] V => t z) he

private def evaluationRange (hc : ⁅L, L₂⁆ = ⊥) :
    Subrepresentation (ρ.comp (L ⊔ L₂).subtype) where
  toSubmodule := (LinearMap.range S.evaluation).restrictScalars (ZMod 2)
  apply_mem_toSubmodule g x hx := by
    obtain ⟨z, hz⟩ := hx
    have hg : (g : G) ∈ (productMap hc).range := by
      rw [productMap_range hc]
      exact g.property
    obtain ⟨⟨l, j⟩, heq⟩ := hg
    refine ⟨TensorProduct.map (S.left l) 1
      (TensorProduct.map 1 (S.multiplicityRepresentation hc j) z), ?_⟩
    rw [S.evaluation_left, S.evaluation_right, hz]
    change ρ (l : G) (ρ (j : G) x) = ρ (g : G) x
    rw [← Module.End.mul_apply, ← map_mul]
    exact congrArg (fun g : G => ρ g x) heq

/-- Joint irreducibility makes evaluation surjective. The specified inclusion
of the nonzero left constituent proves that its range is nonzero. -/
theorem evaluation_surjective (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype)) :
    Function.Surjective S.evaluation := by
  let : Representation.IsIrreducible C.space.toRepresentation := C.irreducible
  let : Nontrivial C.space.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial C.space.toRepresentation
  let : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) := hirr
  have hne : S.evaluationRange hc ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : C.space.toSubmodule)
    intro hbot
    have hmem : (x : V) ∈ S.evaluationRange hc :=
      ⟨x ⊗ₜ[S.F] S.leftInclusion, rfl⟩
    rw [hbot] at hmem
    apply hx
    exact Subtype.ext hmem
  have htop : S.evaluationRange hc = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (S.evaluationRange hc)).resolve_left hne
  intro x
  have hmem : x ∈ S.evaluationRange hc := by rw [htop]; trivial
  exact hmem

/-- Convert actual evaluation bijectivity and an equivariant identification of
the multiplicity space into the specified tensor equivalence. Surjectivity is
already proved from joint irreducibility, so only injectivity is an input here. -/
def tensorEquivalenceOfMultiplicity (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype))
    (hinj : Function.Injective S.evaluation)
    (e : Representation.Equiv (S.multiplicityRepresentation hc) S.right) :
    S.TensorEquivalence := by
  let ev := LinearEquiv.ofBijective S.evaluation ⟨hinj, S.evaluation_surjective hc hirr⟩
  let t := TensorProduct.congr (LinearEquiv.refl S.F C.space.toSubmodule) e.toLinearEquiv
  have hleft (l : L) (z : C.space.toSubmodule ⊗[S.F] S.Multiplicity) :
      t (TensorProduct.map (S.left l) 1 z) = TensorProduct.map (S.left l) 1 (t z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x f => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hright (j : L₂) (z : C.space.toSubmodule ⊗[S.F] S.Multiplicity) :
      t (TensorProduct.map 1 (S.multiplicityRepresentation hc j) z) =
        TensorProduct.map 1 (S.right j) (t z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x f =>
      change x ⊗ₜ[S.F] e (S.multiplicityRepresentation hc j f) =
        x ⊗ₜ[S.F] (S.right j (e f))
      congr 1
      exact congrArg (fun q : S.Multiplicity →ₗ[S.F] D.space.toSubmodule => q f)
        (e.isIntertwining' j)
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨ev.symm.trans t, ?_, ?_⟩
  · intro l v
    have hv : ev.symm (ρ l v) = TensorProduct.map (S.left l) 1 (ev.symm v) := by
      apply ev.injective
      rw [ev.apply_symm_apply]
      change ρ l v = S.evaluation (TensorProduct.map (S.left l) 1 (ev.symm v))
      rw [S.evaluation_left]
      exact congrArg (ρ l) (ev.apply_symm_apply v).symm
    change t (ev.symm (ρ l v)) = TensorProduct.map (S.left l) 1 (t (ev.symm v))
    rw [hv]
    exact hleft l (ev.symm v)
  · intro j v
    have hv : ev.symm (ρ j v) =
        TensorProduct.map 1 (S.multiplicityRepresentation hc j) (ev.symm v) := by
      apply ev.injective
      rw [ev.apply_symm_apply]
      change ρ j v =
        S.evaluation (TensorProduct.map 1 (S.multiplicityRepresentation hc j) (ev.symm v))
      rw [S.evaluation_right]
      exact congrArg (ρ j) (ev.apply_symm_apply v).symm
    change t (ev.symm (ρ j v)) = TensorProduct.map 1 (S.right j) (t (ev.symm v))
    rw [hv]
    exact hright j (ev.symm v)

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.CommonScalarData
