module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Evaluation.Multiplicity
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tensor evaluation and the specified right constituent

For compatible common scalars, the binary homogeneous decomposition computes
`Hom_L(I,V)` as copies of the full Schur endomorphism ring. The scalar Schur
property identifies that ring with the common field. Restriction and lifting
of intertwiners therefore give the dimension of the common-field multiplicity
space, proving that tensor evaluation is bijective.

A nonzero invariant multiplicity subspace evaluates onto the jointly
irreducible ambient module, so dimension forces the multiplicity action to be
irreducible. Evaluation at a nonzero left vector embeds it in the ambient
right action. A binary simple submodule of this image has the specified type
`D`; compatibility of every right constituent map upgrades its embedding to
the common field, giving the required equivariant identification.

This proves the tensor step conditional on `CommonScalarData`, not existence
of those scalars. Source: Aschbacher--Smith, combined manuscript, G.9.3,
first paragraph, printed p.356 (PDF p.367).
-/

@[expose] public noncomputable section

open scoped TensorProduct MonoidAlgebra
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.CommonScalarData

universe u v

variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}
  {C : ConstituentData ρ L} {D : ConstituentData ρ L₂}
  (S : CommonScalarData C D)

private def constituentModuleEquiv (C : ConstituentData ρ L) :
    C.space.toRepresentation.asModule ≃ₗ[(ZMod 2)[L]] C.space.asSubmodule := by
  let i : C.space.toRepresentation.IntertwiningMap (ρ.comp L.subtype) :=
    ⟨C.space.toSubmodule.subtype, fun _ => by ext; rfl⟩
  let f := (IntertwiningMap.equivLinearMapAsModule _ _ i).codRestrict
    C.space.asSubmodule (fun x => x.property)
  exact LinearEquiv.ofBijective f ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
    fun x => ⟨⟨x.val, x.property⟩, rfl⟩⟩

private def postcompEquiv {R k A M N : Type*} [CommRing k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    (e : M ≃ₗ[R] N) : (A →ₗ[R] M) ≃ₗ[k] (A →ₗ[R] N) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)
  map_add' f g := by ext x; exact e.map_add _ _
  map_smul' a f := by ext x; exact e.map_smul_of_tower a (f x)

private def scalarEnd : S.F →ₗ[ZMod 2]
    IntertwiningMap C.space.toRepresentation C.space.toRepresentation where
  toFun c :=
    { toLinearMap := (c • LinearMap.id : Module.End S.F C.space.toSubmodule).restrictScalars (ZMod 2)
      isIntertwining' l := by
        apply LinearMap.ext
        intro x
        change c • C.space.toRepresentation l x = C.space.toRepresentation l (c • x)
        rw [← S.left_apply, ← S.left_apply, map_smul] }
  map_add' c d := by
    apply IntertwiningMap.ext
    exact LinearMap.ext fun x => add_smul c d x
  map_smul' c d := by
    apply IntertwiningMap.ext
    exact LinearMap.ext fun x => smul_assoc c d x

private def scalarEndEquiv : S.F ≃ₗ[ZMod 2]
    IntertwiningMap C.space.toRepresentation C.space.toRepresentation := by
  let : Representation.IsIrreducible C.space.toRepresentation := C.irreducible
  let : Nontrivial C.space.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial C.space.toRepresentation
  apply LinearEquiv.ofBijective (S.scalarEnd)
  constructor
  · intro a b hab
    obtain ⟨x, hx⟩ := exists_ne (0 : C.space.toSubmodule)
    exact (smul_left_injective S.F hx) (congrArg (fun f => f x) hab)
  · intro f
    obtain ⟨c, hc⟩ := S.left_schur f
    refine ⟨c, ?_⟩
    apply IntertwiningMap.ext
    exact LinearMap.ext fun x => (hc x).symm

local instance : Module (ZMod 2) S.Multiplicity :=
  Module.compHom S.Multiplicity (algebraMap (ZMod 2) S.F)

local instance : IsScalarTower (ZMod 2) S.F S.Multiplicity :=
  IsScalarTower.of_compHom (ZMod 2) S.F S.Multiplicity

private def binaryMultiplicityEquiv : S.Multiplicity ≃ₗ[ZMod 2]
    IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype) where
  toFun := S.restrictLeftMap
  invFun := S.liftLeftMap
  left_inv := S.liftLeftMap_restrictLeftMap
  right_inv := S.restrictLeftMap_liftLeftMap
  map_add' _ _ := by ext x; rfl
  map_smul' c f := by
    ext x
    exact algebraMap_smul S.F c (f x)

/-- Homogeneity and the full scalar Schur property give the exact dimension
of the evaluation source over the common field. -/
theorem evaluation_finrank [FiniteDimensional (ZMod 2) V] :
    Module.finrank S.F (C.space.toSubmodule ⊗[S.F] S.Multiplicity) =
      Module.finrank S.F V := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := C.decomposition
  let σ := C.space.toRepresentation
  let c : Representation.asModule (ρ.comp L.subtype) ≃ₗ[(ZMod 2)[L]] (Fin n → σ.asModule) :=
    e.trans (LinearEquiv.piCongrRight fun _ => (constituentModuleEquiv C).symm)
  let h : (IntertwiningMap σ (ρ.comp L.subtype)) ≃ₗ[ZMod 2]
      (Fin n → IntertwiningMap σ σ) :=
    (IntertwiningMap.equivLinearMapAsModule _ _).trans
      ((postcompEquiv c).trans
        ((LinearEquiv.linearMapPi (ZMod 2)).symm.trans
          (LinearEquiv.piCongrRight fun _ => (IntertwiningMap.equivLinearMapAsModule σ σ).symm)))
  have hd : Module.finrank (ZMod 2) S.Multiplicity =
      n * Module.finrank (ZMod 2) S.F := by
    rw [(S.binaryMultiplicityEquiv.trans h).finrank_eq,
      ← (LinearEquiv.piCongrRight (fun _ : Fin n => S.scalarEndEquiv)).finrank_eq]
    simp [Module.finrank_pi_fintype]
  have hv : Module.finrank (ZMod 2) V =
      n * Module.finrank (ZMod 2) C.space.toSubmodule := by
    have hh := (c.restrictScalars (ZMod 2)).finrank_eq
    simpa [Module.finrank_pi_fintype, σ.asModuleEquiv.finrank_eq,
      (Representation.asModuleEquiv (ρ.comp L.subtype)).finrank_eq] using hh
  have hm : Module.finrank S.F S.Multiplicity = n := by
    have ht := Module.finrank_mul_finrank (ZMod 2) S.F S.Multiplicity
    rw [hd, Nat.mul_comm n] at ht
    exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ZMod 2) (M := S.F)) ht
  rw [Module.finrank_tensorProduct, hm]
  have htV := Module.finrank_mul_finrank (ZMod 2) S.F V
  have htI := Module.finrank_mul_finrank (ZMod 2) S.F C.space.toSubmodule
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ZMod 2) (M := S.F))
  rw [htV, hv, ← htI]
  ac_rfl

/-- Evaluation is injective; its already established surjectivity and the
homogeneous dimension calculation make it an isomorphism. -/
theorem evaluation_injective [FiniteDimensional (ZMod 2) V]
    (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype)) :
    Function.Injective S.evaluation :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank S.evaluation_finrank).mpr
    (S.evaluation_surjective hc hirr)

private def restrictedEvaluation (hc : ⁅L, L₂⁆ = ⊥)
    (W : Subrepresentation (S.multiplicityRepresentation hc)) :
    C.space.toSubmodule ⊗[S.F] W.toSubmodule →ₗ[S.F] V :=
  S.evaluation.comp (TensorProduct.map 1 W.toSubmodule.subtype)

private theorem restrictedEvaluation_left (hc : ⁅L, L₂⁆ = ⊥)
    (W : Subrepresentation (S.multiplicityRepresentation hc)) (l : L)
    (z : C.space.toSubmodule ⊗[S.F] W.toSubmodule) :
    S.restrictedEvaluation hc W (TensorProduct.map (S.left l) 1 z) =
      ρ l (S.restrictedEvaluation hc W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x f =>
      exact congrArg (fun t : C.space.toSubmodule →ₗ[S.F] V => t x) (f.val.isIntertwining' l)
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem restrictedEvaluation_right (hc : ⁅L, L₂⁆ = ⊥)
    (W : Subrepresentation (S.multiplicityRepresentation hc)) (j : L₂)
    (z : C.space.toSubmodule ⊗[S.F] W.toSubmodule) :
    S.restrictedEvaluation hc W (TensorProduct.map 1 (W.toRepresentation j) z) =
      ρ j (S.restrictedEvaluation hc W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private def restrictedEvaluationRange (hc : ⁅L, L₂⁆ = ⊥)
    (W : Subrepresentation (S.multiplicityRepresentation hc)) :
    Subrepresentation (ρ.comp (L ⊔ L₂).subtype) where
  toSubmodule := (LinearMap.range (S.restrictedEvaluation hc W)).restrictScalars (ZMod 2)
  apply_mem_toSubmodule g x hx := by
    obtain ⟨z, hz⟩ := hx
    have hg : (g : G) ∈ (productMap hc).range := by
      rw [productMap_range hc]
      exact g.property
    obtain ⟨⟨l, j⟩, heq⟩ := hg
    refine ⟨TensorProduct.map (S.left l) 1 (TensorProduct.map 1 (W.toRepresentation j) z), ?_⟩
    rw [S.restrictedEvaluation_left, S.restrictedEvaluation_right, hz]
    change ρ (l : G) (ρ (j : G) x) = ρ (g : G) x
    rw [← Module.End.mul_apply, ← map_mul]
    exact congrArg (fun g : G => ρ g x) heq

/-- Joint irreducibility forces the actual multiplicity action to be irreducible
 over the common field. -/
theorem multiplicityRepresentation_irreducible [FiniteDimensional (ZMod 2) V]
    (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype)) :
    Representation.IsIrreducible (S.multiplicityRepresentation hc) := by
  classical
  let : Representation.IsIrreducible C.space.toRepresentation := C.irreducible
  let : Nontrivial C.space.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial C.space.toRepresentation
  let : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) := hirr
  have hi : S.leftInclusion ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : C.space.toSubmodule)
    intro heq
    apply hx
    apply Subtype.ext
    exact congrArg (fun f : S.Multiplicity => f x) heq
  let : Nontrivial S.Multiplicity := ⟨⟨S.leftInclusion, 0, hi⟩⟩
  refine ⟨fun W => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hWne : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  obtain ⟨f, hf, hf0⟩ := W.toSubmodule.ne_bot_iff.mp hWne
  obtain ⟨x, hx⟩ : ∃ x : C.space.toSubmodule, f x ≠ 0 := by
    by_contra! h
    exact hf0 (by ext x; exact h x)
  have hrne : S.restrictedEvaluationRange hc W ≠ ⊥ := by
    intro hbot
    have hm : f x ∈ S.restrictedEvaluationRange hc W :=
      ⟨x ⊗ₜ[S.F] (⟨f, hf⟩ : W.toSubmodule), rfl⟩
    rw [hbot] at hm
    exact hx hm
  have htop : S.restrictedEvaluationRange hc W = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left hrne
  have hsurj : Function.Surjective (S.restrictedEvaluation hc W) := by
    intro v
    have hm : v ∈ S.restrictedEvaluationRange hc W := by rw [htop]; trivial
    exact hm
  have hd := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [← S.evaluation_finrank, Module.finrank_tensorProduct, Module.finrank_tensorProduct] at hd
  have hm := Nat.le_of_mul_le_mul_left hd
    (Module.finrank_pos (R := S.F) (M := C.space.toSubmodule))
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.eq_top_of_finrank_eq (le_antisymm W.toSubmodule.finrank_le hm)

private def evaluationAtRange (hc : ⁅L, L₂⁆ = ⊥) (x : C.space.toSubmodule) :
    Subrepresentation (ρ.comp L₂.subtype) where
  toSubmodule := (S.evaluationAt x).range.restrictScalars (ZMod 2)
  apply_mem_toSubmodule j v hv := by
    obtain ⟨f, rfl⟩ := hv
    exact ⟨S.multiplicityRepresentation hc j f, rfl⟩

/-- The multiplicity representation is equivariantly isomorphic to the specified
 right constituent, with its given common-field action. -/
theorem multiplicity_equiv_right [FiniteDimensional (ZMod 2) V]
    (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype)) :
    Nonempty (Representation.Equiv (S.multiplicityRepresentation hc) S.right) := by
  classical
  let : Representation.IsIrreducible C.space.toRepresentation := C.irreducible
  let : Nontrivial C.space.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial C.space.toRepresentation
  let : Representation.IsIrreducible D.space.toRepresentation := D.irreducible
  let : Nontrivial D.space.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial D.space.toRepresentation
  let : Representation.IsIrreducible (S.multiplicityRepresentation hc) :=
    S.multiplicityRepresentation_irreducible hc hirr
  obtain ⟨x, hx⟩ := exists_ne (0 : C.space.toSubmodule)
  let W := S.evaluationAtRange hc x
  have hW : W ≠ ⊥ := by
    intro hbot
    have hm : (x : V) ∈ W := ⟨S.leftInclusion, rfl⟩
    rw [hbot] at hm
    exact hx (Subtype.ext hm)
  obtain ⟨B, hB, hBW⟩ := (eq_bot_or_exists_atom_le W).resolve_left hW
  let : IsSimpleModule (ZMod 2)[L₂] B.asSubmodule :=
    constituent_simple ρ L₂ B ((Subrepresentation.irreducible_iff_isAtom B).mpr hB)
  let b : B.asSubmodule ≃ₗ[(ZMod 2)[L₂]] D.space.asSubmodule := (D.isotypic B.asSubmodule).some
  let a := (constituentModuleEquiv D).trans b.symm
  let f : IntertwiningMap D.space.toRepresentation (ρ.comp L₂.subtype) :=
    (IntertwiningMap.equivLinearMapAsModule _ _).symm
      (B.asSubmodule.subtype.comp a.toLinearMap)
  have hfinj : Function.Injective f := by
    intro y z hyz
    apply a.injective
    exact Subtype.ext hyz
  have hfm (y : D.space.toSubmodule) : f y ∈ (S.evaluationAt x).range :=
    hBW (a y).property
  let e := LinearEquiv.ofInjective (S.evaluationAt x) (S.evaluationAt_injective hx)
  let q : D.space.toSubmodule →ₗ[S.F] S.Multiplicity :=
    e.symm.toLinearMap.comp ((S.liftRightMap f).toLinearMap.codRestrict _ hfm)
  have hq (y : D.space.toSubmodule) : S.evaluationAt x (q y) = f y := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f y, hfm y⟩)
  let t : IntertwiningMap S.right (S.multiplicityRepresentation hc) :=
    { toLinearMap := q
      isIntertwining' j := by
        apply LinearMap.ext
        intro y
        apply S.evaluationAt_injective hx
        change S.evaluationAt x (q (S.right j y)) =
          ρ j (S.evaluationAt x (q y))
        rw [hq, hq, S.right_apply]
        exact congrArg (fun t : D.space.toSubmodule →ₗ[ZMod 2] V => t y) (f.isIntertwining' j) }
  have htinj : Function.Injective t := by
    intro y z hyz
    apply hfinj
    rw [← hq y, ← hq z]
    exact congrArg (S.evaluationAt x) hyz
  have htne : t ≠ 0 := by
    intro hz
    obtain ⟨y, hy⟩ := exists_ne (0 : D.space.toSubmodule)
    apply hy
    apply htinj
    rw [hz]
    rfl
  have htsurj := (Representation.IsIrreducible.surjective_or_eq_zero t).resolve_right htne
  exact ⟨(t.ofBijective ⟨htinj, htsurj⟩).symm⟩

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.CommonScalarData

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField

universe u v

/-- The common-field tensor decomposition, with both actual subgroup actions,
after the scalar compatibility contract has been supplied. -/
theorem tensorEvaluation : TensorEvaluationTheorem.{u,v} := by
  intro G _ _ V _ _ _ ρ L L₂ C D S hc hirr
  obtain ⟨e⟩ := S.multiplicity_equiv_right hc hirr
  exact ⟨S.tensorEquivalenceOfMultiplicity hc hirr (S.evaluation_injective hc hirr) e⟩

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
