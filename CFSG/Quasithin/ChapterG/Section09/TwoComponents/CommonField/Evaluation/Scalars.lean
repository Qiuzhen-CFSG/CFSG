module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Evaluation.ScalarData
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Aligning the two homogeneous Schur-field actions

Extend each constituent's full Schur field diagonally along its homogeneous
ambient decomposition. Coordinate maps are constituent endomorphisms, so
commutativity of the finite Schur field implies compatibility with every
constituent map and centrality in the full restriction endomorphism ring.
The commuting second actor therefore respects these scalars as well.

Both extended fields embed into the Schur field of the irreducible join.
Equal cardinalities identify their images there: both images are precisely
the roots of `X ^ q - X`. The resulting field isomorphism aligns the actual
ambient actions. Transporting the second constituent's scalars along this
isomorphism gives `CommonScalarData`, with the original binary modules intact.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356
(PDF p.367), first paragraph. This proves the scalar step only.
-/

noncomputable section

open scoped MonoidAlgebra
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField

universe u v

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- The actual group-algebra structures behind a constituent agree through
its inclusion into the ambient restriction. -/
def constituentModuleEquiv (C : ConstituentData ρ L) :
    C.space.toRepresentation.asModule ≃ₗ[(ZMod 2)[L]] C.space.asSubmodule where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    change (C.space.toRepresentation.asModuleEquiv (a • x)).val =
      Representation.asModuleEquiv (ρ.comp L.subtype)
        (a • (Representation.asModuleEquiv (ρ.comp L.subtype)).symm
          (C.space.toRepresentation.asModuleEquiv x).val)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      simpa only [add_smul, map_add, Submodule.coe_add] using congrArg₂ (· + ·) ha hb
    | single g a =>
      simp only [Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_single, LinearMap.smul_apply,
        LinearEquiv.apply_symm_apply]
      rfl

namespace CommonScalarDiagonal
variable {R S M : Type*} [Ring R] [AddCommGroup S] [AddCommGroup M]
  [Module R S] [Module R M] {n : ℕ}

def diagonal : Module.End R S →+* Module.End R (Fin n → S) where
  toFun a := LinearMap.pi fun i => a.comp (LinearMap.proj i)
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

def extend (e : M ≃ₗ[R] (Fin n → S)) : Module.End R S →+* Module.End R M :=
  e.symm.conjRingEquiv.toRingHom.comp diagonal

lemma extend_apply (e : M ≃ₗ[R] (Fin n → S)) (a : Module.End R S) (x : M) :
    extend e a x = e.symm (fun i => a (e x i)) := rfl

/-- Every map from the simple type commutes with diagonal scalars, since its
coordinate maps belong to the commutative constituent endomorphism ring. -/
lemma extend_map (e : M ≃ₗ[R] (Fin n → S))
    (hc : ∀ a b : Module.End R S, a * b = b * a)
    (a : Module.End R S) (f : S →ₗ[R] M) (x : S) :
    extend e a (f x) = f (a x) := by
  apply e.injective
  ext i
  simp only [extend_apply, LinearEquiv.apply_symm_apply]
  exact congrArg (fun b : Module.End R S => b x)
    (hc a ((LinearMap.proj i).comp (e.toLinearMap.comp f)))

/-- Expand an arbitrary vector into its constituent coordinates to obtain
centrality in the full ambient endomorphism ring. -/
lemma extend_commute (e : M ≃ₗ[R] (Fin n → S))
    (hc : ∀ a b : Module.End R S, a * b = b * a)
    (a : Module.End R S) (f : Module.End R M) :
    extend e a * f = f * extend e a := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i, e.symm (Pi.single i (e x i)) := by
    rw [← map_sum, LinearMap.sum_single_apply, LinearEquiv.symm_apply_apply]
  rw [hx]
  simp only [Module.End.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  let g : S →ₗ[R] M := e.symm.toLinearMap.comp (LinearMap.single R (fun _ : Fin n => S) i)
  exact (extend_map e hc a (f.comp g) _).trans
    (congrArg f (extend_map e hc a g _).symm)

end CommonScalarDiagonal

open Polynomial in
/-- An embedded field of order `q` consists of all roots of `X ^ q - X`.
Thus equal orders force equal images in the containing field. -/
lemma finiteField_range_le {F K E : Type*} [Field F] [Field K] [Field E]
    [Finite F] [Finite K] (φ : F →+* E) (ψ : K →+* E)
    (hc : Nat.card F = Nat.card K) : φ.fieldRange ≤ ψ.fieldRange := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K
  have hc' : Fintype.card F = Fintype.card K := by simpa using hc
  have hr := roots_map_of_injective_of_card_eq_natDegree
    (p := (X ^ Fintype.card K - X : K[X])) ψ.injective
    (by rw [FiniteField.roots_X_pow_card_sub_X,
            FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]; rfl)
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    FiniteField.roots_X_pow_card_sub_X] at hr
  rintro y ⟨x, rfl⟩
  have hy : φ x ∈ (X ^ Fintype.card K - X : E[X]).roots := by
    rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero E Fintype.one_lt_card)]
    simp only [IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rw [← hc', ← map_pow, FiniteField.pow_card]
  rw [← hr, Multiset.mem_map] at hy
  obtain ⟨z, _, hz⟩ := hy
  exact ⟨z, hz⟩

lemma finiteField_alignment {F K E : Type*} [Field F] [Field K] [Field E]
    [Finite F] [Finite K] (φ : F →+* E) (ψ : K →+* E)
    (hc : Nat.card F = Nat.card K) :
    ∃ e : F ≃+* K, ∀ x, ψ (e x) = φ x := by
  let h := le_antisymm (finiteField_range_le φ ψ hc) (finiteField_range_le ψ φ hc.symm)
  let e := φ.rangeRestrictFieldEquiv.trans
    ((RingEquiv.subfieldCongr h).trans ψ.rangeRestrictFieldEquiv.symm)
  refine ⟨e, fun x => ?_⟩
  exact ψ.rangeRestrictFieldEquiv_apply_symm_apply _

noncomputable def binarySchur {H W : Type*} [Group H] [AddCommGroup W]
    [Module (ZMod 2) W] (σ : Representation (ZMod 2) H W) :
    Module.End (ZMod 2)[H] σ.asModule →+* Module.End (ZMod 2) W where
  toFun a := ((IntertwiningMap.equivAlgEnd σ).symm a).toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

lemma binarySchur_commute {H W : Type*} [Group H] [AddCommGroup W]
    [Module (ZMod 2) W] (σ : Representation (ZMod 2) H W)
    (a : Module.End (ZMod 2)[H] σ.asModule) (g : H) (x : W) :
    binarySchur σ a (σ g x) = σ g (binarySchur σ a x) :=
  IntertwiningMap.isIntertwining σ σ ((IntertwiningMap.equivAlgEnd σ).symm a) g x

/-- The diagonal extension, with compatibility for every binary intertwiner.
This is constructed below from homogeneity, not assumed in the final theorem. -/
structure AmbientScalars (C : ConstituentData ρ L) where
  action : C.SchurField →+* Module.End (ZMod 2) V
  intertwines : ∀ a (l : L) x, action a (ρ l x) = ρ l (action a x)
  maps : ∀ (f : IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype)) a x,
    action a (f x) = f (binarySchur C.space.toRepresentation a x)
  central : ∀ (f : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype)) a x,
    action a (f x) = f (action a x)

set_option backward.isDefEq.respectTransparency false in
noncomputable def ambientScalars [FiniteDimensional (ZMod 2) V]
    (C : ConstituentData ρ L) : AmbientScalars C := by
  classical
  let e₀ := C.decomposition.choose_spec.some
  let e := e₀.trans (LinearEquiv.piCongrRight fun _ => (constituentModuleEquiv C).symm)
  let φ := CommonScalarDiagonal.extend e
  refine {
    action := (binarySchur (ρ.comp L.subtype)).comp φ
    intertwines := fun a l x => binarySchur_commute (ρ.comp L.subtype) (φ a) l x
    maps := ?_
    central := ?_ }
  · intro f a x
    exact CommonScalarDiagonal.extend_map e (fun a b => mul_comm a b) a
      (IntertwiningMap.equivLinearMapAsModule _ _ f) x
  · intro f a x
    exact congrArg (fun t : Module.End (ZMod 2)[L]
        (Representation.asModule (ρ.comp L.subtype)) => t x)
      (CommonScalarDiagonal.extend_commute e (fun a b => mul_comm a b) a
        (IntertwiningMap.equivLinearMapAsModule _ _ f))

lemma AmbientScalars.other {C : ConstituentData ρ L} (A : AmbientScalars C)
    (hc : ⁅L, L₂⁆ = ⊥) (a : C.SchurField) (j : L₂) (x : V) :
    A.action a (ρ j x) = ρ j (A.action a x) := by
  let f : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype) :=
    { toLinearMap := ρ j
      isIntertwining' l := by
        ext v
        change ρ (j : G) (ρ (l : G) v) = ρ (l : G) (ρ (j : G) v)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        exact congrArg (fun g : G => ρ g v)
          (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc l.property) j j.property) }
  exact A.central f a x

/-- Scalars central in either restriction commute with both actors and
therefore define elements of the joint Schur ring. -/
noncomputable def jointSchur {F : Type*} [Semiring F]
    (hc : ⁅L, L₂⁆ = ⊥) (φ : F →+* Module.End (ZMod 2) V)
    (hl : ∀ a (l : L) x, φ a (ρ l x) = ρ l (φ a x))
    (hr : ∀ a (j : L₂) x, φ a (ρ j x) = ρ j (φ a x)) :
    F →+* Module.End (ZMod 2)[↥(L ⊔ L₂)]
      (Representation.asModule (ρ.comp (L ⊔ L₂).subtype)) :=
  (IntertwiningMap.equivAlgEnd (ρ.comp (L ⊔ L₂).subtype)).toRingEquiv.toRingHom.comp
    { toFun a :=
        { toLinearMap := φ a
          isIntertwining' g := by
            ext x
            have hg : (g : G) ∈ (productMap hc).range := by
              rw [productMap_range hc]
              exact g.property
            obtain ⟨⟨l, j⟩, heq⟩ := hg
            change φ a (ρ (g : G) x) = ρ (g : G) (φ a x)
            rw [← heq]
            change φ a (ρ ((l : G) * (j : G)) x) =
              ρ ((l : G) * (j : G)) (φ a x)
            simp only [map_mul, Module.End.mul_apply, hl, hr] }
      map_zero' := by ext x; exact congrArg (fun f : Module.End (ZMod 2) V => f x) φ.map_zero
      map_one' := by ext x; exact congrArg (fun f : Module.End (ZMod 2) V => f x) φ.map_one
      map_add' a b := by ext x; exact congrArg (fun f : Module.End (ZMod 2) V => f x) (φ.map_add a b)
      map_mul' a b := by ext x; exact congrArg (fun f : Module.End (ZMod 2) V => f x) (φ.map_mul a b) }

noncomputable def scalarRepresentation {F H W : Type*} [Semiring F] [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) H W) (φ : F →+* Module.End (ZMod 2) W)
    (hφ : ∀ a g x, φ a (σ g x) = σ g (φ a x)) :
    letI := Module.compHom W φ
    Representation F H W := by
  letI := Module.compHom W φ
  exact {
    toFun g :=
      { toFun := σ g
        map_add' := (σ g).map_add
        map_smul' := fun a x => (hφ a g x).symm }
    map_one' := by ext x; exact congrArg (fun f : Module.End (ZMod 2) W => f x) σ.map_one
    map_mul' g h := by ext x; exact congrArg (fun f : Module.End (ZMod 2) W => f x) (σ.map_mul g h) }

noncomputable def commonScalarsOfAlignment [FiniteDimensional (ZMod 2) V]
    {C : ConstituentData ρ L} {D : ConstituentData ρ L₂}
    (A : AmbientScalars C) (B : AmbientScalars D)
    (e : C.SchurField ≃+* D.SchurField)
    (he : ∀ a, B.action (e a) = A.action a)
    (hc : ⁅L, L₂⁆ = ⊥) : CommonScalarData C D := by
  let α := binarySchur C.space.toRepresentation
  let β := (binarySchur D.space.toRepresentation).comp e.toRingHom
  letI := Module.compHom C.space.toSubmodule α
  letI := Module.compHom D.space.toSubmodule β
  letI := Module.compHom V A.action
  letI := ZMod.instIsScalarTower 2 C.SchurField C.space.toSubmodule
  letI := ZMod.instIsScalarTower 2 C.SchurField D.space.toSubmodule
  letI := ZMod.instIsScalarTower 2 C.SchurField V
  letI : FiniteDimensional C.SchurField C.space.toSubmodule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  letI : FiniteDimensional C.SchurField D.space.toSubmodule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  refine {
    F := C.SchurField
    left := scalarRepresentation C.space.toRepresentation α
      (binarySchur_commute C.space.toRepresentation)
    right := scalarRepresentation D.space.toRepresentation β
      (fun a => binarySchur_commute D.space.toRepresentation (e a))
    left_apply := fun _ _ => rfl
    right_apply := fun _ _ => rfl
    left_schur := ?_
    right_schur := ?_
    left_ambient_linear := fun l a x => (A.intertwines a l x).symm
    right_ambient_linear := fun j a x => (A.other hc a j x).symm
    left_maps_linear := fun f a x => (A.maps f a x).symm
    right_maps_linear := ?_ }
  · intro f
    exact ⟨IntertwiningMap.equivAlgEnd C.space.toRepresentation f, fun _ => rfl⟩
  · intro f
    refine ⟨e.symm (IntertwiningMap.equivAlgEnd D.space.toRepresentation f), fun x => ?_⟩
    change f x = binarySchur D.space.toRepresentation
      (e (e.symm (IntertwiningMap.equivAlgEnd D.space.toRepresentation f))) x
    rw [e.apply_symm_apply]
    rfl
  · intro f a x
    change f (binarySchur D.space.toRepresentation (e a) x) = A.action a (f x)
    rw [← he a]
    exact (B.maps f (e a) x).symm

/-- The full Schur fields of the two homogeneous restrictions admit common
scalars compatible with both ambient actions and every constituent embedding. -/
public theorem commonScalars : CommonScalarTheorem.{u,v} := by
  intro G _ _ V _ _ _ ρ L L₂ C D hc hirr hcard
  let A := ambientScalars C
  let B := ambientScalars D
  have hc' : ⁅L₂, L⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
  let σ : Representation (ZMod 2) ↥(L ⊔ L₂) V := ρ.comp (L ⊔ L₂).subtype
  let : Representation.IsIrreducible σ := hirr
  let φ := jointSchur hc A.action A.intertwines (A.other hc)
  let ψ := jointSchur hc B.action (B.other hc') B.intertwines
  obtain ⟨e, he⟩ := finiteField_alignment φ ψ hcard
  refine ⟨commonScalarsOfAlignment A B e (fun a => ?_) hc⟩
  exact congrArg (binarySchur σ) (he a)

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
