module

/-
The scalar-kernel calculation adapts the corresponding calculation in
Theory/SpecificGroups/SymplecticFour/EvenProjective.lean, based on ATLAS by
Gerald Höhn and the ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Covered by the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: start from trivial action on projective points instead of centrality.
-/

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Algebra.CharP.Two

/-!
# The faithful polar action and its concrete inner-field permutations

Projective points are the one-dimensional subspaces of the actual symplectic
four-space. Their orthogonality relation uses the displayed matrix form, and
the stabilizer of the standard point is the actual point parabolic. The group
acts faithfully in characteristic two: a matrix fixing every line is scalar,
and form preservation makes that scalar one.

Entrywise field maps and symplectic matrices give explicit permutations of
these points. Their action intertwines the actual inner-field automorphism
of the matrix group. This supplies the faithful-action step of the geometric
route to the diagram-preserving automorphism theorem; it does not assert that
an arbitrary diagram-preserving automorphism has such a geometric action.

Source: the automorphism fact used in Aschbacher--Smith F.1.12, printed
pp.263--264 of `refs/quasithin.pdf`.
-/

@[expose] public section

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open Projectivization
variable {F : Type*} [Field F]

abbrev ProjectivePoint (F : Type*) [Field F] := Projectivization F (Vector F)

def projectiveAction : Sp F →* Equiv.Perm (ProjectivePoint F) :=
  MulAction.toPermHom _ _

@[simp] theorem projectiveAction_apply (g : Sp F) (p : ProjectivePoint F) :
    projectiveAction g p = g • p := rfl

theorem submodule_smul (g : Sp F) (p : ProjectivePoint F) :
    (g • p).submodule = p.submodule.map (toLinear g).toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv => simp [smul_mk, Submodule.map_span]

theorem projective_stabilizer (p : ProjectivePoint F) :
    MulAction.stabilizer (Sp F) p = stabilizer p.submodule := by
  ext g
  change g • p = p ↔ p.submodule.map (toLinear g).toLinearMap = p.submodule
  rw [← submodule_smul]
  exact ⟨congrArg Projectivization.submodule, fun h => Projectivization.submodule_injective h⟩

def standardPoint : ProjectivePoint F := Projectivization.mk'' (point F) finrank_point

@[simp] theorem standardPoint_submodule : (standardPoint (F := F)).submodule = point F :=
  Projectivization.submodule_mk'' _ _

theorem standardPoint_stabilizer :
    MulAction.stabilizer (Sp F) (standardPoint (F := F)) = pointParabolic := by
  rw [projective_stabilizer, standardPoint_submodule]
  rfl

def Orthogonal (p q : ProjectivePoint F) : Prop :=
  ∀ x ∈ p.submodule, ∀ y ∈ q.submodule, form F x y = 0

theorem orthogonal_mk_iff (v w : Vector F) (hv : v ≠ 0) (hw : w ≠ 0) :
    Orthogonal (mk F v hv) (mk F w hw) ↔ form F v w = 0 := by
  constructor
  · intro h
    exact h v (Submodule.mem_span_singleton_self v) w (Submodule.mem_span_singleton_self w)
  · intro h x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [map_smul, h]

theorem orthogonal_smul_iff (g : Sp F) (p q : ProjectivePoint F) :
    Orthogonal (g • p) (g • q) ↔ Orthogonal p q := by
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw => simp only [smul_mk, orthogonal_mk_iff, preserves_form]

private theorem scalar_of_projectiveAction_eq_one (g : Sp F)
    (hg : projectiveAction g = 1) : ∃ a : F, ∀ v : Vector F, g • v = a • v := by
  obtain ⟨a, ha⟩ := (toLinear g).toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (fun v => by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · rw [LinearIndependent.pair_iff' hv]
        have h : g • mk F v hv = mk F v hv := by
          simpa using Equiv.congr_fun hg (mk F v hv)
        obtain ⟨c, hc⟩ := (mk_eq_mk_iff' F _ _ _ _).mp h
        exact fun hli => hli c hc)
  exact ⟨a, fun v => congrArg (fun l : Vector F →ₗ[F] Vector F => l v) ha⟩

theorem projectiveAction_injective [CharP F 2] :
    Function.Injective (projectiveAction (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨a, ha⟩ := scalar_of_projectiveAction_eq_one g hg
  have hs := preserves_form g (e (F := F) 0) (Pi.single (.inr 0) 1)
  rw [ha, ha] at hs
  have hsq : a ^ 2 = 1 := by
    simpa [map_smul, form_apply, e, Pi.single_apply, pow_two] using hs
  have haone : a = 1 := CharTwo.sq_injective (by simpa using hsq)
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have h := congrFun (ha (Pi.single j 1)) i
  simpa [haone, smul_eq_mulVec, Matrix.mulVec_single, Pi.single_apply,
    Matrix.one_apply, eq_comm] using h

def fieldVector (σ : F ≃+* F) : Vector F →ₛₗ[σ.toRingHom] Vector F where
  toFun v i := σ (v i)
  map_add' v w := by ext i; exact map_add σ _ _
  map_smul' a v := by ext i; exact map_mul σ _ _

@[simp] theorem fieldVector_apply (σ : F ≃+* F) (v : Vector F) (i : Fin 2 ⊕ Fin 2) :
    fieldVector σ v i = σ (v i) := rfl

theorem fieldVector_injective (σ : F ≃+* F) : Function.Injective (fieldVector σ) := by
  intro v w h
  ext i
  exact σ.injective (congrFun h i)

theorem fieldVector_ne_zero (σ : F ≃+* F) (v : Vector F) (hv : v ≠ 0) :
    fieldVector σ v ≠ 0 := by
  intro h
  exact hv (fieldVector_injective σ (h.trans (map_zero _).symm))

def fieldProjective (σ : F ≃+* F) : Equiv.Perm (ProjectivePoint F) where
  toFun := Projectivization.map (fieldVector σ) (fieldVector_injective σ)
  invFun := Projectivization.map (fieldVector σ.symm) (fieldVector_injective σ.symm)
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [map_mk]
      congr 1
      ext i
      exact σ.symm_apply_apply _
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [map_mk]
      congr 1
      ext i
      exact σ.apply_symm_apply _

@[simp] theorem fieldProjective_mk (σ : F ≃+* F) (v : Vector F) (hv : v ≠ 0) :
    fieldProjective σ (mk F v hv) =
      mk F (fieldVector σ v) (fieldVector_ne_zero σ v hv) := rfl

theorem form_fieldVector (σ : F ≃+* F) (v w : Vector F) :
    form F (fieldVector σ v) (fieldVector σ w) = σ (form F v w) := by
  simp [form_apply, fieldVector]
  rfl

theorem orthogonal_fieldProjective_iff (σ : F ≃+* F) (p q : ProjectivePoint F) :
    Orthogonal (fieldProjective σ p) (fieldProjective σ q) ↔ Orthogonal p q := by
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw =>
      simp only [fieldProjective_mk, orthogonal_mk_iff, form_fieldVector,
        EmbeddingLike.map_eq_zero_iff]

theorem fieldVector_smul (σ : F ≃+* F) (g : Sp F) (v : Vector F) :
    fieldVector σ (g • v) = fieldAutomorphism σ g • fieldVector σ v := by
  ext i
  change σ (∑ j, g.val i j * v j) = ∑ j, σ (g.val i j) * σ (v j)
  simp

theorem fieldProjective_smul (σ : F ≃+* F) (g : Sp F) (p : ProjectivePoint F) :
    fieldProjective σ (g • p) = fieldAutomorphism σ g • fieldProjective σ p := by
  induction p using Projectivization.ind with
  | h v hv => simp only [smul_mk, fieldProjective_mk, fieldVector_smul]

def innerFieldProjective (g : Sp F) (σ : F ≃+* F) : Equiv.Perm (ProjectivePoint F) :=
  projectiveAction g * fieldProjective σ

@[simp] theorem innerFieldProjective_apply (g : Sp F) (σ : F ≃+* F) (p : ProjectivePoint F) :
    innerFieldProjective g σ p = g • fieldProjective σ p := rfl

theorem orthogonal_innerFieldProjective_iff (g : Sp F) (σ : F ≃+* F)
    (p q : ProjectivePoint F) :
    Orthogonal (innerFieldProjective g σ p) (innerFieldProjective g σ q) ↔ Orthogonal p q := by
  simp only [innerFieldProjective_apply, orthogonal_smul_iff, orthogonal_fieldProjective_iff]

theorem innerFieldProjective_smul (g h : Sp F) (σ : F ≃+* F) (p : ProjectivePoint F) :
    innerFieldProjective g σ (h • p) =
      ((MulAut.conj g) * fieldAutomorphism σ) h • innerFieldProjective g σ p := by
  simp only [innerFieldProjective_apply, fieldProjective_smul]
  change g • (fieldAutomorphism σ h • fieldProjective σ p) =
    (g * fieldAutomorphism σ h * g⁻¹) • (g • fieldProjective σ p)
  simp only [mul_smul, inv_smul_smul]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
