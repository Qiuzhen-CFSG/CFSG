module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Conjugation.Coordinates
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SemidirectPerfect
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Group

/-!
# Perfection of the unitary-five plane semidirect product

The coordinate action is the actual homomorphism `Parameters.planeAction`,
re-exported from `Levi.Conjugation.Coordinates`: a determinant-one matrix A
sends `(x,z)` to `(A*x,A*z*A*)`.

Choose a generator a of the multiplicative group of the field of order 16.
The diagonal actor `diag(a,a⁻¹)` has vector weights a and a⁻¹ and matrix
weights a⁵, a⁻³, a³ and a⁻⁵. None is one, so its only fixed parameter is
the identity. On the finite parameter group its commutator map is therefore
surjective. Thus every parameter is an action commutator, and the perfectness
of SL₂ makes the whole semidirect product perfect.

The SL₂-to-PSL₂ equivalence is the canonical central quotient, and the
SL₂ two-core is trivial. Identifying the geometric solvable residual remains
with the plane-parabolic assembly; no residual or perfection assumption is
used here.

Source: the plane-parabolic calculation for Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(I)(7) and (II),
printed pp.263--264 of `refs/quasithin.pdf`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
open scoped MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore.ResidualAction
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

/-- The determinant-one diagonal element associated with a nonzero scalar. -/
def diagonalActor (a : Fˣ) : SL(2, F) :=
  ⟨Matrix.diagonal (fun i => ((![a, a⁻¹] : Fin 2 → Fˣ) i : F)), by
    simp⟩

/-- The two vector weights of the diagonal action. -/
theorem diagonalActor_x (a : Fˣ) (u : Parameters J) (i : Fin 2) :
    (Parameters.planeAction (diagonalActor a) u).x i =
      ((![a, a⁻¹] : Fin 2 → Fˣ) i : F) * u.x i := by
  rw [Parameters.planeAction_x]
  fin_cases i <;> simp [diagonalActor, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The four matrix weights, with fourth-power field conjugation. -/
theorem diagonalActor_z (hconj : ∀ b, J.conj b = b ^ 4)
    (a : Fˣ) (u : Parameters J) (i j : Fin 2) :
    (Parameters.planeAction (diagonalActor a) u).z i j =
      (((![a, a⁻¹] : Fin 2 → Fˣ) i * (![a, a⁻¹] : Fin 2 → Fˣ) j ^ 4 : Fˣ) : F) *
        u.z i j := by
  rw [Parameters.planeAction_z]
  fin_cases i <;> fin_cases j <;>
    simp [diagonalActor, planeAdjoint, Matrix.mul_apply, Fin.sum_univ_two, hconj] <;> ring

private theorem diagonal_weights (a : Fˣ) (ha : orderOf a = 15) :
    (∀ i, (![a, a⁻¹] : Fin 2 → Fˣ) i ≠ 1) ∧
    (∀ i j, (![a, a⁻¹] : Fin 2 → Fˣ) i * (![a, a⁻¹] : Fin 2 → Fˣ) j ^ 4 ≠ 1) := by
  have hp (k : ℕ) (hk : ¬ 15 ∣ k) : a ^ k ≠ 1 := by
    intro h
    exact hk (ha ▸ orderOf_dvd_of_pow_eq_one h)
  have h1 : a ≠ 1 := by simpa using hp 1 (by decide)
  constructor
  · intro i
    fin_cases i <;> simpa using h1
  · intro i j
    fin_cases i <;> fin_cases j <;> dsimp
    · have he : a * a ^ 4 = a ^ 5 := by group
      rw [he]
      exact hp 5 (by decide)
    · have he : a * a⁻¹ ^ 4 = (a ^ 3)⁻¹ := by group
      rw [he]
      simpa only [ne_eq, inv_eq_one] using hp 3 (by decide)
    · have he : a⁻¹ * a ^ 4 = a ^ 3 := by group
      rw [he]
      exact hp 3 (by decide)
    · have he : a⁻¹ * a⁻¹ ^ 4 = (a ^ 5)⁻¹ := by group
      rw [he]
      simpa only [ne_eq, inv_eq_one] using hp 5 (by decide)

/-- A scalar of order fifteen gives an actor fixing only the identity parameter. -/
theorem diagonalActor_fixedPointFree (hconj : ∀ b, J.conj b = b ^ 4)
    (a : Fˣ) (ha : orderOf a = 15) :
    MonoidHom.FixedPointFree (Parameters.planeAction (J := J) (diagonalActor a)) := by
  obtain ⟨hx, hz⟩ := diagonal_weights a ha
  intro u hu
  have zero_of_weight (b : Fˣ) (hb : b ≠ 1) (v : F) (hv : (b : F) * v = v) : v = 0 := by
    by_contra hv0
    exact hb (Units.val_inj.mp ((mul_eq_right₀ hv0).mp hv))
  apply Parameters.ext
  · funext i
    apply zero_of_weight _ (hx i)
    simpa only [diagonalActor_x] using congrArg (fun v : Parameters J => v.x i) hu
  · funext i j
    apply zero_of_weight _ (hz i j)
    simpa only [diagonalActor_z J hconj] using congrArg (fun v : Parameters J => v.z i j) hu

/-- The multiplicative group of the matrix field has a generator of order fifteen. -/
theorem exists_order_fifteen [Finite F] (hcard : Nat.card F = 16) :
    ∃ a : Fˣ, orderOf a = 15 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  exact ⟨a, by simpa only [Nat.card_units, hcard] using ha⟩

variable [CharP F 2]

/-- Every parameter is an actual action commutator; this is derived from the
coordinate weights, rather than an assumed generation property. -/
theorem action_differences [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ b, J.conj b = b ^ 4) :
    ∀ u : Parameters J, ∃ A : SL(2, F), ∃ v : Parameters J,
      Parameters.planeAction A v * v⁻¹ = u := by
  let : Finite (Parameters J) := Finite.of_injective
    (fun u : Parameters J => (u.x, u.z)) (by
      intro u v h
      exact Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  obtain ⟨a, ha⟩ := exists_order_fifteen hcard
  have hf := diagonalActor_fixedPointFree J hconj a ha
  intro u
  obtain ⟨v, hv⟩ := hf.commutatorMap_surjective u⁻¹
  refine ⟨diagonalActor a, v, ?_⟩
  simpa only [MonoidHom.commutatorMap_apply, div_eq_mul_inv, _root_.mul_inv_rev, inv_inv] using
    congrArg Inv.inv hv

open scoped commutatorElement in
/-- The literal embedded parameter and special-linear subgroups satisfy `[U,SL₂] = U`. -/
theorem unipotent_commutator_eq [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ b, J.conj b = b ^ 4) :
    ⁅(SemidirectProduct.inl : Parameters J →*
        Parameters J ⋊[Parameters.planeAction] SL(2, F)).range,
      (SemidirectProduct.inr : SL(2, F) →*
        Parameters J ⋊[Parameters.planeAction] SL(2, F)).range⁆ =
      (SemidirectProduct.inl : Parameters J →*
        Parameters J ⋊[Parameters.planeAction] SL(2, F)).range := by
  apply le_antisymm
  · rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact Subgroup.commutator_le_left _ _
  · rintro _ ⟨u, rfl⟩
    obtain ⟨A, v, hv⟩ := action_differences J hcard hconj u
    rw [← hv, map_mul, map_inv, SemidirectProduct.inl_aut]
    have h := Subgroup.commutator_mem_commutator
      (show (SemidirectProduct.inr A : Parameters J ⋊[Parameters.planeAction] SL(2, F)) ∈
        (SemidirectProduct.inr : SL(2, F) →*
          Parameters J ⋊[Parameters.planeAction] SL(2, F)).range from ⟨A, rfl⟩)
      (show (SemidirectProduct.inl v : Parameters J ⋊[Parameters.planeAction] SL(2, F)) ∈
        (SemidirectProduct.inl : Parameters J →*
          Parameters J ⋊[Parameters.planeAction] SL(2, F)).range from ⟨v, rfl⟩)
    rw [Subgroup.commutator_comm] at h
    simpa only [commutatorElement_def, map_inv] using h

omit [CharP F 2] in
/-- Perfection of the acting group, from the elementary-matrix commutator calculation. -/
theorem sl_isPerfect [Finite F] (hcard : Nat.card F = 16) :
    Group.IsPerfect SL(2, F) := by
  obtain ⟨a, ha⟩ := exists_order_fifteen hcard
  refine ⟨Matrix.SL2.commutator_eq_top a.ne_zero ?_⟩
  intro h
  have hunit : a ^ 2 = 1 := Units.ext (by simpa using h)
  have hd := orderOf_dvd_of_pow_eq_one hunit
  rw [ha] at hd
  norm_num at hd

/-- The explicit plane-unipotent semidirect product over the field of order sixteen
is perfect, with no additional commutator-generation premise. -/
theorem semidirect_isPerfect [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ b, J.conj b = b ^ 4) :
    Group.IsPerfect (Parameters J ⋊[Parameters.planeAction] SL(2, F)) := by
  let : Group.IsPerfect SL(2, F) := sl_isPerfect hcard
  exact Atlas.GroupTheory.semidirect_isPerfect_of_action_differences
    (Parameters.planeAction (J := J)) (action_differences J hcard hconj)

/-- In characteristic two the actual central quotient SL₂ → PSL₂ is an isomorphism. -/
noncomputable def slEquivPSL : SL(2, F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  Atlas.RankOneFieldAutomorphisms.slEquivPSL

/-- The equivalence uses the canonical quotient map on each representative. -/
@[simp] theorem slEquivPSL_apply (A : SL(2, F)) :
    slEquivPSL A = QuotientGroup.mk A := rfl

/-- The defining-characteristic two-core of the acting matrix group is trivial. -/
theorem sl_twoCore_eq_bot [Finite F] : pCore 2 SL(2, F) = ⊥ :=
  Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot

end Theory.SpecificGroups.UnitaryFive.PlaneCore.ResidualAction
