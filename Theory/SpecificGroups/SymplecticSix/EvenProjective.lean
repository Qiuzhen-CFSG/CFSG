module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The transvection and scalar arguments adapt Atlas/LinearGroups/Symplectic/
{Transvection,TransvectionImage,Center}.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Covered by the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: use the existing CFSG six-space carrier and form, specialize to
characteristic two, and keep the matrix implementation private.
-/

public import Theory.SpecificGroups.SymplecticSix.Basic
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Center
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The central quotient in characteristic two

A central matrix commutes with every symplectic transvection, so it preserves
every line and is scalar. Preservation of a hyperbolic pair makes its scalar
square to one; in characteristic two the scalar is one. The quotient map
therefore gives an actual equivalence Sp₆(F) ≃ PSp₆(F). The finite-field
cardinality hypothesis alone supplies characteristic two.

Source: the ATLAS transvection calculation attributed above. This comparison
supports the PSp₆(2) case of Aschbacher–Smith, Theorem 0.1.2(2), printed p.4
(repeated as Theorem 0.1.1(2), printed p.482).
-/

public noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticSix.EvenProjective
variable {F : Type*} [Field F]

private theorem form_self (v : Vector F) : form F v v = 0 := by
  simp [form_apply, mul_comm]

private theorem form_swap (v w : Vector F) : form F v w = -form F w v := by
  simp only [form_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private def transvectionMap (v : Vector F) : Module.End F (Vector F) :=
  LinearMap.transvection ((form F).flip v) v

private theorem transvectionMap_apply (v x : Vector F) :
    transvectionMap v x = x + form F x v • v := rfl

private def transvection (v : Vector F) : Sp F :=
  ⟨LinearMap.toMatrix' (transvectionMap v), by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 3) F)
      (LinearMap.toMatrix' (transvectionMap v)) (LinearMap.toMatrix' (transvectionMap v))
    have hpres : (form F).comp (transvectionMap v) (transvectionMap v) = form F := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change form F (transvectionMap v x) (transvectionMap v y) = form F x y
      simp only [transvectionMap_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, form_self, mul_zero, add_zero]
      rw [form_swap v y]
      ring
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg, Matrix.neg_mul, form] using hm⟩

private theorem transvection_apply (v x : Vector F) :
    transvection v • x = x + form F x v • v := by
  change (LinearMap.toMatrix' (transvectionMap v)) *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, transvectionMap_apply]

private theorem exists_form_left {v : Vector F} (hv : v ≠ 0) :
    ∃ x, form F x v = 1 := by
  have hex : ∃ w, form F w v ≠ 0 := by
    by_contra! h
    apply hv
    funext i
    cases i with
    | inl i =>
      have hi := h (Pi.single (.inr i) 1)
      simpa [form_apply, Pi.single_apply] using hi
    | inr i =>
      have hi := h (e i)
      simpa [form_apply, e, Pi.single_apply] using hi
  obtain ⟨w, hw⟩ := hex
  exact ⟨(form F w v)⁻¹ • w, by simp [map_smul, hw]⟩

private theorem central_preserves_lines (g : Sp F) (hg : g ∈ Subgroup.center (Sp F))
    (v : Vector F) (hv : v ≠ 0) : ∃ a : F, a • v = g • v := by
  obtain ⟨x, hx⟩ := exists_form_left hv
  have h := congrArg (fun t : Sp F => t • x)
    (Subgroup.mem_center_iff.mp hg (transvection v))
  simp only [mul_smul, transvection_apply] at h
  change g • x + form F (g • x) v • v = toLinear g (x + form F x v • v) at h
  rw [(toLinear g).map_add, (toLinear g).map_smul, hx, one_smul] at h
  exact ⟨form F (g • x) v, add_left_cancel h⟩

private theorem central_is_scalar (g : Sp F) (hg : g ∈ Subgroup.center (Sp F)) :
    ∃ a : F, ∀ x : Vector F, g • x = a • x := by
  obtain ⟨a, ha⟩ := (toLinear g).toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (fun v => by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · rw [LinearIndependent.pair_iff' hv]
        obtain ⟨a, ha⟩ := central_preserves_lines g hg v hv
        exact fun h => h a ha)
  exact ⟨a, fun x => congrArg (fun l : Vector F →ₗ[F] Vector F => l x) ha⟩

/-- The actual six-space matrix group has trivial center in characteristic two. -/
theorem center_eq_bot [CharP F 2] : Subgroup.center (Sp F) = ⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨a, ha⟩ := central_is_scalar g hg
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

/-- The equivalence is induced by the actual central quotient map. -/
def equiv [CharP F 2] : Sp F ≃* (Sp F ⧸ Subgroup.center (Sp F)) :=
  ((QuotientGroup.quotientMulEquivOfEq center_eq_bot).trans
    QuotientGroup.quotientBot).symm

theorem equiv_apply [CharP F 2] (g : Sp F) : equiv g = QuotientGroup.mk g := by rfl

/-- A field of two-power order has characteristic two. -/
theorem charTwo_of_card [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) : CharP F 2 := by
  let := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
end Theory.SpecificGroups.SymplecticSix.EvenProjective
