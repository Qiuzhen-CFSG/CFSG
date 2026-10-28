module

public import Theory.GroupTheory.ElementaryEightParabolicRecognition
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Conjugation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
/-!
# Recognition in a binary four-space point stabilizer

The actual quotient action of a nonzero-vector stabilizer has an elementary
abelian displacement kernel of order eight and quotient GL₃(2) of order 168.
Its conjugation kernel on the displacement group is precisely that group.

Consequently a faithfully embedded group whose quotient by its nontrivial
two-core is PSL₃(2) fills the point stabilizer. The elementary-eight recognition
lemma supplies the irreducibility argument. We also construct the genuine
GL₄(2)–PSL₄(2) equivalence: binary determinants are one and the special-linear
center is trivial.

Source: Aschbacher–Smith I.5.10, combined manuscript of 1 March 2004,
printed p.422. The application is the point stabilizer in the reconstructed
quotient of the fifteen-point permutation module.
-/

public section

open Module
namespace Theory.LinearAlgebra.BinaryFourPointStabilizer
open BinaryFivePointStabilizer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
theorem card_linearGroup_three [FiniteDimensional (ZMod 2) E]
    (hE : finrank (ZMod 2) E = 3) : Nat.card (E ≃ₗ[ZMod 2] E) = 168 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) E hE
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ZMod.card]

theorem quotient_finrank [FiniteDimensional (ZMod 2) E] (z : E) (hz : z ≠ 0)
    (hE : finrank (ZMod 2) E = 4) : finrank (ZMod 2) (QuotientSpace z) = 3 := by
  have h := (line z).finrank_quotient_add_finrank
  rw [finrank_span_singleton hz, hE] at h
  change finrank (ZMod 2) (QuotientSpace z) + 1 = 4 at h
  omega

theorem card_kernel [FiniteDimensional (ZMod 2) E] (z : E) (hz : z ≠ 0)
    (hE : finrank (ZMod 2) E = 4) : Nat.card (kernel z) = 8 := by
  rw [Nat.card_congr (kernelDisplacementEquiv z).toEquiv]
  change Nat.card (QuotientSpace z →ₗ[ZMod 2] line z) = 8
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap,
    quotient_finrank z hz hE, finrank_span_singleton hz]
  norm_num

theorem card_stabilizer [FiniteDimensional (ZMod 2) E] (z : E) (hz : z ≠ 0)
    (hE : finrank (ZMod 2) E = 4) : Nat.card (stabilizer z) = 1344 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (kernel z),
    Nat.card_congr (quotientEquiv z).toEquiv,
    card_linearGroup_three (quotient_finrank z hz hE), card_kernel z hz hE]

theorem surjective_of_quotient [FiniteDimensional (ZMod 2) E]
    (z : E) (hz : z ≠ 0) (hE : finrank (ZMod 2) E = 4)
    {A : Type*} [Group A] [Finite A] (j : A →* stabilizer z)
    (hj : Function.Injective j) (hquot : Nat.card (A ⧸ pCore 2 A) = 168)
    (hcore : pCore 2 A ≠ ⊥) : Function.Surjective j := by
  let : Finite E := Module.finite_of_finite (ZMod 2)
  let : Finite (E ≃ₗ[ZMod 2] E) :=
    Finite.of_injective (fun a : E ≃ₗ[ZMod 2] E => (a : E → E)) DFunLike.coe_injective
  exact ElementaryEightParabolic.surjective_of_quotient_card (kernel z)
    (card_kernel z hz hE) (card_stabilizer z hz hE) (conjugation_kernel z hz)
    j hj hquot hcore

private theorem binary_toGL_surjective {n : Type*} [Fintype n] [DecidableEq n] :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup n (ZMod 2) →* Matrix.GeneralLinearGroup n (ZMod 2)) := by
  intro a
  have hunits : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
  have hd : Matrix.det (a : Matrix n n (ZMod 2)) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hunits (Matrix.GeneralLinearGroup.det a)]
    rfl
  exact ⟨⟨a, hd⟩, Units.ext rfl⟩

/-- Actual comparison with the central quotient defining PSL₄(2). -/
noncomputable def equivPSL4 [FiniteDimensional (ZMod 2) E]
    (hE : finrank (ZMod 2) E = 4) :
    (E ≃ₗ[ZMod 2] E) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) E hE
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    change a = 1
    obtain ⟨c, hc, heq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ha
    have hc1 : c = 1 :=
      (by decide : ∀ c : ZMod 2, c ^ 4 = 1 → c = 1) c (by simpa using hc)
    apply Subtype.ext
    simpa [hc1] using heq.symm
  exact e.trans ((MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, binary_toGL_surjective⟩).symm.trans
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcenter.symm)))
end Theory.LinearAlgebra.BinaryFourPointStabilizer
