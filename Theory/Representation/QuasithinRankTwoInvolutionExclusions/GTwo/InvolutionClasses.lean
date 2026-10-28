module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.GTwo.LongRoot
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup

/-!
# Long-root recognition for involutions of the full group G₂(2)

Every involution is conjugate into the six-root Sylow subgroup. Its unique
binary parameters satisfy the explicit square-one equation. A kernel-checked
exhaustion leaves the identity, seven explicit conjugates of `rootA 1`, or twenty
other candidates. For each other candidate a short word gives a product with
one of its conjugates whose cube and fourth power are both nonidentity. Such a
product cannot have order at most four.

The finite certificates use the actual eight-dimensional octonion action.
Checking four successive vectors avoids repeatedly expanding nested powers of
root automorphisms. The final corollary has the requested moved-rank hypothesis
on the actual trace-zero quotient module; the group-theoretic recognition
already follows from the product-order bound alone.

Source: Aschbacher–Smith, proof of 6.2.19, printed p.691 / PDF p.708,
case G.11.2(6), printed p.364 / PDF p.375. Root conventions and the full-group
Sylow marking are inherited from the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`. The finite witnesses below
are checked directly in Lean and do not depend on an external computation.
-/

public section

open scoped Pointwise
open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit
namespace Representation.RankTwo.GTwo
namespace InvolutionClasses
set_option maxRecDepth 4096
private def longRootParameters : Fin 7 → Fin 6 → K :=
  ![![0,0,0,0,1,0],![0,1,0,0,0,0],![0,1,1,1,1,0],![1,0,0,0,0,0],![1,0,0,0,1,0],![1,1,0,0,0,0],![1,1,1,1,1,0]]
private def longRootConjugator : Fin 7 → G :=
  ![weylS * weylR,weylR,rootF 1 * weylS * rootE 1 * weylR,1,weylS * rootE 1 * weylR,rootE 1 * weylR,rootF 1 * weylS * weylR]
private def otherParameters : Fin 20 → Fin 6 → K :=
  ![![0,0,1,1,0,1],
    ![0,1,0,0,0,1],
    ![1,0,1,1,0,1],
    ![1,1,0,0,0,1],
    ![0,0,0,0,0,1],
    ![0,1,1,1,0,1],
    ![1,0,0,0,0,1],
    ![1,1,1,1,0,1],
    ![0,0,1,0,1,0],
    ![0,1,0,1,0,0],
    ![1,0,1,0,1,0],
    ![1,1,0,1,0,0],
    ![0,0,0,1,0,0],
    ![0,0,0,1,1,0],
    ![1,0,0,1,0,0],
    ![1,0,0,1,1,0],
    ![0,0,1,0,0,0],
    ![0,1,1,0,0,0],
    ![1,0,1,0,0,0],
    ![1,1,1,0,0,0]]
private def productConjugator : Fin 20 → G :=
  ![weylS,
    weylS,
    weylS,
    weylS,
    rootC 1 * weylS,
    rootC 1 * weylS,
    rootC 1 * weylS,
    rootC 1 * weylS,
    weylR * weylS,
    weylR * weylS,
    weylR * weylS,
    weylR * weylS,
    rootF 1 * weylS * weylR,
    rootF 1 * weylS * weylR,
    rootF 1 * weylS * weylR,
    rootF 1 * weylS * weylR,
    rootF 1 * weylS * weylR * weylS,
    rootF 1 * weylS * weylR * weylS,
    rootF 1 * weylS * weylR * weylS,
    rootF 1 * weylS * weylR * weylS]
private def conjugateProduct (i : Fin 20) : G :=
  let u := unipotentProduct (otherParameters i)
  let h := productConjugator i
  u * (h⁻¹ * u * h)
private def cubeRow : Fin 20 → Fin 8 :=
  ![0,0,0,0,0,0,0,0,0,1,0,0,1,1,0,1,1,0,3,1]
private def fourthRow : Fin 20 → Fin 8 :=
  ![6,0,6,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0]
private def trajectory : Fin 20 → Fin 5 → Carrier K :=
  ![
    ![![0,0,0,0,0,0,1,0],![0,1,0,0,0,0,0,1],![0,0,0,0,0,0,1,1],![1,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,1]],
    ![![0,0,0,0,0,0,1,0],![1,0,0,1,1,1,0,1],![1,1,0,0,0,1,1,1],![1,0,0,0,0,0,1,0],![1,1,0,1,1,1,0,1]],
    ![![0,0,0,0,0,0,1,0],![0,1,0,0,0,0,0,1],![0,0,0,0,0,0,1,1],![1,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,1]],
    ![![0,0,0,0,0,0,1,0],![1,0,0,1,1,1,0,1],![1,1,0,0,0,1,1,1],![1,0,0,0,0,0,1,0],![1,1,0,1,1,1,0,1]],
    ![![0,0,1,0,0,0,0,0],![1,1,0,0,0,1,0,0],![1,0,1,1,1,1,0,0],![1,0,1,0,0,0,0,0],![1,0,0,0,0,1,0,0]],
    ![![0,0,1,0,0,0,0,0],![1,0,0,0,0,1,0,0],![1,1,1,1,1,1,0,0],![1,0,1,0,0,0,0,0],![1,1,0,0,0,1,0,0]],
    ![![0,0,1,0,0,0,0,0],![1,1,0,0,0,1,0,0],![1,0,1,1,1,1,0,0],![1,0,1,0,0,0,0,0],![1,0,0,0,0,1,0,0]],
    ![![0,0,1,0,0,0,0,0],![1,0,0,0,0,1,0,0],![1,1,1,1,1,1,0,0],![1,0,1,0,0,0,0,0],![1,1,0,0,0,1,0,0]],
    ![![0,0,1,0,0,0,0,0],![0,0,1,1,1,1,0,1],![1,0,1,1,1,1,0,0],![1,0,1,0,0,1,0,1],![0,1,1,0,0,0,0,0]],
    ![![0,0,0,0,0,0,1,0],![0,0,1,1,1,1,1,1],![0,1,1,1,1,0,1,0],![0,1,0,1,1,0,1,1],![1,0,0,0,0,0,1,0]],
    ![![0,0,1,0,0,0,0,0],![0,0,1,1,1,1,0,1],![1,1,1,1,1,1,0,0],![1,1,1,0,0,1,0,1],![0,1,1,0,0,0,0,0]],
    ![![0,0,0,0,0,0,1,0],![0,1,1,1,1,0,1,1],![1,1,1,1,1,0,1,0],![1,0,0,1,1,1,1,1],![1,0,0,0,0,0,1,0]],
    ![![0,0,0,0,0,1,0,0],![0,0,1,1,1,1,1,0],![0,1,1,1,1,1,0,0],![0,1,1,0,0,1,1,0],![1,0,0,0,0,1,0,0]],
    ![![0,0,0,0,0,0,1,0],![1,1,0,1,1,1,1,0],![1,1,1,1,1,0,1,0],![0,1,1,0,0,1,1,0],![1,0,0,0,0,0,1,0]],
    ![![0,0,0,0,0,1,0,0],![0,0,1,1,1,1,1,0],![1,1,1,1,1,1,0,0],![1,1,1,0,0,1,1,0],![1,0,0,0,0,1,0,0]],
    ![![0,0,0,0,0,0,1,0],![0,1,0,1,1,1,1,0],![0,1,1,1,1,0,1,0],![0,1,1,0,0,1,1,0],![1,0,0,0,0,0,1,0]],
    ![![0,0,1,0,0,0,0,0],![1,1,1,0,0,1,0,1],![1,1,1,1,1,1,0,0],![0,1,1,1,1,1,0,1],![0,1,1,0,0,0,0,0]],
    ![![0,0,0,0,0,0,1,0],![1,0,0,1,1,0,1,1],![1,1,1,1,1,0,1,0],![1,1,1,1,1,1,1,1],![1,0,0,0,0,0,1,0]],
    ![![0,0,1,0,0,0,0,0],![1,1,1,0,0,1,0,1],![1,0,1,1,1,1,0,0],![0,0,1,1,1,1,0,1],![0,1,1,0,0,0,0,0]],
    ![![0,0,0,0,0,0,1,0],![1,0,0,1,1,1,1,1],![0,1,1,1,1,0,1,0],![0,1,1,1,1,0,1,1],![1,0,0,0,0,0,1,0]]]
private theorem trajectory_step : ∀ (i : Fin 20) (j : Fin 4),
    (conjugateProduct i).val (trajectory i j.castSucc) = trajectory i j.succ := by
  intro i
  fin_cases i <;>
    simp only [conjugateProduct, otherParameters, productConjugator, unipotentProduct, Fin.isValue] <;>
    decide +kernel
private theorem trajectory_end3 : ∀ i : Fin 20,
    trajectory i 3 (cubeRow i) ≠ trajectory i 0 (cubeRow i) := by
  decide +kernel
private theorem trajectory_end4 : ∀ i : Fin 20,
    trajectory i 4 (fourthRow i) ≠ trajectory i 0 (fourthRow i) := by
  decide +kernel

private theorem conjugateProduct_cube_ne_one (i : Fin 20) : conjugateProduct i ^ 3 ≠ 1 := by
  intro h
  have h0 : (conjugateProduct i).val (trajectory i 0) = trajectory i 1 := trajectory_step i 0
  have h1 : (conjugateProduct i).val (trajectory i 1) = trajectory i 2 := trajectory_step i 1
  have h2 : (conjugateProduct i).val (trajectory i 2) = trajectory i 3 := trajectory_step i 2
  have he : (conjugateProduct i ^ 3).val (trajectory i 0) = trajectory i 3 := by
    change (conjugateProduct i).val ((conjugateProduct i).val ((conjugateProduct i).val (trajectory i 0))) = _
    rw [h0, h1, h2]
  rw [h] at he
  exact trajectory_end3 i (congrArg (fun v : Carrier K => v (cubeRow i)) he.symm)

private theorem conjugateProduct_fourth_ne_one (i : Fin 20) : conjugateProduct i ^ 4 ≠ 1 := by
  intro h
  have h0 : (conjugateProduct i).val (trajectory i 0) = trajectory i 1 := trajectory_step i 0
  have h1 : (conjugateProduct i).val (trajectory i 1) = trajectory i 2 := trajectory_step i 1
  have h2 : (conjugateProduct i).val (trajectory i 2) = trajectory i 3 := trajectory_step i 2
  have h3 : (conjugateProduct i).val (trajectory i 3) = trajectory i 4 := trajectory_step i 3
  have he : (conjugateProduct i ^ 4).val (trajectory i 0) = trajectory i 4 := by
    change (conjugateProduct i).val ((conjugateProduct i).val ((conjugateProduct i).val
      ((conjugateProduct i).val (trajectory i 0)))) = _
    rw [h0, h1, h2, h3]
  rw [h] at he
  exact trajectory_end4 i (congrArg (fun v : Carrier K => v (fourthRow i)) he.symm)

private theorem longRoot_conjugator_on_basis : ∀ (i : Fin 7) (j : Fin 8),
    (longRootConjugator i * rootA 1).val (basisVector j) =
    (unipotentProduct (longRootParameters i) * longRootConjugator i).val (basisVector j) := by
  intro i
  fin_cases i <;>
    simp only [longRootParameters, longRootConjugator, unipotentProduct, Fin.isValue] <;>
    decide +kernel

private theorem exists_conjugate_mem_unipotent (v : G) (hv : orderOf v = 2) :
    ∃ h : G, h * v * h⁻¹ ∈ unipotent := by
  have hp : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv]; rfl)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P (LieParabolicSetup.sylow (F := K))
  refine ⟨h, ?_⟩
  have hm : v ∈ P := hP (Subgroup.mem_zpowers v)
  have hn : MulAut.conj h v ∈ MulAut.conj h • (P : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul v (MulAut.conj h) (P : Subgroup G) hm
  change h * v * h⁻¹ ∈ (h • P : Sylow 2 G) at hn
  rwa [hh] at hn

private theorem pow_three_or_four_eq_one (x : G) (hx : orderOf x ≤ 4) : x ^ 3 = 1 ∨ x ^ 4 = 1 := by
  have hp := orderOf_pos x
  have he := pow_orderOf_eq_one x
  have ho : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by omega
  rcases ho with ho | ho | ho | ho
  · left
    have hx1 : x = 1 := orderOf_eq_one_iff.mp ho
    rw [hx1, one_pow]
  · right
    have hx2 : x ^ 2 = 1 :=
      (congrArg (fun n : ℕ => x ^ n) ho).symm.trans he
    calc
      x ^ 4 = (x ^ 2) ^ 2 := pow_mul x 2 2
      _ = 1 := (congrArg (fun g : G => g ^ (2 : ℕ)) hx2).trans (one_pow 2)
  · exact Or.inl ((congrArg (fun n : ℕ => x ^ n) ho).symm.trans he)
  · exact Or.inr ((congrArg (fun n : ℕ => x ^ n) ho).symm.trans he)

private theorem orderOf_conjugate (h v : G) :
    orderOf (h * v * h⁻¹) = orderOf v :=
  orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective v

private theorem product_bound_conjugate (h v : G) (hv : ∀ k, orderOf (v * (k⁻¹ * v * k)) ≤ 4) :
    ∀ k, orderOf ((h * v * h⁻¹) * (k⁻¹ * (h * v * h⁻¹) * k)) ≤ 4 := by
  intro k
  have he : (h * v * h⁻¹) * (k⁻¹ * (h * v * h⁻¹) * k) =
      (MulAut.conj h) (v * ((h⁻¹ * k * h)⁻¹ * v * (h⁻¹ * k * h))) := by
    simp only [MulAut.conj_apply]
    group
  rw [he, MulEquiv.orderOf_eq]
  exact hv _
private theorem parameter_exhaustion : ∀ t : Fin 6 → K, unipotentProductParameters t t = 0 →
    t = 0 ∨ (∃ i, t = longRootParameters i) ∨ ∃ i, t = otherParameters i := by
  decide +kernel

private theorem longRootParameters_isConj (i : Fin 7) : IsConj (unipotentProduct (longRootParameters i)) (rootA (1 : K)) := by
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨longRootConjugator i, ?_⟩
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext _ _ (longRoot_conjugator_on_basis i)


private theorem isConj_of_unipotent (t : Fin 6 → K)
    (hv : orderOf (unipotentProduct t) = 2)
    (hprod : ∀ h : G, orderOf (unipotentProduct t * (h⁻¹ * unipotentProduct t * h)) ≤ 4) :
    IsConj (unipotentProduct t) (rootA (1 : K)) := by
  have hs : unipotentProductParameters t t = 0 := by
    apply unipotentProduct_injective
    rw [← unipotentProduct_mul, unipotentProduct_zero, ← pow_two]
    exact (congrArg (fun n : ℕ => unipotentProduct t ^ n) hv).symm.trans
      (pow_orderOf_eq_one _)
  rcases parameter_exhaustion t hs with ht | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [ht] at hv
  · exact longRootParameters_isConj i
  · have hb := pow_three_or_four_eq_one _ (hprod (productConjugator i))
    change conjugateProduct i ^ 3 = 1 ∨ conjugateProduct i ^ 4 = 1 at hb
    rcases hb with hb | hb
    · exact False.elim (conjugateProduct_cube_ne_one i hb)
    · exact False.elim (conjugateProduct_fourth_ne_one i hb)

end InvolutionClasses

/-- The source product-order bound singles out the long-root class in the full
binary octonion group. No moved-rank hypothesis is needed for this step. -/
theorem isConj_rootA_of_product_order_bound (v : G) (hv : orderOf v = 2)
    (hprod : ∀ h : G, orderOf (v * (h⁻¹ * v * h)) ≤ 4) :
    IsConj v (rootA (1 : K)) := by
  obtain ⟨h, hh⟩ := InvolutionClasses.exists_conjugate_mem_unipotent v hv
  rw [unipotent_eq_range] at hh
  obtain ⟨t, ht⟩ := hh
  have ho : orderOf (unipotentProduct t) = 2 := by
    rw [ht, InvolutionClasses.orderOf_conjugate, hv]
  have hb : ∀ k : G,
      orderOf (unipotentProduct t * (k⁻¹ * unipotentProduct t * k)) ≤ 4 := by
    rw [ht]
    exact InvolutionClasses.product_bound_conjugate h v hprod
  exact (isConj_iff.mpr ⟨h, ht.symm⟩).trans
    (InvolutionClasses.isConj_of_unipotent t ho hb)

/-- The involution-class calculation required in the G₂(2) branch of 6.2.19,
for the actual trace-zero octonion quotient action. -/
theorem isConj_rootA_of_rank_two (v : G) (hv : orderOf v = 2)
    (_hrank : Module.finrank K (movedSpace (Atlas.G2.Natural.action K) v) = 2)
    (hprod : ∀ h : G, orderOf (v * (h⁻¹ * v * h)) ≤ 4) :
    IsConj v (rootA (1 : K)) :=
  isConj_rootA_of_product_order_bound v hv hprod

end Representation.RankTwo.GTwo
