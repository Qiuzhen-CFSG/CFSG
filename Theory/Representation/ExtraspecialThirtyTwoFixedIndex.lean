module

public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.GroupAction.CoprimeHall
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The center-fixed index for an extraspecial group of order 32

An extraspecial group of order 32 acting on an elementary abelian odd-prime
group has center-fixed index divisible by the fourth power of that prime,
provided its center acts nontrivially.

Coprime splitting identifies the index with the order of the moving subgroup
`[E, Z(K)]`. Its center-fixed subgroup is trivial, so the center still acts
nontrivially there. After extending scalars to an algebraic closure, choose a
simple constituent with nontrivial central action. Extraspeciality makes this
constituent faithful, and the extraspecial degree formula gives dimension four.
Scalar extension preserves the ambient dimension, proving the required bound
on the order of the moving subgroup.

Source: Lyons, *A Characterization of the Group U₃(4)*, p.386.
-/

open scoped IsMulCommutative TensorProduct

namespace Representation

/-- A nontrivial central action of an extraspecial group of order 32 has
center-fixed index divisible by `p ^ 4` on an elementary abelian `p`-group. -/
public theorem extraspecialThirtyTwo_fourth_pow_dvd_center_fixed_index
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K E : Type*} [Group K] [Finite K] [IsExtraspecial 2 K]
    [Group E] [Finite E] [IsElementaryAbelian p E]
    (hcardK : Nat.card K = 32)
    [MulDistribMulAction K E]
    (hnot : ¬ Subgroup.center K ≤ (MulDistribMulAction.toMulAut K E).ker) :
    p ^ 4 ∣ (FixedPoints.subgroup (Subgroup.center K) E).index := by
  let rho := MulDistribMulAction.toMulAut K E
  let Z : Subgroup K := Subgroup.center K
  let W : Subgroup E := commutatorAction Z E
  let : IsInvariant K E W := by
    exact ⟨fun k e =>
      (commutatorAction_isInvariant_of_normalizing_actor (⊤ : Subgroup K) Z
        (by rw [Subgroup.normalizer_eq_top])).invariant ⟨k, Subgroup.mem_top k⟩ e⟩
  let : IsElementaryAbelian p W := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      ((IsMulCommutative.is_comm (M := E)).comm (x : E) (y : E))⟩⟩
    exponent_dvd_p := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro w
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) (w : E)
  }
  let C : Subgroup E := FixedPoints.subgroup Z E
  have hcop : Nat.Coprime (Nat.card Z) (Nat.card E) := by
    rw [IsExtraspecial.center_order_p 2 K]
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
    rw [hn]
    have h2p : ¬ 2 ∣ p := by
      intro hd
      apply hp2
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : Nat.Prime p)).mp hd).symm
    exact Nat.Coprime.pow_right n (Nat.prime_two.coprime_iff_not_dvd.mpr h2p)
  have hcompl : IsCompl C W := by
    simpa [C, W] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := E) (A := Z) (Group.isSolvable_of_comm fun x y : E => mul_comm x y) hcop inferInstance)
  have hWne : W ≠ ⊥ := by
    intro hWbot
    have hCtop : C = ⊤ := by
      rw [← sup_bot_eq C, ← hWbot]
      exact hcompl.sup_eq_top
    apply hnot
    intro z hz
    rw [MonoidHom.mem_ker]
    ext e
    have he : e ∈ C := by rw [hCtop]; trivial
    have hf := (FixedPoints.mem_subgroup (M := Z) (a := e)).1 he ⟨z, hz⟩
    change (⟨z, hz⟩ : Z) • e = e at hf
    change rho z e = e
    exact hf
  have hfixedW : FixedPoints.subgroup Z W = ⊥ := by
    apply bot_unique
    intro w hw
    apply Subtype.ext
    have hwC : (w : E) ∈ C := by
      intro z
      exact congrArg Subtype.val (hw z)
    have hwbot : (w : E) ∈ C ⊓ W := ⟨hwC, w.property⟩
    simpa only [hcompl.inf_eq_bot, Subgroup.mem_bot, Subgroup.coe_one] using hwbot
  let rhoW : Representation (ZMod p) K (Additive W) :=
    Representation.ofElementaryAbelianAction
  have hnotW : ¬ Z ≤ rhoW.ker := by
    intro hle
    apply hWne
    apply bot_unique
    intro w hw
    let wW : W := ⟨w, hw⟩
    have hwfix : wW ∈ FixedPoints.subgroup Z W := by
      intro z
      have hz : rhoW z = 1 := MonoidHom.mem_ker.mp (hle z.property)
      have hz' := LinearMap.congr_fun hz (Additive.ofMul wW)
      exact (show (↑z : K) • wW = wW by
        exact Additive.ofMul.injective (by simpa [rhoW] using hz'))
    have : wW = 1 := by simpa [hfixedW] using hwfix
    exact congrArg Subtype.val this
  have hrhoWker : rhoW.ker = ⊥ :=
    ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 2) rhoW hnotW
  have hrhoWfaith : Function.Injective rhoW := (MonoidHom.ker_eq_bot_iff (f := rhoW)).1 hrhoWker
  let F' := AlgebraicClosure (ZMod p)
  let sigma := Representation.extendScalars F' rhoW
  have hcp : ringChar F' = p :=
    (Algebra.ringChar_eq (ZMod p) F').symm.trans (ZMod.ringChar_zmod_n p)
  have hc : ¬ ringChar F' ∣ Nat.card K := by
    rw [hcp, hcardK]
    intro hd
    apply hp2
    have hd' : p ∣ 2 := (Fact.out : Nat.Prime p).dvd_of_dvd_pow (n := 5) hd
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hd'
  have hchar : ringChar F' = 0 ∨ Nat.Prime (ringChar F') ∧
      Nat.Coprime (ringChar F') (Nat.card K) := by
    have hp : Nat.Prime (ringChar F') := hcp.symm ▸ (Fact.out : p.Prime)
    exact Or.inr ⟨hp, hp.coprime_iff_not_dvd.mpr hc⟩
  have hsemi := Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    sigma hchar
  have hsigfaith : Function.Injective sigma :=
    (Representation.extendScalars_faithful_iff F' rhoW).1 hrhoWfaith
  have hZne : Z ≠ ⊥ := by
    intro hz
    apply hnot
    change Z ≤ rho.ker
    rw [hz]
    exact bot_le
  have hnotSigma : ¬ Z ≤ sigma.ker := by
    intro hle
    apply hZne
    have hker : sigma.ker = ⊥ := (MonoidHom.ker_eq_bot_iff (f := sigma)).2 hsigfaith
    exact le_antisymm (by simpa [hker] using hle) bot_le
  let V' := TensorProduct (ZMod p) F' (Additive W)
  obtain ⟨m, hmSimple, hmKer⟩ :=
    @exists_simple_submodule_nontrivial_of_not_le_ker
      K inferInstance F' inferInstance V'
      inferInstance inferInstance sigma hsemi Z hnotSigma
  let tau := (Subrepresentation.ofSubmodule' m).toRepresentation
  have htauirr : IsIrreducible tau := irreducible_of_ofSubmodule'_simple sigma hmSimple
  let : IsIrreducible tau := htauirr
  let : FiniteDimensional F' ↥m := finiteDimensional_of_irreducible_finite_group tau htauirr
  have htaufait : Function.Injective tau := by
    apply (MonoidHom.ker_eq_bot_iff (f := tau)).1
    apply ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 2)
    exact hmKer
  have hdim : Module.finrank F' ↥m = 4 := by
    apply finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
      (q := 2) (n := 2) tau htaufait
    · simpa using hcardK
    · exact hc
  have hle : 4 ≤ Module.finrank (ZMod p) (Additive W) := by
    have hsub : Module.finrank F' ↥m ≤ Module.finrank F' (F' ⊗[ZMod p] Additive W) := by
      exact Submodule.finrank_le (Subrepresentation.ofSubmodule' m).toSubmodule
    rw [Module.finrank_baseChange (R := F') (S := ZMod p) (M' := Additive W)] at hsub
    rw [hdim] at hsub
    exact hsub
  have hWcard : Nat.card W = p ^ Module.finrank (ZMod p) (Additive W) := by
    calc
      Nat.card W = Nat.card (Additive W) := (Nat.card_congr Additive.toMul).symm
      _ = _ := by rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hindex : (FixedPoints.subgroup Z E).index = Nat.card W := by
    let : C.Normal := Subgroup.normal_of_isMulCommutative C
    have hprod := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint C W
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hcompl.disjoint
    rw [hcompl.sup_eq_top, Subgroup.card_top] at hprod
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C)) (C.card_mul_index.trans hprod)
  rw [hindex, hWcard]
  exact Nat.pow_dvd_pow p hle

/-- Homomorphism form, with the center-fixed subgroup taken for the action
installed by `MulDistribMulAction.compHom E rho`. -/
public theorem extraspecialThirtyTwo_fourth_pow_dvd_center_fixed_index_of_hom
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K E : Type*} [Group K] [Finite K] [IsExtraspecial 2 K]
    [Group E] [Finite E] [IsElementaryAbelian p E]
    (hcardK : Nat.card K = 32) (rho : K →* MulAut E)
    (hnot : ¬ Subgroup.center K ≤ rho.ker) :
    letI : MulDistribMulAction K E := MulDistribMulAction.compHom E rho
    p ^ 4 ∣ (FixedPoints.subgroup (Subgroup.center K) E).index := by
  let : MulDistribMulAction K E := MulDistribMulAction.compHom E rho
  apply extraspecialThirtyTwo_fourth_pow_dvd_center_fixed_index hp2 hcardK
  have hhom : MulDistribMulAction.toMulAut K E = rho := by
    ext k e
    rfl
  rwa [hhom]

end Representation
