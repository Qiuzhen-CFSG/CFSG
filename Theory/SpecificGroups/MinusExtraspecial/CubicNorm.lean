module
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.SpecificGroups.MinusExtraspecial.CubicNorm.Calculation
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour

/-!
# Norms of cubic-inverting involutions on the minus extraspecial core

In a faithful A₅ action on Q₈ ∘ D₈, the action on the five singular
central cosets is faithful: its kernel is normal in A₅ and the group of
inner automorphisms is too small to contain A₅. Perfectness makes the
permutation action even. Thus an inverting involution moves four points.

Cubic normal form puts the order-three actor in the standard quaternion
coordinates. The finite certificate then supplies a fixed reflection whose
norm under the involution has order four. Transporting this norm back is
exactly the calculation needed to construct an order-eight element in the
source normalizer.

`norm_four_of_cubicNormalForm` retains the independent cubic-normal-form
premise. Its existing producer is `qt-i47-j2-core-cubic-normal-form`.
The deliberate `import all` dependencies reuse the existing internal bit
coordinates and five-point action comparison; those implementation details
do not occur in the public theorem's statement.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, p.262, and the
quaternion–dihedral coordinates on p.265.
-/

open Subgroup
namespace MinusExtraspecial.FixedFourCalculation.CubicNorm
open Outside
private theorem decode_cycleBits (x : B) : decode (cycleBits x) = CubicAction.cycle (decode x) := by
  revert x
  decide +kernel

private theorem cycle_fixed : CubicAction.cycle (decode 8) = decode 8 := by decide +kernel
private theorem fourth_power : ∀ q : Model, q ^ 4 = 1 := by decide +kernel

private theorem normalized (b : MulAut Model) (hb : b ^ 2 = 1)
    (hm : (fivePointAction b).support.card = 4)
    (hc : b * CubicAction.cycle = CubicAction.cycle ^ 2 * b) :
    ∃ q : Model, CubicAction.cycle q = q ∧ orderOf (q * b q) = 4 := by
  have hv : encode (b (generators 1)) = second (encode (b (generators 0))) := by
    apply equiv.injective
    change decode (encode (b (generators 1))) = decode (second (encode (b (generators 0))))
    rw [decode_encode, second, decode_mul, decode_cycleBits, decode_cycleBits,
      decode_inv, decode_encode]
    have h := DFunLike.congr_fun hc (generators 0)
    change b (CubicAction.cycle (generators 0)) =
      CubicAction.cycle (CubicAction.cycle (b (generators 0))) at h
    rw [show CubicAction.cycle (generators 0) = generators 1 * generators 0 by
      decide +kernel, map_mul] at h
    exact eq_mul_inv_iff_mul_eq.mpr h
  have hrel := relations_aut b
  rw [hv] at hrel
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hrel
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
  have hi : Outside.invol (encode (b (generators 0))) (encode (b (generators 1)))
      (encode (b (generators 2))) (encode (b (generators 3))) := by
    apply List.all_eq_true.mpr
    intro g _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ g)) = decode g
    rw [decode_word, decode_word]
    have h := DFunLike.congr_fun hb (decode g)
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hc' : reverses (encode (b (generators 0))) (encode (b (generators 1)))
      (encode (b (generators 2))) (encode (b (generators 3))) := by
    apply List.all_eq_true.mpr
    intro g _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (cycleBits g)) = decode (cycleBits (cycleBits (word _ _ _ _ g)))
    rw [decode_word, decode_cycleBits, decode_cycleBits, decode_cycleBits, decode_word]
    have h := DFunLike.congr_fun hc (decode g)
    simpa only [pow_two, MulAut.mul_apply] using h
  have hm' := (moved_eq b).trans hm
  rw [hv] at hi hm' hc'
  have hn := calculation_all (encode (b (generators 0))) h1 h2 h3 _ h4 h5 h6
    _ h7 h8 h9 h10 hi hm' hc'
  have hn' : (decode 8 * b (decode 8)) ^ 2 ≠ 1 := by
    intro h
    apply hn
    apply equiv.injective
    change decode (mul (mul 8 (encode (b (generators 2))))
      (mul 8 (encode (b (generators 2))))) = decode 0
    rw [decode_mul, decode_mul, decode_encode, decode_zero]
    rw [← show decode 8 = generators 2 by decide +kernel]
    simpa only [pow_two] using h
  refine ⟨decode 8, cycle_fixed, ?_⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hn' (fourth_power _)

private theorem faithful_points
    (φ : alternatingGroup (Fin 5) →* MulAut Model) (hφ : Function.Injective φ) :
    Function.Injective (fivePointAction.comp φ) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (fivePointAction.comp φ).ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hle : φ.range ≤ (MulAut.conj : Model →* MulAut Model).range := by
      rintro _ ⟨a, rfl⟩
      rw [← action_kernel]
      exact show a ∈ (fivePointAction.comp φ).ker from h ▸ mem_top a
    have hc := Nat.card_le_card_of_injective _ (inclusion_injective hle)
    have hb := Nat.card_le_card_of_surjective _
      (MonoidHom.rangeRestrict_surjective (MulAut.conj : Model →* MulAut Model))
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv,
      nat_card_alternatingGroup] at hc
    rw [card_model] at hb
    norm_num [Nat.factorial] at hc
    change 60 ≤ Nat.card (MulAut.conj : Model →* MulAut Model).range at hc
    omega

/-- A faithful A₅ action has a norm of order four in the fixed group of any
cubic element, for every involution inverting that element. The only remaining
input is conjugacy of cubic automorphisms to the standard quaternion cycle. -/
public theorem norm_four_of_cubicNormalForm (hNF : CubicAction.HasCubicNormalForm)
    (φ : alternatingGroup (Fin 5) →* MulAut Model) (hφ : Function.Injective φ)
    (x r : alternatingGroup (Fin 5)) (hx : orderOf x = 3) (hr : orderOf r = 2)
    (hrx : r * x * r⁻¹ = x⁻¹) :
    ∃ q : Model, φ x q = q ∧ orderOf (q * φ r q) = 4 := by
  have hxpow : (φ x) ^ 3 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hxne : φ x ≠ 1 := by
    intro he
    have hx1 := hφ (he.trans φ.map_one.symm)
    rw [hx1, orderOf_one] at hx
    contradiction
  obtain ⟨e, he⟩ := hNF (φ x) hxpow hxne
  let θ : alternatingGroup (Fin 5) →* MulAut Model := (MulAut.congr e).toMonoidHom.comp φ
  have hθ : Function.Injective θ := (MulAut.congr e).injective.comp hφ
  have hxθ : θ x = CubicAction.cycle := by
    apply DFunLike.ext
    intro q
    change e (φ x (e.symm q)) = CubicAction.cycle q
    rw [he, e.apply_symm_apply]
  have hb : (θ r) ^ 2 = 1 := by
    rw [← map_pow, ← hr, pow_orderOf_eq_one, map_one]
  have hi := congrArg θ hrx
  simp only [map_mul, map_inv, hxθ] at hi
  have hcycleinv : CubicAction.cycle⁻¹ = CubicAction.cycle ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using CubicAction.cycle_cube
  have hc : θ r * CubicAction.cycle = CubicAction.cycle ^ 2 * θ r := by
    rw [hcycleinv] at hi
    exact mul_inv_eq_iff_eq_mul.mp hi
  let f := fivePointAction.comp θ
  have hsign : Equiv.Perm.sign (f r) = 1 := by
    have hk : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ (Equiv.Perm.sign.comp f).ker := by
      rw [← commutator_alternatingGroup_eq_top (by simp)]
      exact Abelianization.commutator_subset_ker _
    exact hk (mem_top r)
  let ap : alternatingGroup (Fin 5) := ⟨f r, hsign⟩
  have hap : orderOf ap = 2 := by
    rw [← orderOf_coe, orderOf_injective f (faithful_points θ hθ), hr]
  have hm : (fivePointAction (θ r)).support.card = 4 := by
    change (ap : Equiv.Perm (Fin 5)).support.card = 4
    rw [← Equiv.Perm.sum_cycleType,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) ap hap]
    rfl
  obtain ⟨q, hq, hn⟩ := normalized (θ r) hb hm hc
  refine ⟨e.symm q, ?_, ?_⟩
  · apply e.injective
    rw [he, e.apply_symm_apply, hq]
  · rw [← e.orderOf_eq, map_mul, e.apply_symm_apply]
    exact hn

end MinusExtraspecial.FixedFourCalculation.CubicNorm
