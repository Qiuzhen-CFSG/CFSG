module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23.TwoRankLower.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.Candidate
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.Group

/-!
# An elementary eight in the actual Fischer Fi₂₃ carrier

The certified centralizer involution and its two conjugates under the
second ATLAS generator commute. One checked commutation relation suffices,
as that generator has order three. Their eight products move point zero
to eight distinct letters in the literal 31671-point action.
Source: ATLAS F23G1-p31671B0; Aschbacher–Smith A.2.12, printed p.36.
-/
namespace Sporadic.Fischer.Fi23.TwoRank
open CentralizerSection CentralizerSection.CandidateCertificate
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := (C2 × C2) × C2

private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]

private theorem binary_commute {H : Type*} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) (x y : C2) :
    Commute (binaryHom a ha x) (binaryHom b hb y) := by
  change Commute (if x = 1 then 1 else a) (if y = 1 then 1 else b)
  split_ifs <;> simp [hab]

private def tripleHom {H : Type*} [Group H] (a b c : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))

private theorem b_cube : b ^ 3 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one]
  apply Equiv.ext
  intro i
  simpa only [pow_succ, pow_zero, mul_one, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    show inclusion b = generatorB from rfl, generatorB_apply] using Checks.b_cube i
private theorem b_inv : b⁻¹ = b ^ 2 := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [pow_succ] using b_cube
private def phi : MulAut Carrier := MulAut.conj (b⁻¹)
private def x : Carrier := candidate
private def y : Carrier := phi x
private def z : Carrier := phi y
private theorem phi_z : phi z = x := by
  change b⁻¹ * (b⁻¹ * (b⁻¹ * x * b) * b) * b = x
  calc
    _ = (b ^ 3)⁻¹ * x * b ^ 3 := by
      simp only [pow_succ, pow_zero]
      group
    _ = x := by rw [b_cube]; simp
private theorem x_sq : x ^ 2 = 1 := by
  rw [x, ← candidate_order]
  exact pow_orderOf_eq_one _
private theorem y_sq : y ^ 2 = 1 := by
  change phi x ^ 2 = 1
  rw [← map_pow, x_sq, map_one]
private theorem z_sq : z ^ 2 = 1 := by
  change phi y ^ 2 = 1
  rw [← map_pow, y_sq, map_one]
private def fastY (i : Fin 31671) := bMap (bMap (cMap (bMap i)))
private def fastZ (i : Fin 31671) := bMap (bMap (fastY (bMap i)))
private theorem x_apply (i : Fin 31671) : inclusion x i = cMap i := candidate_apply i
private theorem conjugate_action {H X : Type*} [Group H]
    (f : H →* Equiv.Perm X) (b g : H) (hb : b⁻¹ = b ^ 2) (i : X) :
    f (b⁻¹ * g * b) i = f b (f b (f g (f b i))) := by
  rw [hb, pow_two, map_mul, map_mul, map_mul]
  rfl
private theorem phi_apply (g : Carrier) (i : Fin 31671) :
    inclusion (phi g) i = bMap (bMap (inclusion g (bMap i))) := by
  have hh := conjugate_action inclusion b g b_inv i
  change inclusion (b⁻¹ * g * b) i = _
  change inclusion (b⁻¹ * g * b) i = generatorB (generatorB (inclusion g (generatorB i))) at hh
  simpa only [generatorB_apply] using hh
private theorem y_apply (i : Fin 31671) : inclusion y i = fastY i := by
  change inclusion (phi x) i = _
  rw [phi_apply, x_apply]
  rfl
private theorem z_apply (i : Fin 31671) : inclusion z i = fastZ i := by
  change inclusion (phi y) i = _
  rw [phi_apply, y_apply]
  rfl
private theorem commute_of_actions {H X : Type*} [Group H]
    (f : H →* Equiv.Perm X) (hf : Function.Injective f) (g h : H)
    (ha : ∀ i, f g (f h i) = f h (f g i)) : Commute g h := by
  apply hf
  rw [map_mul, map_mul]
  exact Equiv.ext ha
private theorem xy : Commute x y := by
  apply commute_of_actions inclusion inclusion_injective
  intro i
  simpa only [x_apply, y_apply, fastY] using Checks.commute i
private theorem yz : Commute y z := xy.map phi.toMonoidHom
private theorem xz : Commute x z := by
  have hh := yz.map phi.toMonoidHom
  change Commute z (phi z) at hh
  rw [phi_z] at hh
  exact hh.symm
private def embedding : E →* Carrier := tripleHom x y z x_sq y_sq z_sq xy xz yz
private theorem image (e : E) (i : Fin 31671) :
    inclusion (embedding e) i =
      (if e.1.1 = 1 then id else cMap)
        ((if e.1.2 = 1 then id else fastY) ((if e.2 = 1 then id else fastZ) i)) := by
  simp only [embedding, tripleHom, MonoidHom.noncommCoprod_apply, binaryHom,
    MonoidHom.coe_mk, OneHom.coe_mk, map_mul, Equiv.Perm.mul_apply]
  split_ifs <;> simp [x_apply, y_apply, z_apply]
private theorem detected : ∀ e : E,
    (if e.1.1 = 1 then id else cMap)
      ((if e.1.2 = 1 then id else fastY) ((if e.2 = 1 then id else fastZ) 0)) = 0 → e = 1 := by
  decide +kernel
private theorem embedding_injective : Function.Injective embedding := by
  rw [injective_iff_map_eq_one]
  intro e he
  apply detected
  have h := congrArg (fun g => inclusion g (0 : Fin 31671)) he
  simpa only [image, map_one, Equiv.Perm.one_apply] using h
/-- The literal Fischer Fi₂₃ permutation group contains an elementary eight. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 Carrier := by
  apply primeRank_ge_of_elementary_embedding (f := embedding)
  · exact (by decide +kernel : ∀ e : E, e ^ 2 = 1)
  · simp [E,C2,Nat.card_eq_fintype_card]
  · exact embedding_injective
end Sporadic.Fischer.Fi23.TwoRank
