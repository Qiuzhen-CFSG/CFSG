module

public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.GroupAction.SimpleCosets
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Hyperplane stabilizers in the binary four-dimensional SL₃ extension

A functional nonzero on a fixed vector cannot be fixed by an involution:
that vector lies in the involution displacement plane, on which an invariant
functional vanishes. The stabilizer therefore has odd order. Its index divides
168 and is at most the dual-space order 16, forcing index eight and order 21.
Simplicity excludes a proper overgroup of index two or four, proving maximality.

The functional and action are retained literally, for transport to the original
hyperplane normalizer in Aschbacher--Smith, 12.4.8, printed p.815.
-/

public section
open Subgroup Representation Representation.OneCohomology
namespace Representation.OneCohomology.SLThreeCentralExtension

/-- The exact functional stabilizer has order 21 and is maximal of index eight. -/
theorem dual_hyperplane_stabilizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group W)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (z : W) (hz : ∀ b, ρ b z = z)
    (hi : ∀ b, orderOf b = 2 →
      LinearMap.range (ρ b - LinearMap.id) = BinaryOffender.fixedSpace ρ (zpowers b))
    (f : Module.Dual (ZMod 2) W) (hf : f z ≠ 0) :
    ∃ S : Subgroup BinaryLinearThree.Group, S.index = 8 ∧ Nat.card S = 21 ∧ IsCoatom S ∧
      ∀ b, b ∈ S ↔ f.comp (ρ b) = f := by
  classical
  let : MulAction BinaryLinearThree.Group (Module.Dual (ZMod 2) W) := {
    smul b φ := ρ.dual b φ
    one_smul φ := by
      change ρ.dual 1 φ = φ
      rw [map_one]; rfl
    mul_smul b c φ := by
      change ρ.dual (b*c) φ = ρ.dual b (ρ.dual c φ)
      rw [map_mul]; rfl }
  let S := MulAction.stabilizer BinaryLinearThree.Group f
  have hodd : ¬ 2 ∣ Nat.card S := by
    intro hdiv
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
    have hb' : orderOf (b : BinaryLinearThree.Group) = 2 := (orderOf_coe b).trans hb
    have hfix : f.comp (ρ (b : BinaryLinearThree.Group)⁻¹) = f := b.property
    have hinv : (b : BinaryLinearThree.Group)⁻¹ = b := by
      have hpow : (b : BinaryLinearThree.Group) ^ 2 = 1 := by
        simpa only [hb'] using pow_orderOf_eq_one (b : BinaryLinearThree.Group)
      exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpow)
    rw [hinv] at hfix
    have hzfix : z ∈ BinaryOffender.fixedSpace ρ (zpowers (b : BinaryLinearThree.Group)) :=
      fun a => hz a
    rw [← hi _ hb'] at hzfix
    obtain ⟨w, hw⟩ := hzfix
    apply hf
    rw [← hw]
    change f (ρ (b : BinaryLinearThree.Group) w - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun hfix w)
  let : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) W => (f : W → ZMod 2)) DFunLike.coe_injective
  have hbound : S.index ≤ 16 := by
    rw [MulAction.index_stabilizer]
    have hc : Nat.card (Module.Dual (ZMod 2) W) = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Subspace.dual_finrank_eq, hdim]
      decide
    exact hc ▸ Set.ncard_le_card _
  have hcard := S.card_mul_index
  rw [Matrix.PSL3Two.card_SL] at hcard
  have hdiv : S.index ∈ Nat.divisors 168 :=
    Nat.mem_divisors.mpr ⟨hcard ▸ dvd_mul_left _ _, by decide⟩
  have hd : Nat.divisors 168 = {1,2,3,4,6,7,8,12,14,21,24,28,42,56,84,168} := by decide
  rw [hd] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hindex : S.index = 8 := by
    rcases hdiv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals rw [h] at hcard
    all_goals omega
  have hmax : IsCoatom S := by
    let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
    refine ⟨fun he => by simp [he] at hindex, ?_⟩
    intro B hSB
    by_contra hB
    have hsmall : B.index < 8 := hindex ▸ index_strictAnti hSB
    have hdiv8 : B.index ∣ 8 := hindex ▸ index_dvd_of_le hSB.le
    have hfact := B.card_dvd_factorial_index_of_simple hB
    rw [Matrix.PSL3Two.card_SL] at hfact
    interval_cases hiB : B.index <;> (first | omega | norm_num [Nat.factorial] at hfact)
  refine ⟨S,hindex,by rw [hindex] at hcard; omega,hmax,?_⟩
  intro b
  change f.comp (ρ b⁻¹) = f ↔ f.comp (ρ b) = f
  constructor
  · intro h
    ext w
    have hh := LinearMap.congr_fun h (ρ b w)
    simpa only [LinearMap.comp_apply,ρ.inv_self_apply] using hh.symm
  · intro h
    ext w
    have hh := LinearMap.congr_fun h (ρ b⁻¹ w)
    simpa only [LinearMap.comp_apply,ρ.self_inv_apply] using hh.symm

end Representation.OneCohomology.SLThreeCentralExtension
