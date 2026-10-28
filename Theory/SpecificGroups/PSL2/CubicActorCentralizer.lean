module
public import Theory.SpecificGroups.PSL2.CubicActorParameter
public import Theory.SpecificGroups.PSL2.PrimeFourFixers
/-!
# The centralizer of a prime-field cubic actor

An automorphism centralizing an inner, centerless cubic actor fixes its
normal four pointwise. The prime-field four-fixer theorem makes it inner
by an element of that four, and centerlessness then makes it trivial.
This is used for the second module in the paired-cubic source2.4.32.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

theorem prime_cubic_actor_centralizer_eq_bot {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (B : Subgroup (MulAut PSL(2,ZMod p)))
    (hB : B ≤ (MulAut.conj : PSL(2,ZMod p) →* MulAut PSL(2,ZMod p)).range)
    [IsKleinFour (B.pCoreIn 2)] (hz : center B = ⊥) :
    centralizer (B : Set (MulAut PSL(2,ZMod p))) = ⊥ := by
  let X := PSL(2,ZMod p)
  let f : X →* MulAut X := MulAut.conj
  have hf : Function.Injective f :=
    conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot (ZMod p))
  let U := B.pCoreIn 2
  let V := U.comap f
  have hU : U ≤ f.range := (pCoreIn_le 2 B).trans hB
  have hmap : V.map f = U := map_comap_eq_self hU
  let e : V ≃* U := (V.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hmap)
  let : IsKleinFour V := {
    card_four := (Nat.card_congr e.toEquiv).trans (IsKleinFour.card_four (G := U))
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans (IsKleinFour.exponent_two (G := U)) }
  apply eq_bot_iff.mpr
  intro a ha
  have hfix : ∀ x ∈ V, a x = x := by
    intro x hx
    apply hf
    have hc : f x * a = a * f x := ha (f x) ((pCoreIn_le 2 B) hx)
    have he : f (a x) = a * f x * a⁻¹ := by
      ext y
      change a x * y * (a x)⁻¹ = a (x * a.symm y * x⁻¹)
      simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
    rw [he,←hc,mul_inv_cancel_right]
  obtain ⟨u,hu,huA⟩ := primeField_four_fixed_inner
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by omega) V a hfix
  have haB : a ∈ B := huA ▸ (pCoreIn_le 2 B) hu
  have haZ : (⟨a,haB⟩ : B) ∈ center B := by
    rw [mem_center_iff]
    intro b
    apply Subtype.ext
    exact ha b b.property
  have haone : (⟨a,haB⟩ : B) = 1 := by simpa only [hz,mem_bot] using haZ
  exact congrArg Subtype.val haone
end Theory.PSL2
