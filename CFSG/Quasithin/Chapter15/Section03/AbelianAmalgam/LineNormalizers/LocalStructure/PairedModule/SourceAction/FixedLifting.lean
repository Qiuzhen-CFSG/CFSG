module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.Section
public import Theory.GroupTheory.KleinFourKernelInvolutionFusion

/-!
# Fixed lifts in the original binary line section

If `τ²` centralizes `U` and `τ` acts nontrivially on the four-group `E`,
a quotient-fixed vector has a displacement in `C_E(τ)`. Every such element
is a difference for the involution on `E`. Correcting the original lift
by this element of `E` yields a lift in the actual `C_U(τ)`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170, before the temporary replacement.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
variable {G : Type*} [Group G] (V E : Subgroup G)
variable [IsElementaryAbelian 2 (lineV V E)] [IsKleinFour E]

/-- Quotient-fixed vectors have actual fixed lifts, corrected inside the line. -/
theorem fixedImage_eq_of_square_centralizes (hEU : E ≤ lineV V E)
    (t : lineNormalizer E)
    (hsq : (t : G) ^ 2 ∈ centralizer (lineV V E : Set G))
    (hne : (t : G) ∉ centralizer (E : Set G)) :
    fixedImage V E (t : G) = LinearMap.ker (sectionRepresentation V E t - 1) := by
  let A := spanRepresentation V E t
  have hAA (v : Additive (lineV V E)) : A (A v) = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (t : G) * ((t : G) * (v.toMul : G) * (t : G)⁻¹) * (t : G)⁻¹ = v.toMul
    have hh := mem_centralizer_iff.mp hsq (v.toMul : G) v.toMul.property
    calc
      _ = (t : G) ^ 2 * (v.toMul : G) * ((t : G) ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = v.toMul := by rw [← hh, mul_inv_cancel_right]
  let a := E.normalizerMonoidHom t
  have haa : Function.Involutive a := by
    intro e
    apply Subtype.ext
    exact congrArg (fun v : Additive (lineV V E) => (v.toMul : G))
      (hAA (Additive.ofMul ⟨e, hEU e.property⟩))
  have han : a ≠ 1 := by
    intro he
    apply hne
    have hk : t ∈ E.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker] at hk
    exact hk
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_fixedImage V E (t : G) x).mp hx
    have hfix : A (Additive.ofMul u) = Additive.ofMul u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (t : G) * (u : G) * (t : G)⁻¹ = u
      rw [← hu, mul_inv_cancel_right]
    change sectionRepresentation V E t (sectionProjection V E (Additive.ofMul u)) -
      sectionProjection V E (Additive.ofMul u) = 0
    rw [sectionRepresentation_projection, hfix, sub_self]
  · intro x hx
    obtain ⟨v, rfl⟩ := sectionProjection_surjective V E x
    have hz : A v - v ∈ lineSubspace V E := by
      rw [← sectionProjection_ker, LinearMap.mem_ker, map_sub]
      exact hx
    let z := A v - v
    let c : E := ⟨z.toMul, hz⟩
    have hnz : -z = z := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun e : E => (e : G)) (IsKleinFour.inv_eq_self c)
    have haz : A z = z := by
      change A (A v - v) = z
      rw [map_sub, hAA]
      exact (neg_sub (A v) v).symm.trans hnz
    have hac : a c = c := by
      apply Subtype.ext
      exact congrArg (fun w : Additive (lineV V E) => (w.toMul : G)) haz
    obtain ⟨b, hb⟩ := IsKleinFour.exists_difference_of_involutive_ne_one a haa han c hac
    let w : Additive (lineV V E) := Additive.ofMul ⟨b, hEU b.property⟩
    have hw : w - A w = z := by
      apply Additive.toMul.injective
      apply Subtype.ext
      have hbG := congrArg (fun e : E => (e : G)) hb
      change (b : G) * ((t : G) * (b : G) * (t : G)⁻¹)⁻¹ = (z.toMul : G) at hbG
      change (b : G) / ((t : G) * (b : G) * (t : G)⁻¹) = (z.toMul : G)
      simpa only [div_eq_mul_inv] using hbG
    have hfixed : A (v + w) = v + w := by
      calc
        A (v + w) = (A v - v) - (w - A w) + (v + w) := by rw [map_add]; abel
        _ = v + w := by rw [hw]; dsimp [z]; abel
    apply (mem_fixedImage V E (t : G) _).mpr
    refine ⟨(v + w).toMul, ?_, ?_⟩
    · have hh := congrArg (fun b : Additive (lineV V E) => (b.toMul : G)) hfixed
      change (t : G) * ((v + w).toMul : G) * (t : G)⁻¹ = (v + w).toMul at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · have hw0 : sectionProjection V E w = 0 := by
        rw [← LinearMap.mem_ker, sectionProjection_ker]
        exact b.property
      change sectionProjection V E (v + w) = sectionProjection V E v
      rw [map_add, hw0, add_zero]
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
