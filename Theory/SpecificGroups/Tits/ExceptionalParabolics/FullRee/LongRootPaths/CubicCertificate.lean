module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.WordCertificate

/-!
# A cubic carrying the two marked long-root endpoints

The literal Parrott word s5 r8 s8 has cube one, carries the left endpoint
to the right endpoint, and centralizes their short-root commutator. These
three small faithful-permutation certificates replace any unmarked orbit
assumption in the final J.4.7 quotient separation. Source: the marked local
calculation used in Aschbacher--Smith J.4.7, printed p.444.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
open Tits
abbrev cubicWord : Atlas1600Group := a .s5 * a .r8 * a .s8
private theorem val_mul (x y:Atlas1600Group) : (x*y).val=x.val*y.val := rfl
private theorem val_inv (x:Atlas1600Group) : x⁻¹.val=x.val⁻¹ := rfl
private theorem val_pow (x:Atlas1600Group) (n:ℕ) : (x^n).val=x.val^n := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem cubic_word_cube : cubicWord^3=1 := by
  apply Subtype.ext
  change cubicWord.val^3=1
  simp only [cubicWord,a,val_mul,atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem cubic_word_left : cubicWord*leftWord= a .s1*cubicWord := by
  apply Subtype.ext
  simp only [cubicWord,leftWord,a,atlas1600R5_eq,val_mul,val_inv,val_pow,atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem cubic_word_short : cubicWord*(a .s7*a .s4*(a .s7)⁻¹)=
    (a .s7*a .s4*(a .s7)⁻¹)*cubicWord := by
  apply Subtype.ext
  simp only [cubicWord,a,val_mul,val_inv,atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel
end Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
