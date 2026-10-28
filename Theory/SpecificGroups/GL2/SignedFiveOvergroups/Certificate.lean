module
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# A checked word certificate in the five-element matrix algebra

Every invertible two-by-two matrix outside the eight signed permutation
matrices generates the scalar 2I together with diag(-1,1) and the swap.
The table stores positive words in these three matrices, in base four.
Four-entry tuples keep the kernel check small; SignedFiveOvergroups transports
the certificate to actual matrices and proves its Sylow consequence.

The certificate is checked in five sequential blocks to bound peak memory.
This is a local matrix calculation for Aschbacher--Smith 14.6.15, p.1034.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup.SignedFiveCertificate
abbrev Mat := ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5
def identity : Mat := (1,0,0,1)
def mul (a b : Mat) : Mat :=
  (a.1*b.1+a.2.1*b.2.2.1, a.1*b.2.1+a.2.1*b.2.2.2,
   a.2.2.1*b.1+a.2.2.2*b.2.2.1, a.2.2.1*b.2.1+a.2.2.2*b.2.2.2)
def neg (a : Mat) : Mat := (-a.1,-a.2.1,-a.2.2.1,-a.2.2.2)
def reflection : Mat := (-1,0,0,1)
def swap : Mat := (0,1,1,0)
def scalarTwo : Mat := (2,0,0,2)
def signed (a : Mat) : Prop :=
  a = identity ∨ a = reflection ∨ a = neg identity ∨ a = neg reflection ∨
  a = swap ∨ a = mul reflection swap ∨ a = neg swap ∨ a = neg (mul reflection swap)
private instance (a : Mat) : Decidable (signed a) := by unfold signed; infer_instance
def eval (a : Mat) (fuel n : ℕ) : Mat :=
  match fuel with
  | 0 => identity
  | k+1 => if n=0 then identity else
      mul (if n%4=1 then reflection else if n%4=2 then swap else a) (eval a k (n/4))
private def certificate : Array ℕ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 262041, 63, 16281, 1023, 15, 14661593, 65469, 1048473, 14661593,
  221, 4095, 980925, 980925, 4095, 0, 12023673, 3549, 46969, 908765,
  0, 0, 0, 0, 0, 15, 16235993, 64509, 1048473, 16235993,
  14, 978670, 3549, 46969, 908765, 57, 262041, 63, 16281, 1023,
  221, 4095, 1030125, 1030125, 4095, 0, 0, 0, 0, 0,
  221, 4095, 1030125, 1030125, 4095, 45, 262041, 63, 16281, 1023,
  217, 3927517, 3549, 46969, 908765, 15, 16235993, 1048473, 64509, 16235993,
  0, 0, 0, 0, 0, 0, 12023673, 3549, 46969, 908765,
  221, 4095, 980925, 980925, 4095, 15, 14661593, 1048473, 65469, 14661593,
  0, 262041, 63, 16281, 1023, 0, 0, 238, 3801, 0,
  0, 257982, 980925, 14661593, 971480697, 0, 3822, 980925, 14661593, 224889,
  0, 61145, 980925, 14661593, 237177, 0, 978670, 980925, 14661593, 921149049,
  0, 257982, 1030125, 16235993, 921149049, 262041, 0, 3822, 3513, 15,
  16235993, 63, 0, 3961, 3993, 4095, 2937, 1005, 0, 46969,
  908765, 249, 3801, 1023, 0, 0, 3822, 1030125, 16235993, 237177,
  14661593, 63, 0, 4025, 3993, 908765, 221, 3705, 1023, 0,
  262041, 0, 4054521, 238, 15, 4095, 2937, 16281, 0, 46969,
  0, 61145, 1030125, 16235993, 224889, 4095, 2937, 957, 0, 46969,
  262041, 0, 3112441, 238, 15, 908765, 221, 3705, 1023, 0,
  14661593, 63, 0, 4025, 3993, 0, 978670, 1030125, 16235993, 971480697,
  908765, 221, 3801, 1023, 0, 4095, 2937, 16281, 0, 46969,
  16235993, 63, 0, 3549, 3993, 262041, 0, 61145, 3513, 15,
  0, 238, 3, 185, 3801, 0, 1030125, 1023, 15658713, 16235993,
  0, 1030125, 1023, 3822, 16235993, 0, 1030125, 1023, 61145, 16235993,
  0, 1030125, 1023, 978670, 16235993, 0, 980925, 1023, 15658713, 14661593,
  63, 3822, 3705, 0, 3513, 1048473, 0, 221, 971480697, 4025,
  1030125, 16281, 978670, 15, 0, 46969, 3801, 0, 238, 262041,
  0, 980925, 1023, 3822, 14661593, 1048473, 0, 221, 921149049, 3961,
  46969, 3705, 0, 237, 262041, 63, 253821, 189, 0, 238,
  980925, 1005, 15658713, 15, 0, 0, 980925, 1023, 61145, 14661593,
  980925, 16281, 978670, 15, 0, 63, 253821, 249, 0, 238,
  46969, 3705, 0, 3993, 262041, 65469, 0, 221, 971480697, 3549,
  0, 980925, 1023, 978670, 14661593, 46969, 3801, 0, 238, 262041,
  1030125, 957, 15658713, 15, 0, 64509, 0, 221, 921149049, 4025,
  63, 61145, 3705, 0, 3513, 0, 3801, 13, 63, 238,
  0, 16235993, 908765, 262041, 1030125, 0, 16235993, 3822, 262041, 1030125,
  0, 16235993, 61145, 262041, 1030125, 0, 16235993, 908765, 262041, 1030125,
  0, 14661593, 908765, 262041, 980925, 16281, 3513, 0, 3705, 3822,
  64509, 3949, 971480697, 221, 0, 1030125, 0, 15, 978670, 63,
  3549, 1023, 238, 0, 3801, 0, 14661593, 3822, 262041, 980925,
  65469, 3961, 921149049, 221, 0, 3549, 1023, 3993, 0, 3705,
  16281, 238, 0, 249, 253821, 980925, 0, 15, 15658713, 63,
  0, 14661593, 61145, 262041, 980925, 980925, 0, 15, 978670, 63,
  16281, 238, 0, 189, 253821, 3549, 1023, 237, 0, 3705,
  1048473, 3833, 971480697, 221, 0, 0, 14661593, 908765, 262041, 980925,
  3549, 1023, 238, 0, 3801, 1030125, 0, 15, 15658713, 63,
  1048473, 3577, 921149049, 221, 0, 16281, 3513, 0, 3705, 61145,
  0, 0, 3801, 238, 0, 0, 971480697, 14661593, 980925, 4127705,
  0, 224889, 14661593, 980925, 3822, 0, 237177, 14661593, 980925, 61145,
  0, 921149049, 14661593, 980925, 257982, 0, 921149049, 16235993, 1030125, 4127705,
  1023, 15, 3513, 3822, 0, 16235993, 3993, 3961, 0, 16281,
  4095, 3549, 0, 63, 2937, 12023673, 0, 262041, 3801, 221,
  0, 237177, 16235993, 1030125, 3822, 14661593, 3993, 3949, 0, 16281,
  978670, 0, 262041, 3705, 221, 1023, 15, 238, 908765, 0,
  4095, 3549, 0, 63, 2937, 0, 224889, 16235993, 1030125, 61145,
  4095, 3549, 0, 63, 2937, 1023, 15, 238, 908765, 0,
  15658713, 0, 262041, 3705, 221, 14661593, 3993, 3577, 0, 16281,
  0, 971480697, 16235993, 1030125, 257982, 12023673, 0, 262041, 3801, 249,
  4095, 3549, 0, 63, 2937, 16235993, 3993, 3833, 0, 16281,
  1023, 15, 3513, 61145, 0
]
set_option Elab.async false in
private theorem checked0 : ∀ b c d : ZMod 5,
    let A : Mat := (0,b,c,d)
    (0:ZMod 5)*d-b*c ≠ 0 → signed A ∨ eval A 15 (certificate[0*125+b.val*25+c.val*5+d.val]!) = scalarTwo := by
  decide +kernel
set_option Elab.async false in
private theorem checked1 : ∀ b c d : ZMod 5,
    let A : Mat := (1,b,c,d)
    (1:ZMod 5)*d-b*c ≠ 0 → signed A ∨ eval A 15 (certificate[1*125+b.val*25+c.val*5+d.val]!) = scalarTwo := by
  decide +kernel
set_option Elab.async false in
private theorem checked2 : ∀ b c d : ZMod 5,
    let A : Mat := (2,b,c,d)
    (2:ZMod 5)*d-b*c ≠ 0 → signed A ∨ eval A 15 (certificate[2*125+b.val*25+c.val*5+d.val]!) = scalarTwo := by
  decide +kernel
set_option Elab.async false in
private theorem checked3 : ∀ b c d : ZMod 5,
    let A : Mat := (3,b,c,d)
    (3:ZMod 5)*d-b*c ≠ 0 → signed A ∨ eval A 15 (certificate[3*125+b.val*25+c.val*5+d.val]!) = scalarTwo := by
  decide +kernel
set_option Elab.async false in
private theorem checked4 : ∀ b c d : ZMod 5,
    let A : Mat := (4,b,c,d)
    (4:ZMod 5)*d-b*c ≠ 0 → signed A ∨ eval A 15 (certificate[4*125+b.val*25+c.val*5+d.val]!) = scalarTwo := by
  decide +kernel
theorem checked (a b c d : ZMod 5) (h : a*d-b*c ≠ 0) :
    signed (a,b,c,d) ∨ ∃ n, eval (a,b,c,d) 15 n = scalarTwo := by
  have hh : signed (a,b,c,d) ∨ eval (a,b,c,d) 15
      (certificate[a.val*125+b.val*25+c.val*5+d.val]!) = scalarTwo := by
    fin_cases a
    · exact checked0 b c d h
    · exact checked1 b c d h
    · exact checked2 b c d h
    · exact checked3 b c d h
    · exact checked4 b c d h
  exact hh.imp_right (fun he => ⟨_,he⟩)
end Matrix.GeneralLinearGroup.SignedFiveCertificate
