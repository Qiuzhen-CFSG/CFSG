module

public import Theory.SpecificGroups.ReeTwo.RootAction

/-!
# Core cocycles for the first binary Ree reflection

The Weyl action on the ten collected binary root coordinates has a short
polynomial expression. Its cocycles have five free coordinates. An explicit
conjugator shows that each is cohomologous either to the identity or to root 9.
This is the first-endpoint reduction for the pointed reflection-pair census.

Source: Shinoda (1975), (2.3), pp. 81–83; the ordered core and Weyl conventions
are those of `ReeTwo.Core` and `ReeTwo.Core.r`.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo

def rPolynomial (x:Core) : Core where
  b0 := x.b4
  b1 := x.b3
  b2 := x.b2
  b3 := x.b1
  b4 := x.b0
  b5 := x.b1*x.b4+x.b2*x.b4+x.b8
  b6 := x.b2*x.b3+x.b0*x.b4+x.b1*x.b4+x.b7
  b7 := x.b1*x.b2+x.b0*x.b3+x.b0*x.b4+x.b6
  b8 := x.b0*x.b2+x.b0*x.b3+x.b5
  b9 := x.b0*x.b3+x.b1*x.b4+x.b0*x.b1*x.b4+x.b0*x.b3*x.b4+x.b9

theorem rPolynomial_eq (x:Core) : rPolynomial x=Core.r x := by
  change rPolynomial x=Core.normalWord Core.rRoot (Core.coords x)
  simp only [Core.normalWord,Core.rRoot,Core.root_pow]
  change rPolynomial x = Core.mul (Core.mul (Core.mul (Core.mul (Core.mul (Core.mul (Core.mul (Core.mul (Core.mul (_) _) _) _) _) _) _) _) _) _
  apply Core.ext <;> simp [rPolynomial,Core.mul,Core.ofCoords,Core.coords,weylRoot]
  all_goals try ring_nf
  all_goals reduce_mod_char

def rCocycle (a b c d e : ZMod 2) : Core :=
  ⟨a, b, 0, b, a, c, d, d, c+b, e⟩

theorem rCocycle_form (x : Core) (h : x * Core.r x = 1) :
    x = rCocycle x.b0 x.b1 x.b5 x.b6 x.b9 := by
  rw [← rPolynomial_eq] at h
  change Core.mul x (rPolynomial x) = ⟨0,0,0,0,0,0,0,0,0,0⟩ at h
  have h4 : x.b4 = x.b0 := by
    have hh := congrArg Core.b0 h
    change x.b0 + x.b4 = 0 at hh
    simpa only [eq_neg_iff_add_eq_zero, ZMod.neg_eq_self_mod_two] using
      (add_eq_zero_iff_eq_neg.mp hh).symm
  have h3 : x.b3 = x.b1 := by
    have hh := congrArg Core.b1 h
    change x.b1 + x.b3 = 0 at hh
    simpa only [ZMod.neg_eq_self_mod_two] using (add_eq_zero_iff_eq_neg.mp hh).symm
  have sq (z : ZMod 2) : z ^ 2 = z := by exact (by decide : ∀ z : ZMod 2, z^2=z) z
  have h8 : x.b8 = x.b5+x.b1 := by
    have hh := congrArg Core.b5 h
    simp only [Core.mul, rPolynomial, h4, h3] at hh
    ring_nf at hh
    reduce_mod_char at hh
    simp only [sq] at hh
    simpa only [ZMod.neg_eq_self_mod_two] using (add_eq_zero_iff_eq_neg.mp hh).symm
  have h7 : x.b7 = x.b6 := by
    have hh := congrArg Core.b6 h
    simp only [Core.mul, rPolynomial, h4, h3] at hh
    ring_nf at hh
    reduce_mod_char at hh
    simpa only [ZMod.neg_eq_self_mod_two] using (add_eq_zero_iff_eq_neg.mp hh).symm
  have h2 : x.b2 = 0 := by
    have hh := congrArg Core.b9 h
    simp only [Core.mul, rPolynomial, h4, h3, h8, h7] at hh
    ring_nf at hh
    reduce_mod_char at hh
    simp only [sq] at hh
    ring_nf at hh
    reduce_mod_char at hh
    exact hh
  apply Core.ext <;> simp [rCocycle, h4, h3, h8, h7, h2]

def rConjugator (a b c d : ZMod 2) : Core :=
  ⟨a+c+b*c+b*d+b*c*d, b+c+d+b*d, d+b*d+b*c*d,
    c+d+b*d, c+b*c+b*d+b*c*d, 0,0,0,0,0⟩

theorem rCocycle_conjugator (a b c d e : ZMod 2) :
    rCocycle a b c d e = rConjugator a b c d *
      Core.root 9 ^ (a*c+b*d+e).val * Core.r (rConjugator a b c d)⁻¹ := by
  rw [← rPolynomial_eq]
  exact (by decide +kernel : ∀ a b c d e : ZMod 2,
    rCocycle a b c d e = rConjugator a b c d *
      Core.root 9 ^ (a*c+b*d+e).val * rPolynomial (rConjugator a b c d)⁻¹) a b c d e

theorem rCocycle_conjugate (x : Core) (h : x * Core.r x = 1) :
    ∃ g : Core, ∃ e : ZMod 2, x = g * Core.root 9 ^ e.val * Core.r g⁻¹ := by
  refine ⟨rConjugator x.b0 x.b1 x.b5 x.b6, x.b0*x.b5+x.b1*x.b6+x.b9, ?_⟩
  exact (rCocycle_form x h).trans (rCocycle_conjugator _ _ _ _ _)
end Tits.AmalgamRigidity.FullRee.PointedPairs
