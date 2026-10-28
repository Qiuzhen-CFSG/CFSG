module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.RankOneTorus
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters

/-!
# Scalar arithmetic forced by a marked rank-one action

An additive action on two axes, whose upper roots are shears and whose
Weyl element exchanges the axes, determines the arithmetic of its shear
coefficients. The parameterized rank-one word identifies the diagonal
with the two inverse shears. Multiplication of these actual diagonal
matrices then forces multiplicativity of the coefficient operators.

This uses the whole SL₂ action, not a supplied linear representation or
field embedding. NaturalScalarAction applies it to the literal source
radical quotient, then uses the full Cartan to prove linearity over the
already chosen cubic field. All binary parameters, including 2 and 4,
are retained.

Source: Fong--Seitz II (9.24)--(9.27), printed pp.218--219. This elementary
rank-one argument supplies the natural-action calculation directly.
-/

@[expose] public noncomputable section
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.NaturalShears
variable {K E : Type*} [Field K] [CharP K 2] [Field E] [CharP E 2]
  (r : SL2 K →* MulAut (Multiplicative E × Multiplicative E))
  (f : K → E →+ E)
  (hU : ∀ b a c, r (uni b) (.ofAdd a,.ofAdd c) = (.ofAdd a,.ofAdd (f b a+c)))
  (hW : ∀ a b : Multiplicative E, r (weyl K) (a,b) = (b,a))
  (h1 : ∀ a, f 1 a = a)

omit [CharP K 2] [CharP E 2] in
include hU in
/-- Addition of root parameters adds the corresponding coefficient operators. -/
theorem parameter_add (b c : K) (a : E) : f (b+c) a = f b a+f c a := by
  have h := congrArg (fun g : SL2 K => r g (.ofAdd a,.ofAdd 0)) (uni_mul_uni b c)
  simp only [map_mul,MulAut.mul_apply,hU,add_zero] at h
  exact (congrArg (fun z : Multiplicative E × Multiplicative E => z.2.toAdd) h).symm

omit [CharP K 2] [CharP E 2] in
include hU h1 in
private theorem tor_second_first_zero (t : Kˣ) (a : E) :
    (r (tor t) (.ofAdd 0,.ofAdd a)).1 = .ofAdd 0 := by
  have hm : uni (1 : K)*tor t = tor t*uni ((t⁻¹ : Kˣ).val^2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,pow_two]
  have hh := congrArg (fun g : SL2 K => r g (.ofAdd 0,.ofAdd a)) hm
  simp only [map_mul,MulAut.mul_apply,hU,map_zero,zero_add] at hh
  let z := r (tor t) (.ofAdd 0,.ofAdd a)
  change r (uni 1) (z.1,z.2) = (z.1,z.2) at hh
  have hu := hU 1 z.1.toAdd z.2.toAdd
  rw [h1] at hu
  have hz : z.1.toAdd+z.2.toAdd=z.2.toAdd :=
    congrArg (fun v : Multiplicative E × Multiplicative E => v.2.toAdd) (hu.symm.trans hh)
  exact Multiplicative.toAdd.injective (add_right_cancel (hz.trans (zero_add _).symm))

include hU hW h1 in
/-- Every nonzero shear has the shear at the inverse parameter as inverse. -/
theorem inverse_parameter (t : Kˣ) (a : E) : f (t⁻¹).val (f t.val a) = a := by
  have hw : (weyl K)⁻¹ = weyl K := inv_eq_of_mul_eq_one_right weyl_sq
  have hh := congrArg (fun g : SL2 K => r g (.ofAdd a,.ofAdd 0)) (weyl_parameter_word t)
  simp only [hw,map_mul,MulAut.mul_apply,hU,hW,add_zero] at hh
  have he := congrArg Prod.fst hh
  rw [tor_second_first_zero r f hU h1] at he
  exact CharTwo.add_eq_zero.mp (congrArg Multiplicative.toAdd he)

include hU hW h1 in
/-- The diagonal acts on the two axes by inverse mutually commuting shears. -/
theorem action_tor (t : Kˣ) (a b : E) :
    r (tor t) (.ofAdd a,.ofAdd b) =
      (.ofAdd (f (t⁻¹).val a),.ofAdd (f t.val b)) := by
  have hw : (weyl K)⁻¹ = weyl K := inv_eq_of_mul_eq_one_right weyl_sq
  have hh := congrArg (fun g : SL2 K => r g (.ofAdd b,.ofAdd a)) (weyl_parameter_word t)
  simp only [hw,map_mul,MulAut.mul_apply,hU,hW] at hh
  have hinv : f t.val (f (t⁻¹).val a) = a := by
    simpa only [inv_inv] using inverse_parameter r f hU hW h1 t⁻¹ a
  have cancel (x y : E) : x+y+x=y := by
    rw [add_right_comm,CharTwo.add_self_eq_zero,zero_add]
  simp only [map_add,inverse_parameter r f hU hW h1,hinv,cancel] at hh
  simpa only [← add_assoc,cancel] using hh.symm

include hU hW h1 in
/-- Multiplicativity follows from the whole diagonal subgroup of the same actor. -/
theorem parameter_mul (b c : K) (a : E) : f (b*c) a = f b (f c a) := by
  have hz (x : E) : f 0 x = 0 := by
    have hh := parameter_add r f hU 0 0 x
    simpa only [add_zero,CharTwo.add_self_eq_zero] using hh
  by_cases hb : b = 0
  · simp [hb,hz]
  by_cases hc : c = 0
  · simp [hc,hz]
  let u := Units.mk0 b hb
  let v := Units.mk0 c hc
  have hh := congrArg (fun g : SL2 K => r g (.ofAdd 0,.ofAdd a)) (tor_mul u v)
  simp only [map_mul,MulAut.mul_apply,action_tor r f hU hW h1,map_zero] at hh
  exact congrArg (fun z : Multiplicative E × Multiplicative E => z.2.toAdd) hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.NaturalShears
