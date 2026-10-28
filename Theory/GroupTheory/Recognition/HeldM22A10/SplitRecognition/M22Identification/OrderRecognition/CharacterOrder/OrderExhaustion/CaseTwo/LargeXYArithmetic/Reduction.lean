module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeConstraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic.Sieve

/-!
# Reduction of large selected degrees to checked finite searches

The integer system supplies membership in the finite row and denominator lists.
Substituting `z = y-x-1` produces the two quadratic polynomials below. For the
only possible constant polynomial, `y=225`, `b=-15` and `c=-a`; nonzero P and
positive g force `0 < x < 224`. Thus the finite root enumeration covers this
case too. Candidate checking retains all original divisibility, congruence,
sign, and cofactor conditions.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY

@[expose] public def alternative (g x y a b : ℤ) : Prop :=
  g = 443520 ∨ (g = 93824640 ∧ x = -358 ∧ y = 180) ∨ (a = 7 ∧ b = -2)

public instance (g x y a b : ℤ) : Decidable (alternative g x y a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Direct arithmetic checking of a candidate recovered from a denominator and a root. -/
@[expose] public def candidateCheck (x y z : ℤ) (r s t : ℤ × ℤ) : Bool :=
  if (x+r.2)%128 = 0 ∧ (y+s.2)%128 = 0 ∧ (z+t.2)%128 = 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 then
    let P := caseTwoDenominator x y z r.1 s.1 t.1
    let N := 1118208*x*y*z
    let g := N/P
    decide ((P ≠ 0 ∧ N%P = 0 ∧ 0 < g ∧ g%40320 = 0 ∧
      (g/40320)%2 ≠ 0 ∧ (g/40320)%3 ≠ 0 ∧ g%x = 0 ∧ g%y = 0 ∧ g%z = 0) →
      alternative g x y r.1 s.1)
  else true

public theorem candidateCheck_sound {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c) {r s t : ℤ × ℤ}
    (ha : a = r.1) (hb : b = s.1) (hc : c = t.1)
    (hx : (x+r.2)%128 = 0) (hy : (y+s.2)%128 = 0) (hz : (z+t.2)%128 = 0)
    (hcheck : candidateCheck x y z r s t = true) : alternative g x y a b := by
  have hP := S.denominator_bounds.1
  have he : 1118208*x*y*z / caseTwoDenominator x y z a b c = (g : ℤ) :=
    Int.ediv_eq_of_eq_mul_left hP S.suzuki.symm
  have hd : 1118208*x*y*z % caseTwoDenominator x y z a b c = 0 := by
    rw [← S.suzuki]
    simp
  obtain ⟨h,hh,hg,h2,h3⟩ := S.cofactor
  have hge : (g : ℤ) = 40320*(h : ℤ) := by exact_mod_cast hg
  have hgdiv : (g : ℤ)/40320 = (h : ℤ) := by rw [hge]; omega
  have hp : (0 : ℤ) < g := by omega
  have h2' : (h : ℤ)%2 ≠ 0 := by
    intro hh2
    apply h2
    exact_mod_cast Int.dvd_of_emod_eq_zero hh2
  have h3' : (h : ℤ)%3 ≠ 0 := by
    intro hh3
    apply h3
    exact_mod_cast Int.dvd_of_emod_eq_zero hh3
  rw [candidateCheck, if_pos ⟨hx,hy,hz,S.nonzero_x,S.nonzero_y,S.nonzero_z⟩] at hcheck
  rw [← ha, ← hb, ← hc] at hcheck
  dsimp only at hcheck
  rw [he] at hcheck
  apply of_decide_eq_true hcheck
  refine ⟨hP,hd,hp,?_,?_,?_,Int.emod_eq_zero_of_dvd S.row_x.1,
    Int.emod_eq_zero_of_dvd S.row_y.1,Int.emod_eq_zero_of_dvd S.row_z.1⟩
  · rw [hge]; omega
  · rwa [hgdiv]
  · rwa [hgdiv]

@[expose] public def checkX (p : ℤ × (ℤ × ℤ)) : Bool :=
  (rows (-329) (-7)).all fun s => (rows 127 1).all fun t =>
    if 1+p.2.1-s.1+t.1=16 then
      (denominators p.1 (p.1+1)).all fun P =>
        (rootsAt (p.2.1^2+p.1)
          (-p.2.1^2*p.1-p.2.1^2-s.1^2*p.1+t.1^2*p.1-p.1^2-p.1)
          (s.1^2*p.1*(p.1+1)-P) s.2).all fun y =>
          candidateCheck p.1 y (y-p.1-1) p.2 s t
    else true

@[expose] public def checkY (p : ℤ × (ℤ × ℤ)) : Bool :=
  (rows 78 2).all fun r => (rows 127 1).all fun t =>
    if 1+r.1-p.2.1+t.1=16 then
      (denominators p.1 (p.1-1)).all fun P =>
        (rootsAt (p.2.1^2-p.1)
          (-r.1^2*p.1-p.2.1^2*p.1+p.2.1^2+t.1^2*p.1+p.1^2-p.1)
          (r.1^2*p.1*(p.1-1)-P) r.2).all fun x =>
          candidateCheck x p.1 (p.1-1-x) r p.2 t
    else true

set_option maxRecDepth 100000 in
public theorem largeX_facts :
    (largeRows 78 2).all (fun p => decide (p.1+1 ≠ 0 ∧ p.2.1^2+p.1 ≠ 0)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem largeY_facts :
    (largeRows (-329) (-7)).all (fun p =>
      decide (p.1-1 ≠ 0 ∧ (p.2.1^2-p.1=0 → p.1=225 ∧ p.2.1 = -15))) = true := by
  decide +kernel

/-- The only constant-polynomial case has positive complementary degrees. -/
public theorem constantY_bound {g : ℕ} {x z a c : ℤ}
    (S : CaseTwoIntegerSystem g x 225 z a (-15) c) : 0 ≤ x ∧ x < 225 := by
  have hz : z = 224-x := by have := S.degree; omega
  have hc : c = -a := by have := S.value; omega
  have hP : caseTwoDenominator x 225 z a (-15) c = 50400*a^2 := by
    rw [hz,hc]
    unfold caseTwoDenominator
    ring
  have hane : a ≠ 0 := by
    intro h
    apply S.denominator_bounds.1
    rw [hP,h]
    norm_num
  have hPpos : 0 < caseTwoDenominator x 225 z a (-15) c := by
    rw [hP]
    exact mul_pos (by norm_num) (sq_pos_of_ne_zero hane)
  obtain ⟨h,hh,hg,_,_⟩ := S.cofactor
  have hgpos : (0 : ℤ) < g := by omega
  have hpos := mul_pos hgpos hPpos
  rw [S.suzuki, hz] at hpos
  have hprod : 0 < x*(224-x) := by nlinarith
  rcases (mul_pos_iff.mp hprod) with ⟨hx,hz⟩ | ⟨hx,hz⟩ <;> omega

public theorem checkX_sound {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c)
    (hr : (x.natAbs : ℤ) < 4*a^2)
    (hcheck : (largeRows 78 2).all checkX = true) : alternative g x y a b := by
  obtain ⟨r,hrm,har,hxr⟩ := row_mem S.row_x
  obtain ⟨s,hsm,hbs,hys⟩ := row_mem S.row_y
  obtain ⟨t,htm,hct,hzt⟩ := row_mem S.row_z
  have hpm := largeRow_mem hrm S.nonzero_x hxr (har ▸ hr)
  have hf := of_decide_eq_true (List.all_eq_true.mp largeX_facts _ hpm)
  have hP := S.denominator_bounds
  have hm := mem_denominators S.nonzero_x hf.1 hP.2.1
  have hroot : y ∈ rootsAt (r.1^2+x)
      (-r.1^2*x-r.1^2-s.1^2*x+t.1^2*x-x^2-x)
      (s.1^2*x*(x+1)-caseTwoDenominator x y z a b c) s.2 := by
    apply mem_rootsAt
    · rw [← har,← hbs,← hct]
      have hz : z = y-x-1 := by have := S.degree; omega
      rw [hz]
      unfold caseTwoDenominator
      ring
    · exact hys
    · intro hh
      exact (hf.2 hh).elim
  have ht := List.all_eq_true.mp hcheck _ hpm
  simp only [checkX] at ht
  have ht := List.all_eq_true.mp (List.all_eq_true.mp ht _ hsm) _ htm
  have hv : 1+r.1-s.1+t.1=16 := by rw [← har,← hbs,← hct]; exact S.value
  rw [if_pos hv] at ht
  have ht := List.all_eq_true.mp (List.all_eq_true.mp ht _ hm) _ hroot
  have hz : y-x-1 = z := by have := S.degree; omega
  rw [hz] at ht
  exact candidateCheck_sound S har hbs hct hxr hys hzt ht

public theorem checkY_sound {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c)
    (hr : (y.natAbs : ℤ) < 4*b^2)
    (hcheck : (largeRows (-329) (-7)).all checkY = true) : alternative g x y a b := by
  obtain ⟨r,hrm,har,hxr⟩ := row_mem S.row_x
  obtain ⟨s,hsm,hbs,hys⟩ := row_mem S.row_y
  obtain ⟨t,htm,hct,hzt⟩ := row_mem S.row_z
  have hpm := largeRow_mem hsm S.nonzero_y hys (hbs ▸ hr)
  have hf := of_decide_eq_true (List.all_eq_true.mp largeY_facts _ hpm)
  have hP := S.denominator_bounds
  have hm := mem_denominators S.nonzero_y hf.1 hP.2.2.1
  have hroot : x ∈ rootsAt (s.1^2-y)
      (-r.1^2*y-s.1^2*y+s.1^2+t.1^2*y+y^2-y)
      (r.1^2*y*(y-1)-caseTwoDenominator x y z a b c) r.2 := by
    apply mem_rootsAt
    · rw [← har,← hbs,← hct]
      have hz : z = y-1-x := by have := S.degree; omega
      rw [hz]
      unfold caseTwoDenominator
      ring
    · exact hxr
    · intro hA _
      obtain ⟨hy,hb⟩ := hf.2 hA
      have hb' : b = -15 := hbs.trans hb
      change y = 225 at hy
      exact constantY_bound (show CaseTwoIntegerSystem g x 225 z a (-15) c by
        simpa only [hy,hb'] using S)
  have ht := List.all_eq_true.mp hcheck _ hpm
  simp only [checkY] at ht
  have ht := List.all_eq_true.mp (List.all_eq_true.mp ht _ hrm) _ htm
  have hv : 1+r.1-s.1+t.1=16 := by rw [← har,← hbs,← hct]; exact S.value
  rw [if_pos hv] at ht
  have ht := List.all_eq_true.mp (List.all_eq_true.mp ht _ hm) _ hroot
  have hz : y-1-x = z := by have := S.degree; omega
  rw [hz] at ht
  exact candidateCheck_sound S har hbs hct hxr hys hzt ht

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY
