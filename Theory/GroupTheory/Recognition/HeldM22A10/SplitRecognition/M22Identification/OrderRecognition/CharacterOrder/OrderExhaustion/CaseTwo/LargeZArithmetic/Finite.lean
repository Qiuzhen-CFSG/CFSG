module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeConstraints
public import Mathlib.Data.Int.Sqrt
/-!
# Complete divisor and quadratic enumeration for the large-Z branch

The denominator divides `1118208*z*(z+1)`. Prime-power factor lists enumerate
all its signed divisors, and completing the square enumerates every integral
root after substituting `y=x+z+1`. The congruence `x+r = 0 mod 128` gives the
stronger polynomial modulus `128*gcd(128*A,B-2*A*r)`, which avoids unnecessary
square-root calculations. The root list may include rounded nonroots; checking
this larger list still gives a valid exclusion.

The final soundness lemma applies the computation to the literal integer
system, using the restriction congruences, denominator divisibility, positivity
of the group order, and its factor 40320. The selected-row lemma retains all
nine choices of the two free multiplicities and both signs of the degree.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15. This supplies part of the arithmetic
omitted by the source's statement that the second decomposition is similar.
-/

@[expose] public section

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeZ

def factorsValue (fs : List (ℕ × ℕ)) : ℕ := (fs.map fun pe => pe.1 ^ pe.2).prod

def factorDivisors : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p,e) :: fs => (List.range (e+1)).flatMap fun k => (factorDivisors fs).map (p^k * ·)

theorem divisor_mem {fs : List (ℕ × ℕ)} (hp : ∀ pe ∈ fs, Nat.Prime pe.1)
    {d : ℕ} (hd : d ∣ factorsValue fs) : d ∈ factorDivisors fs := by
  induction fs generalizing d with
  | nil => simpa [factorsValue, factorDivisors] using Nat.eq_one_of_dvd_one hd
  | cons pe fs ih =>
    obtain ⟨p,e⟩ := pe
    change d ∣ p^e * factorsValue fs at hd
    obtain ⟨r,s,hr,hs,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨k,hk,rfl⟩ := (Nat.dvd_prime_pow (hp (p,e) (by simp))).mp hr
    exact List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨s, ih (fun pe h => hp pe (by simp [h])) hs, rfl⟩⟩

def signedDivisors (fs : List (ℕ × ℕ)) : List ℤ :=
  (factorDivisors fs).flatMap fun n : ℕ => [(n : ℤ), -(n : ℤ)]

theorem signed_mem {fs : List (ℕ × ℕ)} (hp : ∀ pe ∈ fs, Nat.Prime pe.1)
    {n d : ℤ} (hn : n.natAbs = factorsValue fs) (hd : d ∣ n) :
    d ∈ signedDivisors fs := by
  have h := Int.natAbs_dvd_natAbs.mpr hd
  rw [hn] at h
  apply List.mem_flatMap.mpr
  refine ⟨d.natAbs, divisor_mem hp h, ?_⟩
  rw [Int.natCast_natAbs]
  rcases le_total 0 d with he | he
  · simp [abs_of_nonneg he]
  · simp [abs_of_nonpos he]

def roots (A B C : ℤ) : List ℤ :=
  let D := B*B - 4*A*C
  let s := Int.sqrt D
  if s*s == D then [(-B+s)/(2*A), (-B-s)/(2*A)] else []

theorem root_mem {A B C x : ℤ} (hA : A ≠ 0) (hx : A*x*x+B*x+C=0) :
    x ∈ roots A B C := by
  have he : (2*A*x+B)*(2*A*x+B) = B*B-4*A*C := by linear_combination 4*A*hx
  have hs : Int.sqrt (B*B-4*A*C) = |2*A*x+B| := by
    rw [← he, Int.sqrt_eq, Int.natCast_natAbs]
  have hss : Int.sqrt (B*B-4*A*C)*Int.sqrt (B*B-4*A*C) = B*B-4*A*C :=
    (Int.exists_mul_self _).mp ⟨_,he⟩
  simp only [roots, hss, beq_self_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false]
  have h2 : 2*A ≠ 0 := mul_ne_zero (by norm_num) hA
  rcases le_total 0 (2*A*x+B) with h | h
  · left
    rw [hs, abs_of_nonneg h]
    have hn : -B+(2*A*x+B) = x*(2*A) := by ring
    rw [hn, Int.mul_ediv_cancel _ h2]
  · right
    rw [hs, abs_of_nonpos h]
    have hn : -B-(-(2*A*x+B)) = x*(2*A) := by ring
    rw [hn, Int.mul_ediv_cancel _ h2]

def unitRows (q v : ℤ) : List (ℤ × ℤ) :=
  ([-1,0,1] : List ℤ).flatMap fun u =>
    ([-1,0,1] : List ℤ).map fun w => (v+8*u+3*w, q+280*u+45*w)

theorem row_mem {g : ℕ} {q v d t : ℤ} (h : CaseTwoRowConditions g q v (d,t)) :
    ∃ r, (t,r) ∈ unitRows q v ∧ (d+r)%128=0 := by
  obtain ⟨_,u,hu,w,hw,ht,hd⟩ := h
  refine ⟨q+280*u+45*w, ?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨w,hw,by simp only [Prod.mk.injEq]; exact ⟨ht.symm,trivial⟩⟩⟩
  · convert Int.emod_eq_zero_of_dvd hd using 1
    congr 1
    ring

def validRoot (z rx ry P x : ℤ) : Bool :=
  let y := x+z+1
  let g := (1118208*x*y*z)/P
  (x+rx)%128 == 0 && (y+ry)%128 == 0 && decide (0 < g) && (g%40320 == 0)

def modulus (A B r : ℤ) : ℤ := 128 * (Int.gcd (128*A) (B-2*A*r) : ℤ)

theorem polynomial_congruence {A B C P x r : ℤ}
    (hx : (x+r)%128=0) (he : A*x*x+B*x+C=P) :
    (P-(A*r*r-B*r+C)) % modulus A B r = 0 := by
  obtain ⟨t,ht⟩ := Int.dvd_of_emod_eq_zero hx
  have hx' : x = 128*t-r := by omega
  have hd : (Int.gcd (128*A) (B-2*A*r) : ℤ) ∣ 128*A*t+(B-2*A*r) :=
    dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _) (Int.gcd_dvd_right _ _)
  apply Int.emod_eq_zero_of_dvd
  have he' : P-(A*r*r-B*r+C) = 128*(t*(128*A*t+(B-2*A*r))) := by
    rw [← he, hx']; ring
  rw [he']
  exact mul_dvd_mul (dvd_refl (128 : ℤ)) (dvd_mul_of_dvd_right hd t)

def rowCheck (fs : List (ℕ × ℕ)) (z c : ℤ) : Bool :=
  (unitRows 78 2).all fun ar =>
    (unitRows (-329) (-7)).all fun br =>
      if 1+ar.1-br.1+c == 16 then
        let A := z+c*c
        let B := z*(z+1)+ar.1*ar.1*z-br.1*br.1*z+c*c*(z+1)
        let C := ar.1*ar.1*z*(z+1)
        (signedDivisors fs).all fun P =>
          if (P-(A*ar.2*ar.2-B*ar.2+C)) % modulus A B ar.2 == 0 then
            (roots A B (C-P)).all fun x => !(validRoot z ar.2 br.2 P x)
          else true
      else true

theorem rowCheck_sound {fs : List (ℕ × ℕ)} {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c)
    (hp : ∀ pe ∈ fs, Nat.Prime pe.1)
    (hf : (1118208*z*(z+1)).natAbs = factorsValue fs)
    (hA : z+c*c ≠ 0) (hc : rowCheck fs z c = true) : False := by
  obtain ⟨rx,hrx,hxmod⟩ := row_mem S.row_x
  obtain ⟨ry,hry,hymod⟩ := row_mem S.row_y
  have hv := S.value
  have hy : y = x+z+1 := by have := S.degree; omega
  obtain ⟨hP,_,_,hd⟩ := S.denominator_bounds
  have hpMem := signed_mem hp hf hd
  have hrMem : x ∈ roots (z+c*c)
      (z*(z+1)+a*a*z-b*b*z+c*c*(z+1))
      (a*a*z*(z+1)-caseTwoDenominator x y z a b c) := by
    apply root_mem hA
    rw [hy]
    unfold caseTwoDenominator
    ring
  have h1 := List.all_eq_true.mp hc (a,rx) hrx
  have h2 := List.all_eq_true.mp h1 (b,ry) hry
  simp only [hv, beq_self_eq_true, ↓reduceIte] at h2
  have h3 := List.all_eq_true.mp h2 _ hpMem
  have hcon := polynomial_congruence hxmod (show
      (z+c*c)*x*x+(z*(z+1)+a*a*z-b*b*z+c*c*(z+1))*x+a*a*z*(z+1)=
        caseTwoDenominator x y z a b c by rw [hy]; unfold caseTwoDenominator; ring)
  simp only [hcon, beq_self_eq_true, ↓reduceIte] at h3
  have h4 := List.all_eq_true.mp h3 x hrMem
  have hg : 1118208*x*y*z/caseTwoDenominator x y z a b c = (g : ℤ) := by
    rw [← S.suzuki, Int.mul_ediv_cancel _ hP]
  obtain ⟨h,hh,hg',_,_⟩ := S.cofactor
  have hpos : (0 : ℤ) < g := by exact_mod_cast (by omega : 0 < g)
  have hgmod : (g : ℤ)%40320=0 := by
    rw [hg']
    simp
  simp [validRoot, ← hy, hxmod, hymod, hg, hgmod] at h4
  omega



def zRows : List (ℤ × ℤ) :=
  [(-58, -10), (70, -10), (-186, -10), (198, -10),
    (-314, -10), (326, -10), (25, -7), (-103, -7),
    (153, -7), (-20, -4), (1, 1), (-44, 4),
    (22, 6), (-106, 6), (-23, 9), (105, 9),
    (-151, 9), (233, 9), (-279, 9), (60, 12),
    (-68, 12), (188, 12), (-196, 12), (316, 12),
    (-324, 12), (444, 12), (-452, 12), (572, 12)]

theorem zRow_mem {g : ℕ} {z c : ℤ} (hz : CaseTwoRowConditions g 127 1 (z,c))
    (hr : (z.natAbs : ℤ) < 4*c^2) : (z,c) ∈ zRows := by
  obtain ⟨_,u,hu,v,hv,hc,hd⟩ := hz
  rw [Int.natCast_natAbs, abs_lt] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  change c = 1+8*u+3*v at hc
  change 128 ∣ z+127+280*u+45*v at hd
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    norm_num at hc <;> subst c <;>
    simp only [zRows, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] <;>
    norm_num at hr hd ⊢ <;> omega
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeZ
