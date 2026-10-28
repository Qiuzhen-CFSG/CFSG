module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Matrices
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Selecting a cubic for the last hexad power word

Normalize the first member of the marked (3,2,5) pair by its cubic cycle type.
The eighteen possibilities for the second member are the orbit under its
centralizer. A six-element cubic calculation then selects the original cubic
or its inverse, times a power of the retained torus word. The resulting word
has cube one and no nonzero fixed vector in the actual polar module.
-/

public noncomputable section
open Equiv Subgroup Subgroup.CosetWordCertificate
namespace Theory.SpecificGroups.SymmetricSix.HexadCubicWord
open Matrix.PSL3Four.MathieuAmalgamMarking
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

private def a0 : S6 := swap 0 1 * swap 1 4 * (swap 2 3 * swap 3 5)
private def b0 : S6 := swap 0 1 * swap 2 4
private def torusWordValue (a b : S6) := eval ![a,b] torusWord
private def yWord (a b n : S6) := n*a⁻¹*n⁻¹*b*n*a
private def actor (i : Fin 3) (j : Fin 3) (b : Bool) : S6 :=
  (swap 0 1 * swap 1 4)^i.val * (swap 2 3 * swap 3 5)^j.val *
    (if b then swap 0 2 * swap 1 3 * swap 4 5 else 1)

private theorem cubic_type : ∀ a : S6, a ^ 3 = 1 →
    (∀ d : Duad, (duadSet d).image a ≠ duadSet d) →
    a.cycleType = a0.cycleType := by decide +kernel

private theorem tail_orbit : ∀ b : S6, b.sign=1 → b^2=1 → (a0*b)^5=1 →
    ∃ i : Fin 3, ∃ j : Fin 3, ∃ z : Bool,
      actor i j z*a0*(actor i j z)⁻¹=a0 ∧
      actor i j z*b0*(actor i j z)⁻¹=b := by decide +kernel

private theorem canonical_choice : ∀ n : S6, n^3=1 → n ≠ 1 →
    n ≠ torusWordValue a0 b0 → n ≠ (torusWordValue a0 b0)^2 →
    n * torusWordValue a0 b0 = torusWordValue a0 b0 * n →
    ∃ ε : Bool, ∃ k : Fin 3,
      let m := (if ε then n else n⁻¹) * (torusWordValue a0 b0)^k.val
      yWord a0 b0 m ^3=1 ∧
      (∀ d : Duad, (duadSet d).image (yWord a0 b0 m) ≠ duadSet d) := by
  decide +kernel

private theorem no_duad_iff (g : S6) :
    (∀ d : Duad, (duadSet d).image g ≠ duadSet d) ↔
      ∀ v : NaturalModule, polarAction g v=v → v=0 := by
  constructor
  · intro hg v hv
    by_contra hn
    obtain ⟨d,hd⟩ := polarVector_bijective.2 ⟨v,hn⟩
    have hdv : (polarVector d).val = v := congrArg Subtype.val hd
    rw [←hdv,polarAction_vector] at hv
    have hh := polarVector_injective (Subtype.ext hv)
    exact hg d (by rw [←duadSet_smul,hh])
  · intro hg d hd
    have hs : g • d=d := duadSet_injective (by rw [duadSet_smul,hd])
    have hv : polarAction g (polarVector d).val=(polarVector d).val := by
      rw [polarAction_vector,hs]
    exact (polarVector d).property (hg _ hv)

private theorem eval_conj (g : S6) (p : Fin 2→S6) (w : Word (Fin 2)) :
    eval (fun i => MulAut.conj g (p i)) w=MulAut.conj g (eval p w) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,ih,map_mul]
    cases a with
    | mk a b => cases b <;> simp [mul_assoc]

private theorem fixed_conj (g a : S6)
    (ha : ∀ v : NaturalModule, polarAction a v=v → v=0) :
    ∀ v : NaturalModule, polarAction (MulAut.conj g a) v=v → v=0 := by
  intro v hv
  have hh : polarAction a (polarAction g⁻¹ v)=polarAction g⁻¹ v := by
    have hh := congrArg (polarAction g⁻¹) hv
    simpa only [MulAut.conj_apply,←polarAction_mul,mul_assoc,inv_mul_cancel_left] using hh
  have hz := ha _ hh
  have hh := congrArg (polarAction g) hz
  simpa only [←polarAction_mul,mul_inv_cancel,polarAction_one,polarAction_zero] using hh

private theorem pair_conjugate (a b : S6) (ha : a^3=1)
    (hfree : ∀ v : NaturalModule, polarAction a v=v → v=0)
    (hb : b.sign=1) (hb2 : b^2=1) (hab : (a*b)^5=1) :
    ∃ g : S6, MulAut.conj g a0=a ∧ MulAut.conj g b0=b := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq
    (cubic_type a ha ((no_duad_iff a).mpr hfree)).symm)
  let f := MulAut.conj g⁻¹
  have hfa : f a=a0 := by change g⁻¹*a*g=a0; rw [←hg]; group
  have hfb : (f b).sign=1 := by
    change (g⁻¹*b*g).sign=1
    simp only [map_mul,map_inv,hb,mul_one,inv_mul_cancel]
  have hfb2 : (f b)^2=1 := by rw [←map_pow,hb2,map_one]
  have hfab : (a0*f b)^5=1 := by rw [←hfa,←map_mul,←map_pow,hab,map_one]
  obtain ⟨i,j,z,ha',hb'⟩ := tail_orbit (f b) hfb hfb2 hfab
  refine ⟨g*actor i j z,?_,?_⟩
  · change (g*actor i j z)*a0*(g*actor i j z)⁻¹=a
    calc
      _ = g*(actor i j z*a0*(actor i j z)⁻¹)*g⁻¹ := by group
      _ = a := by rw [ha',hg]
  · change (g*actor i j z)*b0*(g*actor i j z)⁻¹=b
    calc
      _ = g*(actor i j z*b0*(actor i j z)⁻¹)*g⁻¹ := by group
      _ = b := by rw [hb']; change g*(g⁻¹*b*g)*g⁻¹=b; group

/-- For the same marked (3,2,5) pair, one of the six original exterior-cubic
variants makes the last hexad word a fixed-point-free cubic in the polar action. -/
theorem exists_cubic_variant (a b n : S6) (ha : a^3=1)
    (hfree : ∀ v : NaturalModule, polarAction a v=v → v=0)
    (hb : b.sign=1) (hb2 : b^2=1) (hab : (a*b)^5=1)
    (hn : n^3=1) (hne : n≠1)
    (hnt : n≠eval ![a,b] torusWord)
    (hnt2 : n≠(eval ![a,b] torusWord)^2)
    (hcomm : Commute n (eval ![a,b] torusWord)) :
    ∃ ε : Bool, ∃ k : Fin 3,
      let m := (if ε then n else n⁻¹) * (eval ![a,b] torusWord)^k.val
      (m*a⁻¹*m⁻¹*b*m*a)^3=1 ∧
      ∀ v : NaturalModule, polarAction (m*a⁻¹*m⁻¹*b*m*a) v=v → v=0 := by
  obtain ⟨g,hga,hgb⟩ := pair_conjugate a b ha hfree hb hb2 hab
  let f := MulAut.conj g⁻¹
  have hfa : f a=a0 := by change g⁻¹*a*g=a0; rw [←hga]; simp [MulAut.conj_apply,mul_assoc]
  have hfb : f b=b0 := by change g⁻¹*b*g=b0; rw [←hgb]; simp [MulAut.conj_apply,mul_assoc]
  have ht : f (eval ![a,b] torusWord)=torusWordValue a0 b0 := by
    rw [←eval_conj]
    congr 1
    funext i
    fin_cases i
    · exact hfa
    · exact hfb
  have hn3 : (f n)^3=1 := by rw [←map_pow,hn,map_one]
  have hn1 : f n≠1 := by simpa using (f.injective.ne hne)
  have hnt' : f n≠torusWordValue a0 b0 := by rw [←ht]; exact f.injective.ne hnt
  have hnt2' : f n≠(torusWordValue a0 b0)^2 := by rw [←ht,←map_pow]; exact f.injective.ne hnt2
  have hnc : f n*torusWordValue a0 b0=torusWordValue a0 b0*f n := by
    rw [←ht,←map_mul,←map_mul,hcomm.eq]
  obtain ⟨ε,k,hpow,hfix⟩ := canonical_choice (f n) hn3 hn1 hnt' hnt2' hnc
  let Y := ((if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val)*a⁻¹*
    (((if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val))⁻¹*b*
    ((if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val)*a
  have hmap : f Y=yWord a0 b0
      ((if ε then f n else (f n)⁻¹)*(torusWordValue a0 b0)^k.val) := by
    simp only [Y,map_mul,map_inv,map_pow,apply_ite,hfa,hfb,ht,yWord]
  refine ⟨ε,k,?_,?_⟩
  · change Y^3=1
    apply f.injective
    rw [map_pow,hmap,hpow,map_one]
  · have hh := fixed_conj g _ ((no_duad_iff _).mp hfix)
    have he : MulAut.conj g (f Y)=Y := by
      change g*(g⁻¹*Y*g)*g⁻¹=Y
      group
    rw [hmap] at he
    rw [he] at hh
    exact hh

end Theory.SpecificGroups.SymmetricSix.HexadCubicWord
