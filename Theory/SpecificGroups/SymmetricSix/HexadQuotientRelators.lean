module

public import Theory.SpecificGroups.SymmetricSix.HexadCubicWord
public import Theory.SpecificGroups.MathieuAmalgamCompletion.Relators
import all Theory.SpecificGroups.SymmetricSix.HexadCubicWord

/-!
# Simultaneous marked-pair quotient relators

The internal import of HexadCubicWord deliberately reuses its exact
`pair_conjugate` proof and canonical pair. A single finite choice gives both
the fixed-free word 25 and words 17–22 and 24. Conjugating every literal word
back retains the caller's pair and the same exterior-cubic variant.
-/

public noncomputable section
open Equiv Subgroup Subgroup.CosetWordCertificate
namespace Theory.SpecificGroups.SymmetricSix.HexadCubicWord
open Matrix.PSL3Four.MathieuAmalgamMarking
open Theory.SpecificGroups.MathieuAmalgamCompletion
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

private theorem eval_hom_relators {G H α : Type*} [Group G] [Group H]
    (f : G→*H) (p : α→G) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

private theorem eval_agrees_relators {G α : Type*} [Group G]
    (g h : α→G) (w : Word α)
    (ha : ∀ a∈w,g a.1=h a.1) : eval g w=eval h w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [eval_cons,eval_cons,ha a (by simp),ih (fun b hb => ha b (by simp [hb]))]

private theorem remaining_support : ∀ i : Fin 27,
    (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
    ∀ a∈relator i, a.1≠2 := by decide +kernel

private theorem canonical_relator_choice : ∀ n : S6, n^3=1 → n ≠ 1 →
    n ≠ torusWordValue a0 b0 → n ≠ (torusWordValue a0 b0)^2 →
    n * torusWordValue a0 b0 = torusWordValue a0 b0 * n →
    ∃ ε : Bool, ∃ k : Fin 3,
      let m := (if ε then n else n⁻¹) * (torusWordValue a0 b0)^k.val
      yWord a0 b0 m ^3=1 ∧
      (∀ d : Duad, (duadSet d).image (yWord a0 b0 m) ≠ duadSet d) ∧
      ∀ i : Fin 27, (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
        eval ![a0,b0,1,m] (relator i)=1 := by
  decide +kernel

/-- For the same marked (3,2,5) pair, one of the six original exterior-cubic
variants makes the last hexad word a fixed-point-free cubic in the polar action. -/
theorem exists_cubic_variant_relators (a b n : S6) (ha : a^3=1)
    (hfree : ∀ v : NaturalModule, polarAction a v=v → v=0)
    (hb : b.sign=1) (hb2 : b^2=1) (hab : (a*b)^5=1)
    (hn : n^3=1) (hne : n≠1)
    (hnt : n≠eval ![a,b] torusWord)
    (hnt2 : n≠(eval ![a,b] torusWord)^2)
    (hcomm : Commute n (eval ![a,b] torusWord)) :
    ∃ ε : Bool, ∃ k : Fin 3,
      let m := (if ε then n else n⁻¹) * (eval ![a,b] torusWord)^k.val
      (m*a⁻¹*m⁻¹*b*m*a)^3=1 ∧
      (∀ v : NaturalModule, polarAction (m*a⁻¹*m⁻¹*b*m*a) v=v → v=0) ∧
      ∀ ell : S6, ∀ i : Fin 27,
        (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
        eval ![a,b,ell,m] (relator i)=1 := by
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
  obtain ⟨ε,k,hpow,hfix,hwords⟩ := canonical_relator_choice (f n) hn3 hn1 hnt' hnt2' hnc
  let Y := ((if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val)*a⁻¹*
    (((if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val))⁻¹*b*
    ((if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val)*a
  have hmap : f Y=yWord a0 b0
      ((if ε then f n else (f n)⁻¹)*(torusWordValue a0 b0)^k.val) := by
    simp only [Y,map_mul,map_inv,map_pow,apply_ite,hfa,hfb,ht,yWord]
  refine ⟨ε,k,?_,?_,?_⟩
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

  · intro ell i hi
    let m := (if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val
    change eval ![a,b,ell,m] (relator i)=1
    apply f.injective
    change f.toMonoidHom (eval ![a,b,ell,m] (relator i)) = f.toMonoidHom 1
    rw [eval_hom_relators f.toMonoidHom,map_one]
    calc
      eval (fun j => f (![a,b,ell,m] j)) (relator i) =
          eval ![a0,b0,1,(if ε then f n else (f n)⁻¹)*(torusWordValue a0 b0)^k.val]
            (relator i) := by
        apply eval_agrees_relators
        rintro ⟨j,s⟩ hj
        have hne := remaining_support i hi ⟨j,s⟩ hj
        fin_cases j
        · exact hfa
        · exact hfb
        · exact (hne rfl).elim
        · change f m=(if ε then f n else (f n)⁻¹)*(torusWordValue a0 b0)^k.val
          simp only [m,map_mul,map_inv,map_pow,apply_ite,ht]
      _ = 1 := hwords i hi

end Theory.SpecificGroups.SymmetricSix.HexadCubicWord
