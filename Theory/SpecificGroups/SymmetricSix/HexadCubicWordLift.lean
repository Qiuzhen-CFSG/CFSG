module

public import Theory.SpecificGroups.SymmetricSix.HexadCubicWord
public import Theory.SpecificGroups.SymmetricSix.PolarAffine.FixedFreePower

/-!
# The last hexad power word in the original marked extension

The quotient calculation selects one of the same six cubic variants.
The cube of the resulting word lies in the actual kernel and is fixed by
conjugation by that word. Its fixed-point-free polar action therefore kills
the cube. No section or splitting of the extension is needed.
-/

public noncomputable section
open Subgroup Subgroup.CosetWordCertificate
namespace Theory.SpecificGroups.SymmetricSix.HexadCubicWord
open Matrix.PSL3Four.MathieuAmalgamMarking

private theorem eval_hom {G H α : Type*} [Group G] [Group H]
    (f : G→*H) (p : α→G) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

/-- The literal natural-kernel extension satisfies relator 25 after choosing
one of the six variants of its original exterior cubic. The shared pair is
unchanged and no splitting of the original quotient is assumed. -/
theorem exists_lifted_cubic_variant {G : Type*} [Group G]
    (q : G→*A6) (e : q.ker≃*Multiplicative NaturalModule)
    (he : ∀ (g : G) (a : q.ker),
      e (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (polarAction (q g).val (e a).toAdd))
    (a b n : G) (ha : a^3=1)
    (hfree : ∀ v : NaturalModule, polarAction (q a).val v=v → v=0)
    (hb2 : (q b)^2=1) (hab : (a*b)^5=1) (hn : n^3=1)
    (hne : q n≠1) (hnt : q n≠q (eval ![a,b] torusWord))
    (hnt2 : q n≠q ((eval ![a,b] torusWord)^2))
    (hcomm : Commute n (eval ![a,b] torusWord)) :
    ∃ ε : Bool, ∃ k : Fin 3,
      let m := (if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val
      ∀ ell : G, eval ![a,b,ell,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25)=1 := by
  let f : G→*S6 := (alternatingGroup (Fin 6)).subtype.comp q
  have ht : f (eval ![a,b] torusWord)=eval ![f a,f b] torusWord := by
    rw [eval_hom]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hfa : (f a)^3=1 := by rw [←map_pow,ha,map_one]
  have hfb : (f b).sign=1 := (q b).property
  have hfb2 : (f b)^2=1 := congrArg Subtype.val hb2
  have hfab : (f a*f b)^5=1 := by rw [←map_mul,←map_pow,hab,map_one]
  have hfn : (f n)^3=1 := by rw [←map_pow,hn,map_one]
  have hfn1 : f n≠1 := fun hh => hne (Subtype.ext hh)
  have hfnt : f n≠eval ![f a,f b] torusWord := by
    rw [←ht]
    exact fun hh => hnt (Subtype.ext hh)
  have hfnt2 : f n≠(eval ![f a,f b] torusWord)^2 := by
    rw [←ht,←map_pow]
    exact fun hh => hnt2 (Subtype.ext hh)
  have hfc : Commute (f n) (eval ![f a,f b] torusWord) := by
    rw [←ht]
    exact hcomm.map f
  obtain ⟨ε,k,hpow,hfix⟩ := exists_cubic_variant (f a) (f b) (f n)
    hfa hfree hfb hfb2 hfab hfn hfn1 hfnt hfnt2 hfc
  let m := (if ε then n else n⁻¹)*(eval ![a,b] torusWord)^k.val
  let Y := m*a⁻¹*m⁻¹*b*m*a
  have hfY : f Y=
      ((if ε then f n else (f n)⁻¹)*(eval ![f a,f b] torusWord)^k.val)*(f a)⁻¹*
      (((if ε then f n else (f n)⁻¹)*(eval ![f a,f b] torusWord)^k.val))⁻¹*(f b)*
      ((if ε then f n else (f n)⁻¹)*(eval ![f a,f b] torusWord)^k.val)*(f a) := by
    simp only [Y,m,map_mul,map_inv,map_pow,apply_ite,ht]
  have hqY : (q Y)^3=1 := Subtype.ext (by change (f Y)^3=1; rw [hfY]; exact hpow)
  have hfreeY : ∀ v : NaturalModule, polarAction (q Y).val v=v → v=0 := by
    change ∀ v : NaturalModule, polarAction (f Y) v=v → v=0
    rw [hfY]
    exact hfix
  have hY : Y^3=1 := PolarAffine.power_eq_one_of_quotient_power_of_fixed_free q e he Y 3 hqY hfreeY
  refine ⟨ε,k,?_⟩
  change ∀ ell : G, eval ![a,b,ell,m]
    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25)=1
  intro ell
  simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
    Theory.SpecificGroups.MathieuAmalgamCompletion.decode,
    eval,FreeGroup.lift_mk,pow_succ,mul_assoc,Y] using hY

end Theory.SpecificGroups.SymmetricSix.HexadCubicWord
