module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine
public import Theory.SpecificGroups.SymmetricSix.HexadCubicWord
import all Theory.SpecificGroups.SymmetricSix.HexadCubicWord
import all Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen.Finite

/-!
# Actual nineteenth hexad word in the split polar extension

The literal torus commutation forces the fourth-power translation to vanish.
The finite calculation is transported through the exact marked-pair conjugacy,
so the original pair and the same selected cubic are retained.
-/

public noncomputable section
open Equiv Subgroup Subgroup.CosetWordCertificate
open Matrix.PSL3Four.MathieuAmalgamMarking
namespace Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
open HexadCubicWord
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
private noncomputable abbrev fullAction :=
  MulDistribMulAction.toMulAut S6 (Multiplicative NaturalModule)
private abbrev Full := Multiplicative NaturalModule ⋊[fullAction] S6
private def interp (x : Raw) : Full := ⟨Multiplicative.ofAdd (decode x.1),x.2⟩
private theorem decode_injective : Function.Injective decode := by decide +kernel
private theorem interp_injective : Function.Injective interp := by
  intro x y h
  apply Prod.ext
  · exact decode_injective (congrArg (fun x : Full => x.left.toAdd) h)
  · exact congrArg SemidirectProduct.right h
private theorem interp_one : interp (0,1)=1 := by
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd decode_zero
  · rfl
private theorem interp_mul (x y : Raw) : interp (mul x y)=interp x*interp y := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change decode (plus x.1 (act x.2 y.1))=decode x.1+polarAction x.2 (decode y.1)
    rw [decode_plus,decode_act]
  · rfl
private theorem interp_inv (x : Raw) : interp (inv x)=(interp x)⁻¹ := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change decode (act x.2⁻¹ x.1)=polarAction x.2⁻¹ (-decode x.1)
    rw [decode_act,decode_neg]
  · rfl
private theorem interp_pw (x : Raw) (k : Nat) : interp (pw x k)=(interp x)^k := by
  induction k with
  | zero => exact interp_one
  | succ k ih => rw [pw,interp_mul,ih,pow_succ]
private theorem interp_ev {α : Type*} (p : α→Raw) (w : Word α) :
    interp (ev p w)=eval (fun i => interp (p i)) w := by
  have aux (w : Word α) (x : Raw) :
      interp (w.foldl (fun x a => mul x (if a.2 then p a.1 else inv (p a.1))) x)=
        interp x*eval (fun i => interp (p i)) w := by
    induction w generalizing x with
    | nil => simp
    | cons a w ih =>
      rcases a with ⟨i,b⟩
      simp only [List.foldl_cons,ih,interp_mul,eval_cons]
      cases b <;> simp [interp_inv,mul_assoc]
  simpa only [ev,interp_one,one_mul] using aux w (0,1)
private theorem eval_hom {G H α : Type*} [Group G] [Group H]
    (f : G→*H) (p : α→G) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp
private theorem centralizer_unique (t x y : Full)
    (ht : ∀ v : NaturalModule, polarAction t.right v=v → v=0)
    (hxy : x.right=y.right) (hxt : Commute x t) (hyt : Commute y t) : x=y := by
  apply SemidirectProduct.ext _ hxy
  apply Multiplicative.toAdd.injective
  apply sub_eq_zero.mp
  apply ht
  have hx : x.left.toAdd+polarAction x.right t.left.toAdd=
      t.left.toAdd+polarAction t.right x.left.toAdd := congrArg
    (fun z : Full => z.left.toAdd) hxt.eq
  have hy : y.left.toAdd+polarAction x.right t.left.toAdd=
      t.left.toAdd+polarAction t.right y.left.toAdd := by
    rw [hxy]
    exact congrArg (fun z : Full => z.left.toAdd) hyt.eq
  change polarLinearMap t.right (x.left.toAdd-y.left.toAdd)=x.left.toAdd-y.left.toAdd
  rw [map_sub]
  change polarAction t.right x.left.toAdd-polarAction t.right y.left.toAdd=_
  calc
    _ = (t.left.toAdd+polarAction t.right x.left.toAdd)-
        (t.left.toAdd+polarAction t.right y.left.toAdd) := by abel
    _ = (x.left.toAdd+polarAction x.right t.left.toAdd)-
        (y.left.toAdd+polarAction x.right t.left.toAdd) := by rw [←hx,←hy]
    _ = x.left.toAdd-y.left.toAdd := by abel
private theorem torus_free : ∀ v : NaturalModule,
    polarAction (eval ![a0,b0] torusWord) v=v → v=0 := by
  apply (HexadCubicWord.no_duad_iff _).mp
  decide +kernel
private theorem normalized (a b n : Full) (ha : a=interp (0,a0)) (hb : b.right=b0)
    (hn3 : n.right^3=1)
    (hcomm : Commute n (eval ![a,b] torusWord))
    (hquot : (b.right*n.right*a.right⁻¹)^4=1) : (b*n*a⁻¹)^4=1 := by
  have har : a.right=a0 := by rw [ha]; rfl
  have hT : (eval ![a,b] torusWord).right=eval ![a0,b0] torusWord := by
    change SemidirectProduct.rightHom (eval ![a,b] torusWord)=_
    rw [eval_hom]
    congr 1
    funext i
    fin_cases i <;> simp [har,hb]
  have hqc : n.right * eval ![a0,b0] torusWord=eval ![a0,b0] torusWord * n.right := by
    have hh := congrArg SemidirectProduct.right hcomm.eq
    simpa only [SemidirectProduct.mul_right,hT] using hh
  have hq4 : (b0*n.right*a0⁻¹)^4=1 := by simpa only [har,hb] using hquot
  obtain ⟨w,hw⟩ := decode_surjective b.left.toAdd
  have hA : interp (0,a0)=a := ha.symm
  have hB : interp (w,b0)=b := SemidirectProduct.ext
    (congrArg Multiplicative.ofAdd hw) hb.symm
  have hE : interp (ev ![(0,a0),(w,b0)] torusWord)=eval ![a,b] torusWord := by
    rw [interp_ev]
    congr 1
    funext i
    fin_cases i
    · exact hA
    · exact hB
  obtain ⟨N,hNr,hC,hF⟩ : ∃ N : Raw, N.2=n.right ∧
      mul N (ev ![(0,a0),(w,b0)] torusWord)=
        mul (ev ![(0,a0),(w,b0)] torusWord) N ∧
      pw (mul (mul (w,b0) N) (inv (0,a0))) 4=(0,1) := by
    rcases candidates n.right hn3 hqc hq4 with h1|h2|h3
    · exact ⟨(u1 0 w,c1),h1.symm,(check1 w).1,(check1 w).2⟩
    · exact ⟨(u2 0 w,c2),h2.symm,(check2 w).1,(check2 w).2⟩
    · exact ⟨(u3 0 w,c3),h3.symm,(check3 w).1,(check3 w).2⟩
  have hNc : Commute (interp N) (eval ![a,b] torusWord) := by
    have hh := congrArg interp hC
    change interp N * eval ![a,b] torusWord = eval ![a,b] torusWord * interp N
    simpa only [interp_mul,hE] using hh
  have hN : interp N=n := centralizer_unique (eval ![a,b] torusWord) (interp N) n
    (by rw [hT]; exact torus_free) hNr hNc hcomm
  have hh := congrArg interp hF
  simpa only [interp_pw,interp_mul,interp_inv,interp_one,hA,hB,hN] using hh

private theorem canonical (a b n : Full) (ha : a.right=a0) (hb : b.right=b0)
    (hn3 : n.right^3=1)
    (hcomm : Commute n (eval ![a,b] torusWord))
    (hquot : (b.right*n.right*a.right⁻¹)^4=1) : (b*n*a⁻¹)^4=1 := by
  obtain ⟨v,hv⟩ := decode_surjective a.left.toAdd
  have hA : interp (v,a0)=a := SemidirectProduct.ext
    (congrArg Multiplicative.ofAdd hv) ha.symm
  let f := MulAut.conj (interp (shift v))
  have hfr (x : Full) : (f x).right=x.right := by
    simp only [f,MulAut.conj_apply,SemidirectProduct.mul_right,
      SemidirectProduct.inv_right,interp,shift,inv_one,one_mul,mul_one]
  have hfa : f a=interp (0,a0) := by
    have hh := congrArg interp (normalize v)
    rw [interp_mul,interp_mul,interp_inv,hA] at hh
    exact hh
  have hTe : f (eval ![a,b] torusWord)=eval ![f a,f b] torusWord := by
    change f.toMonoidHom (eval ![a,b] torusWord)=_
    rw [eval_hom]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hfc : Commute (f n) (eval ![f a,f b] torusWord) := by
    rw [←hTe]
    exact hcomm.map f.toMonoidHom
  have hh := normalized (f a) (f b) (f n) hfa (by rw [hfr,hb])
    (by rw [hfr];exact hn3) hfc (by simp only [hfr];exact hquot)
  apply f.injective
  simpa only [map_pow,map_mul,map_inv,map_one] using hh

private noncomputable def embed : PolarAffine.Model→*Full where
  toFun x := ⟨x.left,x.right.val⟩
  map_one' := rfl
  map_mul' _ _ := rfl
private theorem embed_injective : Function.Injective embed := by
  intro x y h
  exact SemidirectProduct.ext (congrArg (fun z : Full => z.left) h)
    (Subtype.ext (congrArg (fun z : Full => z.right) h))

/-- In the literal split polar extension, the actual torus commutation kills
word 19's translation defect. The quotient is the caller's same marked pair
and cubic; no commutation of the unknown fourth-power defect is assumed. -/
public theorem word19 (a b n : PolarAffine.Model)
    (ha : a.right^3=1)
    (hfree : ∀ v : NaturalModule, polarAction a.right.val v=v → v=0)
    (hb : b.right^2=1) (hab : (a.right*b.right)^5=1)
    (hn : n.right^3=1)
    (hcomm : Commute n (eval ![a,b] torusWord))
    (hquot : (b.right*n.right*a.right⁻¹)^4=1) : (b*n*a⁻¹)^4=1 := by
  obtain ⟨g,hga,hgb⟩ := HexadCubicWord.pair_conjugate a.right.val b.right.val
    (congrArg Subtype.val ha) hfree b.right.property
    (congrArg Subtype.val hb) (congrArg Subtype.val hab)
  let f := MulAut.conj (SemidirectProduct.inr g⁻¹ : Full)
  let c := MulAut.conj g⁻¹
  have hfr (x : PolarAffine.Model) : (f (embed x)).right=c x.right.val := rfl
  have hfa : (f (embed a)).right=a0 := by
    rw [hfr]
    change g⁻¹*a.right.val*(g⁻¹)⁻¹=a0
    rw [←hga]
    simp [MulAut.conj_apply,mul_assoc]
  have hfb : (f (embed b)).right=b0 := by
    rw [hfr]
    change g⁻¹*b.right.val*(g⁻¹)⁻¹=b0
    rw [←hgb]
    simp [MulAut.conj_apply,mul_assoc]
  have hfn : (f (embed n)).right^3=1 := by
    rw [hfr,←map_pow]
    have hh : n.right.val^3=1 := congrArg Subtype.val hn
    rw [hh,map_one]
  have hfq : ((f (embed b)).right*(f (embed n)).right*(f (embed a)).right⁻¹)^4=1 := by
    simp only [hfr,←map_inv,←map_mul,←map_pow]
    have hh : (b.right.val*n.right.val*a.right.val⁻¹)^4=1 := congrArg Subtype.val hquot
    rw [hh,map_one]
  let F := f.toMonoidHom.comp embed
  have hFE : F (eval ![a,b] torusWord)=eval ![F a,F b] torusWord := by
    rw [eval_hom]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hfc : Commute (f (embed n)) (eval ![f (embed a),f (embed b)] torusWord) := by
    change Commute (F n) (eval ![F a,F b] torusWord)
    rw [←hFE]
    exact hcomm.map F
  have hh := canonical (f (embed a)) (f (embed b)) (f (embed n)) hfa hfb hfn hfc hfq
  apply embed_injective
  apply f.injective
  simpa only [map_pow,map_mul,map_inv,map_one] using hh
end Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
