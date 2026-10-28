module

public import Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
public import Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Finite
public import Theory.SpecificGroups.MathieuAmalgamCompletion.Relators
import all Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
import all Theory.SpecificGroups.SymmetricSix.HexadSixDefects.Finite
import all Theory.SpecificGroups.MathieuAmalgamCompletion.Relators

/-!
# Exact identities among the six lifted hexad defects

The quotient criteria for words 17 and 19 select the same canonical cubic.
The split affine calculation then gives literal product identities between the
actual lifted words.  This file transports those identities through the exact
marked-pair conjugacy and the already proved affine normalization.
-/

public noncomputable section
open Equiv Subgroup Subgroup.CosetWordCertificate
open Matrix.PSL3Four.MathieuAmalgamMarking
namespace Theory.SpecificGroups.SymmetricSix.HexadSixDefects
open HexadCubicWord HexadAffineNineteen
open Theory.SpecificGroups.MathieuAmalgamCompletion
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- The six exterior-cubic words, with the unused middle letter set to one. -/
@[expose] public def hexadWord {G : Type*} [Group G] (a b n : G) (i : Fin 27) : G :=
  eval ![a,b,1,n] (relator i)

private def hexadConj {G : Type*} [Group G] (x y : G) : G := x*y*x⁻¹

/-- Exact equations expressing words 18, 20, 21, 22, and 24 through word 17. -/
public def Equations {G : Type*} [Group G] (a b n : G) : Prop :=
  let w := fun i : Fin 27 => hexadWord a b n i
  w 18 = hexadConj (a*b) (w 17) * hexadConj (b*a⁻¹) (w 17) ∧
  w 20 = hexadConj a (w 17) * hexadConj (n*a*n⁻¹) (w 17) ∧
  w 21 = w 17 * hexadConj (a*b*a*b) (w 17) ∧
  w 22 = w 17 * hexadConj (a*b*n⁻¹*a) (w 17) ∧
  w 24 = hexadConj a⁻¹ (w 17) * hexadConj (n⁻¹*a*b) (w 17)

public theorem hexadWord_eq {G : Type*} [Group G] (a b n : G) (i : Fin 27) :
    hexadWord a b n i=eval ![a,b,1,n] (relator i) := rfl

public theorem Equations_iff {G : Type*} [Group G] (a b n : G) :
    Equations a b n ↔
    let w := fun i : Fin 27 => hexadWord a b n i
    w 18 = (a*b)*w 17*(a*b)⁻¹ * ((b*a⁻¹)*w 17*(b*a⁻¹)⁻¹) ∧
    w 20 = a*w 17*a⁻¹ * ((n*a*n⁻¹)*w 17*(n*a*n⁻¹)⁻¹) ∧
    w 21 = w 17 * ((a*b*a*b)*w 17*(a*b*a*b)⁻¹) ∧
    w 22 = w 17 * ((a*b*n⁻¹*a)*w 17*(a*b*n⁻¹*a)⁻¹) ∧
    w 24 = a⁻¹*w 17*(a⁻¹)⁻¹ * ((n⁻¹*a*b)*w 17*(n⁻¹*a*b)⁻¹) := Iff.rfl

private theorem eval_hom {G H α : Type*} [Group G] [Group H]
    (f : G→*H) (p : α→G) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

private theorem hexadWord_map {G H : Type*} [Group G] [Group H]
    (f : G→*H) (a b n : G) (i : Fin 27) :
    f (hexadWord a b n i) = hexadWord (f a) (f b) (f n) i := by
  dsimp [hexadWord]
  rw [eval_hom]
  congr 1
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact map_one f
  · rfl

/-- Equations are preserved by every group homomorphism. -/
public theorem Equations.map {G H : Type*} [Group G] [Group H]
    (f : G→*H) {a b n : G} (h : Equations a b n) :
    Equations (f a) (f b) (f n) := by
  rcases h with ⟨h18,h20,h21,h22,h24⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [hexadConj,map_mul,map_inv,hexadWord_map] using congrArg f h18
  · simpa only [hexadConj,map_mul,map_inv,hexadWord_map] using congrArg f h20
  · simpa only [hexadConj,map_mul,map_inv,hexadWord_map] using congrArg f h21
  · simpa only [hexadConj,map_mul,map_inv,hexadWord_map] using congrArg f h22
  · simpa only [hexadConj,map_mul,map_inv,hexadWord_map] using congrArg f h24

private theorem Equations.of_injective {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Injective f) {a b n : G}
    (h : Equations (f a) (f b) (f n)) : Equations a b n := by
  unfold Equations at h ⊢
  rcases h with ⟨h18,h20,h21,h22,h24⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply hf
    simpa only [map_mul,map_inv,hexadConj,←hexadWord_map f] using h18
  · apply hf
    simpa only [map_mul,map_inv,hexadConj,←hexadWord_map f] using h20
  · apply hf
    simpa only [map_mul,map_inv,hexadConj,←hexadWord_map f] using h21
  · apply hf
    simpa only [map_mul,map_inv,hexadConj,←hexadWord_map f] using h22
  · apply hf
    simpa only [map_mul,map_inv,hexadConj,←hexadWord_map f] using h24

/-- The five equations are equivalent to simultaneous vanishing of all six words. -/
public theorem Equations.all_iff {G : Type*} [Group G] {a b n : G}
    (h : Equations a b n) :
    (∀ i : Fin 27,
      (i=17 ∨ i=18 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) → hexadWord a b n i=1) ↔
      hexadWord a b n 17=1 := by
  constructor
  · intro hall
    exact hall 17 (Or.inl rfl)
  · intro h17 i hi
    rcases h with ⟨h18,h20,h21,h22,h24⟩
    dsimp only at h18 h20 h21 h22 h24
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · exact h17
    · rw [h18]
      simp [hexadConj,h17]
    · rw [h20]
      simp [hexadConj,h17]
    · rw [h21]
      simp [hexadConj,h17]
    · rw [h22]
      simp [hexadConj,h17]
    · rw [h24]
      simp [hexadConj,h17]



private theorem fullEquations_of_raw (w : Fin 16) :
    Equations (interp (0,a0)) (interp (w,b0)) (interp (lin 3 11 10 13 w,c2)) := by
  let A := interp (0,a0)
  let B := interp (w,b0)
  let N := interp (lin 3 11 10 13 w,c2)
  have ht : (fun j => interp (canonical w j)) = ![A,B,1,N] := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact interp_one
    · rfl
  have he (i : Fin 27) : interp (defect w i)=hexadWord A B N i := by
    change interp (ev (canonical w) (relator i))=_
    rw [interp_ev,ht]
    rfl
  have hc (x y : Raw) : interp (conj x y)=hexadConj (interp x) (interp y) := by
    change interp (mul (mul x y) (inv x))=_
    rw [interp_mul,interp_mul,interp_inv]
    rfl
  have hab : interp (ab w)=A*B := by
    change interp (mul (canonical w 0) (canonical w 1))=_
    rw [interp_mul]
    rfl
  have hba : interp (baInv w)=B*A⁻¹ := by
    change interp (mul (canonical w 1) (inv (canonical w 0)))=_
    rw [interp_mul,interp_inv]
    rfl
  have hna : interp (nanInv w)=N*A*N⁻¹ := by
    change interp (mul (mul (canonical w 3) (canonical w 0)) (inv (canonical w 3)))=_
    rw [interp_mul,interp_mul,interp_inv]
    rfl
  have habab : interp (abab w)=A*B*A*B := by
    change interp (mul (mul (mul (canonical w 0) (canonical w 1)) (canonical w 0)) (canonical w 1))=_
    rw [interp_mul,interp_mul,interp_mul]
    rfl
  have habna : interp (abnInvA w)=A*B*N⁻¹*A := by
    change interp (mul (mul (mul (canonical w 0) (canonical w 1)) (inv (canonical w 3))) (canonical w 0))=_
    rw [interp_mul,interp_mul,interp_mul,interp_inv]
    rfl
  have hnab : interp (nInvAb w)=N⁻¹*A*B := by
    change interp (mul (mul (inv (canonical w 3)) (canonical w 0)) (canonical w 1))=_
    rw [interp_mul,interp_mul,interp_inv]
    rfl
  have hA : interp (canonical w 0)=A := rfl
  rcases equations w with ⟨h18,h20,h21,h22,h24⟩
  change Equations A B N
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [interp_mul,hc,he,hab,hba] using congrArg interp h18
  · simpa only [interp_mul,hc,he,hA,hna] using congrArg interp h20
  · simpa only [interp_mul,hc,he,habab] using congrArg interp h21
  · simpa only [interp_mul,hc,he,habna] using congrArg interp h22
  · simpa only [interp_mul,hc,he,interp_inv,hA,hnab] using congrArg interp h24

private theorem normalized_equations (a b n : Full)
    (ha : a=interp (0,a0)) (hb : b.right=b0)
    (hn3 : n.right^3=1)
    (hcomm : Commute n (eval ![a,b] torusWord))
    (hquot19 : (b.right*n.right*a.right⁻¹)^4=1)
    (hquot17 : eval ![a.right,b.right,1,n.right] (relator 17)=1) :
    Equations a b n := by
  have har : a.right=a0 := by rw [ha]; rfl
  have hT : (eval ![a,b] torusWord).right=eval ![a0,b0] torusWord := by
    change SemidirectProduct.rightHom (eval ![a,b] torusWord)=_
    rw [HexadAffineNineteen.eval_hom]
    congr 1
    funext i
    fin_cases i <;> simp [har,hb]
  have hqc : n.right * eval ![a0,b0] torusWord =
      eval ![a0,b0] torusWord * n.right := by
    have hh := congrArg SemidirectProduct.right hcomm.eq
    simpa only [SemidirectProduct.mul_right,hT] using hh
  have hq4 : (b0*n.right*a0⁻¹)^4=1 := by simpa only [har,hb] using hquot19
  have hq17 : eval ![a0,b0,1,n.right] (relator 17)=1 := by
    simpa only [har,hb] using hquot17
  have hncan : n.right=c2 := selected_c2 n.right (by simpa only [←map_pow] using hn3)
      hqc hq4 hq17
  obtain ⟨w,hw⟩ := decode_surjective b.left.toAdd
  have hA : interp (0,a0)=a := ha.symm
  have hB : interp (w,b0)=b := SemidirectProduct.ext
    (congrArg Multiplicative.ofAdd hw) hb.symm
  have hE : interp (ev ![(0,a0),(w,b0)] torusWord)=
      eval ![a,b] torusWord := by
    rw [interp_ev]
    congr 1
    funext i
    fin_cases i
    · exact hA
    · exact hB
  let N : Raw := (u2 0 w,c2)
  have hNc : Commute (interp N) (eval ![a,b] torusWord) := by
    have hh := congrArg interp (check2 w).1
    change interp N * eval ![a,b] torusWord = eval ![a,b] torusWord * interp N
    simpa only [interp_mul,hE] using hh
  have hN : interp N=n := centralizer_unique (eval ![a,b] torusWord)
      (interp N) n (by rw [hT]; exact torus_free) hncan.symm hNc hcomm
  have hNN : interp (lin 3 11 10 13 w,c2)=n := by
    have hu : u2 0 w=lin 3 11 10 13 w := by
      have hall : ∀ z : Fin 16, u2 0 z=lin 3 11 10 13 z := by decide +kernel
      exact hall w
    simpa only [N,hu] using hN
  simpa only [hA,hB,hNN] using fullEquations_of_raw w

private theorem canonical_equations (a b n : Full)
    (ha : a.right=a0) (hb : b.right=b0)
    (hn3 : n.right^3=1)
    (hcomm : Commute n (eval ![a,b] torusWord))
    (hquot19 : (b.right*n.right*a.right⁻¹)^4=1)
    (hquot17 : eval ![a.right,b.right,1,n.right] (relator 17)=1) :
    Equations a b n := by
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
    rw [HexadAffineNineteen.eval_hom]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hfc : Commute (f n) (eval ![f a,f b] torusWord) := by
    rw [←hTe]
    exact hcomm.map f.toMonoidHom
  have hf19 : ((f b).right*(f n).right*(f a).right⁻¹)^4=1 := by
    simpa only [hfr] using hquot19
  have hf17 : eval ![(f a).right,(f b).right,1,(f n).right] (relator 17)=1 := by
    simpa only [hfr] using hquot17
  have hh := normalized_equations (f a) (f b) (f n)
    hfa (by rw [hfr,hb]) (by rw [hfr]; exact hn3) hfc hf19 hf17
  exact Equations.of_injective f.toMonoidHom f.injective hh

/-- Exact six-word equations in the split polar affine model. -/
public theorem actual_equations (a b n : PolarAffine.Model)
    (ha : a.right^3=1)
    (hfree : ∀ v : NaturalModule, polarAction a.right.val v=v → v=0)
    (hb : b.right^2=1) (hab : (a.right*b.right)^5=1)
    (hn : n.right^3=1)
    (hcomm : Commute n (eval ![a,b] torusWord))
    (hquot19 : (b.right*n.right*a.right⁻¹)^4=1)
    (hquot17 : eval ![a.right.val,b.right.val,1,n.right.val] (relator 17)=1) :
    Equations a b n := by
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
    rw [hfr]
    have hv : n.right.val^3=1 := congrArg Subtype.val hn
    have hh := congrArg c.toMonoidHom hv
    change c (n.right.val^3)=c 1 at hh
    simpa only [map_pow,map_one] using hh
  have hf19 : ((f (embed b)).right*(f (embed n)).right*(f (embed a)).right⁻¹)^4=1 := by
    rw [hfr,hfr,hfr]
    have hv : (b.right.val*n.right.val*a.right.val⁻¹)^4=1 := congrArg Subtype.val hquot19
    have hh := congrArg c.toMonoidHom hv
    change c ((b.right.val*n.right.val*a.right.val⁻¹)^4)=c 1 at hh
    simpa only [map_pow,map_mul,map_inv,map_one] using hh
  have hf17 : eval ![(f (embed a)).right,(f (embed b)).right,1,(f (embed n)).right]
      (relator 17)=1 := by
    have hh := congrArg c.toMonoidHom hquot17
    rw [eval_hom,map_one] at hh
    have ht : (fun i => c.toMonoidHom (![a.right.val,b.right.val,1,n.right.val] i)) =
        ![c a.right.val,c b.right.val,1,c n.right.val] := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact map_one c
      · rfl
    rw [ht] at hh
    simpa only [hfr] using hh
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
  have hh := canonical_equations (f (embed a)) (f (embed b)) (f (embed n))
    hfa hfb hfn hfc hf19 hf17
  have hEmbed : Equations (embed a) (embed b) (embed n) := by
    exact Equations.of_injective f.toMonoidHom f.injective hh
  exact Equations.of_injective embed embed_injective hEmbed

end Theory.SpecificGroups.SymmetricSix.HexadSixDefects
