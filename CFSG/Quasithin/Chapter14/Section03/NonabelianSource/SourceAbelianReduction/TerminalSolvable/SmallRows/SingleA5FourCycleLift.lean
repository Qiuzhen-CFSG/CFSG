module
public import Theory.GroupTheory.MinusExtraspecialFourCycle.Model
public import Theory.GroupTheory.MinusExtraspecialA5Fusion
import all Theory.GroupTheory.MinusExtraspecialA5Fusion
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.NormalCenterQuotient
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.SourceReflection.ModelNorm

/-!
# Order-four roots in the symmetric-five local extension

Correct a lift of a four-cycle so that its fourth power lies in the
extraspecial center. The existing even outside involution and the proved
central-norm obstruction then force that fourth power to be one. The square
is outside the core and belongs to the specified two-perfect subgroup of
index at most two. No splitting or centralizer isomorphism is assumed.

The normal-core calculation is reusable. This extension sits at the source
layer because its central-norm input is currently proved in the J₂ source
development; the new finite model certificate remains in Theory.
The internal import reuses the literal five-point action and kernel.
Source: Aschbacher–Smith 14.2.17(1), printed p.987; the even central-norm
input is Aschbacher, Sporadic Groups (1994), 46.8 and 46.11, pp.253–255.
-/

open Subgroup
namespace MinusExtraspecial
open FixedFourCalculation.Outside
open FixedFourCalculation.FourCycle
variable {H : Type*} [Group H]

private theorem central_square_one_of_even_involution
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q)
    (hf : Function.Surjective (pointAction Q e))
    (u : H) (hu : orderOf u=2) (huQ : u ∉ Q)
    (huEven : Equiv.Perm.sign (pointAction Q e u)=1)
    (x : H) (hx2 : pointAction Q e x ^ 2=1) (hxne : pointAction Q e x ≠ 1)
    (hxEven : Equiv.Perm.sign (pointAction Q e x)=1)
    (hxZ : x^2 ∈ center H) : x^2=1 := by
  let f := pointAction Q e
  let up : alternatingGroup (Fin 5) := ⟨f u,huEven⟩
  let xp : alternatingGroup (Fin 5) := ⟨f x,hxEven⟩
  have hu2 : u^2=1 := hu ▸ pow_orderOf_eq_one u
  have hup : orderOf up=2 := orderOf_eq_prime
    (Subtype.ext (by change f u ^2=1; rw [←map_pow,hu2,map_one]))
    (fun hh => huQ (by rw [←pointAction_kernel Q e hc]; exact congrArg Subtype.val hh))
  have hxp : orderOf xp=2 := orderOf_eq_prime (Subtype.ext hx2)
    (fun hh => hxne (congrArg Subtype.val hh))
  obtain ⟨c,hcux⟩ := isConj_iff.mp (alternatingGroup.five_involutions_isConj up xp hup hxp)
  obtain ⟨g,hg⟩ := hf c
  let w := g*u*g⁻¹
  have hw2 : w^2=1 := by
    change (MulAut.conj g u)^2=1
    rw [←map_pow,hu2,map_one]
  have hwf : f w=f x := by
    change f (g*u*g⁻¹)=f x
    have hcg : f g=(c:Equiv.Perm (Fin 5)) := hg
    rw [map_mul,map_mul,map_inv,hcg]
    exact congrArg Subtype.val hcux
  have hdmem : w*x⁻¹ ∈ Q := by
    rw [←pointAction_kernel Q e hc,MonoidHom.mem_ker,map_mul,map_inv,hwf,mul_inv_cancel]
  let d : Q := ⟨w*x⁻¹,hdmem⟩
  let a := modelAction Q e x
  have ha : a^2=1 := by
    have hcq : (MulAut.conjNormal (x^2) : MulAut Q)=1 := by
      ext q
      change x^2*(q:H)*(x^2)⁻¹=(q:H)
      rw [←Subgroup.mem_center_iff.mp hxZ q]
      group
    rw [←map_pow]
    change MulAut.congr e (MulAut.conjNormal (x^2))=1
    rw [hcq,map_one]
  have hn : ((d*MulAut.conjNormal x d:Q):H)=(x^2)⁻¹ := by
    change (w*x⁻¹)*(x*(w*x⁻¹)*x⁻¹)=(x^2)⁻¹
    calc
      _ = w^2*(x^2)⁻¹ := by simp only [pow_two]; group
      _ = _ := by rw [hw2,one_mul]
  have hnZ : d*MulAut.conjNormal x d ∈ center Q := by
    apply Subgroup.mem_center_iff.mpr
    intro q
    apply Subtype.ext
    change (q:H)*((d*MulAut.conjNormal x d:Q):H)=((d*MulAut.conjNormal x d:Q):H)*(q:H)
    rw [hn]
    exact Subgroup.mem_center_iff.mp (inv_mem hxZ) q
  have he : e d*a (e d)=e (d*MulAut.conjNormal x d) := by
    change e d*e (MulAut.conjNormal x (e.symm (e d)))=_
    rw [e.symm_apply_apply,map_mul]
  have hnZ' : e d*a (e d) ∈ center Model := by
    rw [he]
    apply Subgroup.mem_center_iff.mpr
    intro q
    obtain ⟨q,rfl⟩ := e.surjective q
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hnZ q)
  have hh := FixedFourCalculation.Reflection.central_norm_eq_one a ha hxEven hxne (e d) hnZ'
  rw [he,e.map_eq_one_iff] at hh
  have hh' := congrArg Subtype.val hh
  rw [hn] at hh'
  exact inv_eq_one.mp hh'

/-- An existing even outside involution forces an actual order-four lift
of a four-cycle in the full symmetric-five quotient. -/
private theorem exists_four_cycle_lift [Finite H]
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (hq : Nat.card (H ⧸ Q)=120)
    (u : H) (hu : orderOf u=2) (huQ : u ∉ Q)
    (huEven : Equiv.Perm.sign (pointAction Q e u)=1) :
    ∃ r : H, orderOf r=4 ∧ r^2 ∉ Q := by
  let f := pointAction Q e
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply eq_top_of_card_eq
    rw [←index_ker,pointAction_kernel Q e hc]
    change Nat.card (H ⧸ Q)=Nat.card (Equiv.Perm (Fin 5))
    rw [hq,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  obtain ⟨t,ht⟩ := hf cycle
  have ht4 : t^4 ∈ Q := by
    rw [←pointAction_kernel Q e hc,MonoidHom.mem_ker,map_pow,ht]
    exact cycle_fourth
  let a := modelAction Q e t
  let d : Q := ⟨t^4,ht4⟩
  have hd : a (e d)=e d := by
    change e (MulAut.conjNormal t (e.symm (e d)))=e d
    rw [e.symm_apply_apply]
    congr 1
    apply Subtype.ext
    change t*t^4*t⁻¹=t^4
    group
  have ha : a^4=MulAut.conj (e d) := by
    rw [←map_pow]
    apply MulEquiv.ext
    intro x
    change e (MulAut.conjNormal (t^4) (e.symm x))=e d*x*(e d)⁻¹
    rw [←e.apply_symm_apply x,←map_inv,←map_mul,←map_mul]
    congr 1
    simp only [e.symm_apply_apply]
    rfl
  obtain ⟨q,hqZ⟩ := exists_central_fourth_norm a ht (e d) hd ha
  let qQ := e.symm q
  let n : Q := qQ*MulAut.conjNormal t qQ*MulAut.conjNormal t (MulAut.conjNormal t qQ)*
    MulAut.conjNormal t (MulAut.conjNormal t (MulAut.conjNormal t qQ))*d
  have hn : e n=q*a q*a (a q)*a (a (a q))*e d := by
    simp only [n,map_mul,a,modelAction,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply,MulEquiv.trans_apply,qQ,e.apply_symm_apply,e.symm_apply_apply]
  have hnZ : n ∈ center Q := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul,hn] using Subgroup.mem_center_iff.mp hqZ (e y)
  have hcentral : (center Q).map Q.subtype ≤ center H := by
    let : ((center Q).map Q.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    apply central_of_normal_card_two
    rw [card_map_of_injective Q.subtype_injective,
      Nat.card_congr (centerCongr e).toEquiv,MinusExtraspecial.card_center]
  let r : H := (qQ:H)*t
  have hr4 : r^4=(n:H) := by
    change ((qQ:H)*t)^4=(qQ:H)*(t*(qQ:H)*t⁻¹)*
      (t*(t*(qQ:H)*t⁻¹)*t⁻¹)*(t*(t*(t*(qQ:H)*t⁻¹)*t⁻¹)*t⁻¹)*t^4
    simp only [show (4:Nat)=2*2 from rfl,pow_mul,pow_two]
    group
  have hrZ : r^4 ∈ center H := hr4 ▸ hcentral (mem_map_of_mem Q.subtype hnZ)
  have hrmap : f r=cycle := by
    change f ((qQ:H)*t)=cycle
    rw [map_mul,show f (qQ:H)=1 from
      (show (qQ:H)∈f.ker from (pointAction_kernel Q e hc).symm ▸ qQ.property),one_mul,ht]
  have hr4one : r^4=1 := by
    have hh := central_square_one_of_even_involution Q e hc hf u hu huQ huEven
      (r^2) (by rw [map_pow,hrmap,←pow_mul]; exact cycle_fourth)
      (by rw [map_pow,hrmap]; exact cycle_square_ne)
      (by rw [map_pow,hrmap]; exact cycle_square_even)
      (by simpa only [←pow_mul] using hrZ)
    simpa only [←pow_mul] using hh
  have hr2Q : r^2 ∉ Q := by
    intro hh
    have he : f (r^2)=1 :=
      (show r^2 ∈ f.ker from (pointAction_kernel Q e hc).symm ▸ hh)
    rw [map_pow,hrmap] at he
    exact cycle_square_ne he
  refine ⟨r,?_,hr2Q⟩
  apply @orderOf_eq_prime_pow H _ _ 1 2 ⟨Nat.prime_two⟩
  · change r^2 ≠ 1
    exact fun hh => hr2Q (hh.symm ▸ Q.one_mem)
  · exact hr4one
/-- In the symmetric-five extension, a two-perfect subgroup of index at
most two containing an outside involution contains the square of an
order-four element outside the core. -/
public theorem exists_outside_square [Finite H]
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (hq : Nat.card (H ⧸ Q)=120)
    (K : Subgroup H) (hK : IsPPerfect 2 K) (hi : K.index=1 ∨ K.index=2)
    (u : K) (hu : orderOf u=2) (huQ : (u:H) ∉ Q) :
    ∃ r : H, orderOf r=4 ∧ r^2 ∈ K ∧ r^2 ∉ Q := by
  let f := pointAction Q e
  have heven : Equiv.Perm.sign (f (u:H))=1 := by
    let s := Equiv.Perm.sign.comp (f.comp K.subtype)
    have h2 : IsPGroup 2 ℤˣ := IsPGroup.of_card (n:=1) (by
      rw [Nat.card_eq_fintype_card,Fintype.card_units_int]; rfl)
    exact DFunLike.congr_fun (hK.hom_eq_one_of_isPGroup h2 s) u
  obtain ⟨r,hr,hrQ⟩ := exists_four_cycle_lift Q e hc hq u
    ((orderOf_coe u).trans hu) huQ heven
  refine ⟨r,hr,?_,hrQ⟩
  rcases hi with hi | hi
  · rw [index_eq_one.mp hi]; exact mem_top _
  · exact sq_mem_of_index_two hi r
end MinusExtraspecial
