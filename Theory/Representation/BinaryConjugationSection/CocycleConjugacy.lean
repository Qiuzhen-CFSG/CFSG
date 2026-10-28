module
public import Theory.Representation.BinaryConjugationSection.InvariantCount
import all Theory.Representation.BinaryConjugationSection.InvolutionCount

/-!
# Conjugacy descent through free binary sections

A fixed coordinate is a displacement for a free binary action. Conjugating
its twisted cocycle by a displacement lift sends it into the coordinate
kernel. In the ambient group this conjugates an involution coset into the
smaller kernel coset. A conjugacy-invariant two-element fiber with a moving
actor is a single orbit. These facts supply actual fusion, beyond cardinal
counts, in the corrected H-transitivity assertion of J.2.7(8).
-/

open Subgroup
namespace Representation.BinaryConjugationSection

public theorem cocycle_conjugate_into_kernel {A W:Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (s:MulAut A) (hs:∀a,s (s a)=a) (p:A→*Multiplicative W)
    (hp:Function.Surjective p) (f:W→ₗ[ZMod 2]W)
    (he:∀a,(p (s a)).toAdd=f (p a).toAdd)
    (hfree:∀v,f v=v→∃w,f w+w=v) (c:Cocycles s) :
    ∃a:A,p (cocycleConj s hs a c).val=1 := by
  let v:=cocycleMap s p f he c
  obtain ⟨w,hw⟩:=hfree v ((mem_fixed f v).mp v.property)
  obtain ⟨a,ha⟩:=hp (Multiplicative.ofAdd w)
  refine ⟨a,?_⟩
  have hshift:=cocycleMap_shift s hs p f he a c
  rw [ha] at hshift
  change (p (cocycleConj s hs a c).val).toAdd=(v:W)+(f w+w) at hshift
  rw [hw] at hshift
  change (p (cocycleConj s hs a c).val).toAdd=(v:W)+(v:W) at hshift
  change (p (cocycleConj s hs a c).val).toAdd=0
  exact hshift.trans (ZModModule.add_self (v:W))

variable {G:Type*} [Group G]
public theorem inverting_conjugate_into_kernel {A B:Subgroup G} {W:Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    (i:G) (hi:i^2=1) (hn:i∈normalizer A)
    (p:A→*Multiplicative W) (hp:Function.Surjective p)
    (hker:∀a:A,p a=1↔(a:G)∈B) (f:W→ₗ[ZMod 2]W)
    (he:∀a:A,(p (A.normalizerMonoidHom ⟨i,hn⟩ a)).toAdd=f (p a).toAdd)
    (hfree:∀v,f v=v→∃w,f w+w=v) (c:Inverting A i) :
    ∃a:A,∃b:Inverting B i,(a:G)*((c.val:G)*i)*(a:G)⁻¹=(b.val:G)*i := by
  let s:=A.normalizerMonoidHom ⟨i,hn⟩
  have hs (a:A):s (s a)=a := by
    apply Subtype.ext
    change i*(i*(a:G)*i⁻¹)*i⁻¹=(a:G)
    calc
      _=i^2*(a:G)*(i^2)⁻¹ := by simp only [pow_two];group
      _=_ := by rw [hi];simp
  let c':Cocycles s:=⟨c.val,Subtype.ext c.property⟩
  obtain ⟨a,ha⟩:=cocycle_conjugate_into_kernel s hs p hp f he hfree c'
  let b:Inverting B i:=⟨⟨(cocycleConj s hs a c').val,(hker _).mp ha⟩,
    congrArg Subtype.val (cocycleConj s hs a c').property⟩
  refine ⟨a,b,?_⟩
  change (a:G)*((c.val:G)*i)*(a:G)⁻¹=((a:G)*(c.val:G)*(i*(a:G)*i⁻¹)⁻¹)*i
  group

public theorem conjugacy_filter_of_card_two {G:Type*} [Group G] [Finite G]
    (A:Subgroup G) (i:G) (hi:i^2=1) (hn:i∈normalizer A)
    (P:G→Prop) (hPi:P i) (hP:∀a:A,∀x:G,P ((a:G)*x*(a:G)⁻¹)↔P x)
    (hc:Nat.card {a:Inverting A i//P ((a.val:G)*i)}=2)
    (hmove:∃a:A, i*(a:G)≠(a:G)*i) :
    ∀b:Inverting A i,P ((b.val:G)*i)→∃a:A,(a:G)*i*(a:G)⁻¹=(b.val:G)*i := by
  classical
  let s:=A.normalizerMonoidHom ⟨i,hn⟩
  have hs (a:A):s (s a)=a := by
    apply Subtype.ext
    change i*(i*(a:G)*i⁻¹)*i⁻¹=(a:G)
    calc
      _=i^2*(a:G)*(i^2)⁻¹ := by simp only [pow_two];group
      _=_ := by rw [hi];simp
  let X:={a:Inverting A i//P ((a.val:G)*i)}
  let z:X:=⟨⟨1,by simp⟩,by simpa using hPi⟩
  obtain ⟨a,ha⟩:=hmove
  let q:=cocycleConj s hs a ⟨1,by simp⟩
  have he : (q.val:G)*i=(a:G)*i*(a:G)⁻¹ := by
    change ((a:G)*1*(i*(a:G)*i⁻¹)⁻¹)*i=(a:G)*i*(a:G)⁻¹
    group
  let y:X:=⟨⟨q.val,congrArg Subtype.val q.property⟩,by
    rw [he];exact (hP a i).mpr hPi⟩
  have hy:y≠z := by
    intro hy
    have hh:=congrArg (fun x:X=>(x.val.val:G)*i) hy
    change (q.val:G)*i=(1:G)*i at hh
    rw [he,one_mul] at hh
    exact ha (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hall (x:X):x=z ∨ x=y := by
    by_contra! h
    let := Fintype.ofFinite X
    have hh:=Fintype.two_lt_card_iff.mpr ⟨x,z,y,h.1,h.2,hy.symm⟩
    rw [←Nat.card_eq_fintype_card,hc] at hh
    omega
  intro b hb
  rcases hall ⟨b,hb⟩ with h | h
  · refine ⟨1,?_⟩
    have hh:=congrArg (fun x:X=>(x.val.val:G)*i) h
    change (b.val:G)*i=1*i at hh
    change (1:G)*i*(1:G)⁻¹=(b.val:G)*i
    simpa only [one_mul,inv_one,mul_one] using hh.symm
  · refine ⟨a,?_⟩
    have hh:=congrArg (fun x:X=>(x.val.val:G)*i) h
    exact he.symm.trans hh.symm

end Representation.BinaryConjugationSection
