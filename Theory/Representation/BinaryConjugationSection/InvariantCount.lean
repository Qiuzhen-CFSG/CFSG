module
public import Theory.Representation.BinaryConjugationSection.InvolutionCount
import all Theory.Representation.BinaryConjugationSection.InvolutionCount

/-!
# Counting a conjugacy-invariant part of a free binary section

The usual cocycle count remains valid after restricting to any predicate
preserved by conjugation. The same cocycle conjugation transports the zero
coordinate fiber to every fixed-vector fiber and preserves the predicate.
The ambient form counts inverted elements a subject to a condition on a*i.
This keeps a specified ambient conjugacy class throughout repeated section
counts, as required for the z-class count in J.2.7(8).
-/

open Subgroup
namespace Representation.BinaryConjugationSection
noncomputable section

public theorem card_cocycles_filter {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : MulAut A) (hs : ∀ a,s (s a)=a)
    (p : A→*Multiplicative W) (hp : Function.Surjective p)
    (f : W→ₗ[ZMod 2]W) (he : ∀a,(p (s a)).toAdd=f (p a).toAdd)
    (hfree : ∀v,f v=v→∃w,f w+w=v)
    (P : Cocycles s→Prop)
    (hP : ∀a c,P (cocycleConj s hs a c)↔P c) :
    Nat.card {c:Cocycles s//P c}=Nat.card (Fixed f)*Nat.card {c:{c:Cocycles s//P c}//p c.val.val=1} := by
  let F := fun c:{c:Cocycles s//P c} => cocycleMap s p f he c.val
  apply card_of_fibers F
  intro v
  obtain ⟨w,hw⟩ := hfree v ((mem_fixed f v).mp v.property)
  obtain ⟨a,ha⟩ := hp (Multiplicative.ofAdd w)
  let E : {c:Cocycles s//P c}≃{c:Cocycles s//P c} :=
    Equiv.subtypeEquiv (cocycleConj s hs a) (fun c => (hP a c).symm)
  have hshift (c:{c:Cocycles s//P c}) : (F (E c):W)=(F c:W)+v := by
    change (cocycleMap s p f he (cocycleConj s hs a c.val):W)=_
    rw [cocycleMap_shift,ha]
    exact congrArg ((F c:W)+·) hw
  apply Nat.card_congr
  symm
  refine Equiv.subtypeEquiv E ?_
  intro c
  rw [Subtype.ext_iff,hshift]
  change p c.val.val=1 ↔ (p c.val.val).toAdd+(v:W)=v
  rw [add_eq_right]
  rfl

variable {G : Type*} [Group G]
public theorem card_inverting_section_filter [Finite G] {H A B:Subgroup G} {W:Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ:Representation (ZMod 2) H W}
    (d:BinaryConjugationSection H A B ρ) (i:H) (hi:(i:G)^2=1)
    (hfree:∀v,ρ i v=v→∃w,ρ i w+w=v)
    (P:G→Prop) (hP:∀a:A,∀x:G,P ((a:G)*x*(a:G)⁻¹)↔P x) :
    Nat.card {a:Inverting A (i:G)//P ((a.val:G)*i)}=
      Nat.card (Fixed (ρ i))*Nat.card {b:Inverting B (i:G)//P ((b.val:G)*i)} := by
  let s:=sectionAut d i
  have hs:=sectionAut_sq d i hi
  have he (a:A) : (d.coordinates (s a)).toAdd=ρ i (d.coordinates a).toAdd:=d.equivariant i a
  let Q := fun a:Cocycles s => P ((a.val:G)*i)
  have hQ (a:A) (x:Cocycles s) : Q (cocycleConj s hs a x)↔Q x := by
    change P (((a:G)*x*((i:G)*(a:G)*(i:G)⁻¹)⁻¹)*(i:G))↔P ((x.val:G)*i)
    have hh : ((a:G)*x*((i:G)*(a:G)*(i:G)⁻¹)⁻¹)*(i:G)=(a:G)*((x.val:G)*i)*(a:G)⁻¹ := by group
    rw [hh]
    exact hP a _
  let e : Cocycles s≃Inverting A (i:G) :=
    Equiv.subtypeEquiv (Equiv.refl A) (fun a => by
      change (s a=a⁻¹)↔_
      rw [Subtype.ext_iff]
      rfl)
  let eQ : {a:Cocycles s//Q a}≃{a:Inverting A (i:G)//P ((a.val:G)*i)} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  let eB : {a:{a:Cocycles s//Q a}//d.coordinates a.val.val=1}≃
      {b:Inverting B (i:G)//P ((b.val:G)*i)} := {
    toFun a := ⟨⟨⟨a.val.val.val,(d.coordinates_eq_one_iff _).mp a.property⟩,
      congrArg Subtype.val a.val.val.property⟩,a.val.property⟩
    invFun b := ⟨⟨⟨⟨b.val.val,d.kernel_le b.val.val.property⟩,Subtype.ext b.val.property⟩,
      b.property⟩,(d.coordinates_eq_one_iff _).mpr b.val.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [←Nat.card_congr eQ,card_cocycles_filter s hs d.coordinates d.onto (ρ i) he hfree Q hQ,
    Nat.card_congr eB]

/-- A single normalizing involution suffices for the filtered section count. -/
public theorem card_inverting_hom_filter [Finite G] {A B:Subgroup G} {W:Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (i:G) (hi:i^2=1) (hn:i∈normalizer A) (hBA:B≤A)
    (p:A→*Multiplicative W) (hp:Function.Surjective p)
    (hker:∀a:A,p a=1↔(a:G)∈B)
    (f:W→ₗ[ZMod 2]W)
    (he:∀a:A,(p (A.normalizerMonoidHom ⟨i,hn⟩ a)).toAdd=f (p a).toAdd)
    (hfree:∀v,f v=v→∃w,f w+w=v)
    (P:G→Prop) (hP:∀a:A,∀x:G,P ((a:G)*x*(a:G)⁻¹)↔P x) :
    Nat.card {a:Inverting A i//P ((a.val:G)*i)}=
      Nat.card (Fixed f)*Nat.card {b:Inverting B i//P ((b.val:G)*i)} := by
  let s:=A.normalizerMonoidHom ⟨i,hn⟩
  have hs (a:A) : s (s a)=a := by
    apply Subtype.ext
    change i*(i*(a:G)*i⁻¹)*i⁻¹=(a:G)
    calc
      _=i^2*(a:G)*(i^2)⁻¹ := by simp only [pow_two];group
      _=_ := by rw [hi];simp
  let Q := fun a:Cocycles s => P ((a.val:G)*i)
  have hQ (a:A) (x:Cocycles s) : Q (cocycleConj s hs a x)↔Q x := by
    change P (((a:G)*x*((i:G)*(a:G)*(i:G)⁻¹)⁻¹)*(i:G))↔P ((x.val:G)*i)
    have hh : ((a:G)*x*((i:G)*(a:G)*(i:G)⁻¹)⁻¹)*(i:G)=(a:G)*((x.val:G)*i)*(a:G)⁻¹ := by group
    rw [hh]
    exact hP a _
  let e : Cocycles s≃Inverting A (i:G) :=
    Equiv.subtypeEquiv (Equiv.refl A) (fun a => by
      change (s a=a⁻¹)↔_
      rw [Subtype.ext_iff]
      rfl)
  let eQ : {a:Cocycles s//Q a}≃{a:Inverting A (i:G)//P ((a.val:G)*i)} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  let eB : {a:{a:Cocycles s//Q a}//p a.val.val=1}≃
      {b:Inverting B (i:G)//P ((b.val:G)*i)} := {
    toFun a := ⟨⟨⟨a.val.val.val,(hker _).mp a.property⟩,
      congrArg Subtype.val a.val.val.property⟩,a.val.property⟩
    invFun b := ⟨⟨⟨⟨b.val.val,hBA b.val.val.property⟩,Subtype.ext b.val.property⟩,
      b.property⟩,(hker _).mpr b.val.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [←Nat.card_congr eQ,card_cocycles_filter s hs p hp f he hfree Q hQ,
    Nat.card_congr eB]


end
end Representation.BinaryConjugationSection
