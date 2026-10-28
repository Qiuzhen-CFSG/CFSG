module
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Abel

/-!
# Splitting the moved plane of a binary involution

A two-dimensional Jordan block of a binary involution is an invariant
summand. Choose a linear functional taking the displacement to one, adjust
it to vanish on the starting vector, and use these two coefficient maps
to build an equivariant retraction. Its kernel is the invariant complement.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19(9), printed p.997.
-/

open Module Submodule LinearMap

public theorem LinearEquiv.exists_invariant_complement_of_binary_moved_plane
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (a : E ≃ₗ[ZMod 2] E) (ha : a * a = 1) (v : E) (hm : a v ≠ v) :
    ∃ C : Submodule (ZMod 2) E,
      IsCompl (Submodule.span (ZMod 2) ({v,a v} : Set E)) C ∧
      ∀ x ∈ C, a x ∈ C := by
  have htwo (x:E) : x+x=0 := by
    calc
      x+x=(2:ZMod 2) • x := (two_smul (ZMod 2) x).symm
      _=0 := by rw [show (2:ZMod 2)=0 by decide,zero_smul]
  have haa (x : E) : a (a x)=x := congrArg (fun b:E≃ₗ[ZMod 2] E=>b x) ha
  let d : E →ₗ[ZMod 2] E := a.toLinearMap + LinearMap.id
  have hd (x:E) : d x=a x+x := rfl
  have hdd (x:E) : d (d x)=0 := by
    simp only [hd,map_add,haa]
    calc
      x+a x+(a x+x)=(x+x)+(a x+a x) := by abel
      _=0 := by rw [htwo,htwo,zero_add]
  let z:=d v
  have hz:z≠0 := by
    intro h
    apply hm
    have hh:=congrArg (fun x:E=>x+v) h
    simpa only [z,hd,zero_add,add_assoc,htwo,add_zero] using hh
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz
  let f : Module.Dual (ZMod 2) E := l + l v • l.comp d
  have fz:f z=1 := by simp [f,z,hdd,hl]
  have fv:f v=0 := by
    change l v + l v*l (d v)=0
    rw [show l (d v)=1 from hl,mul_one,CharTwo.add_self_eq_zero]
  have fdd (x:E) : f (d (d x))=0 := by rw [hdd,map_zero]
  let P:=Submodule.span (ZMod 2) ({v,a v}:Set E)
  have hvP:v∈P := Submodule.subset_span (by simp)
  have haP:a v∈P := Submodule.subset_span (by simp)
  have hzP:z∈P := P.add_mem haP hvP
  let p : E →ₗ[ZMod 2] P := (f.comp d).smulRight ⟨v,hvP⟩ + f.smulRight ⟨z,hzP⟩
  have hp (x:E) : (p x:E)= f (d x) • v + f x • z := rfl
  have hpv : (p v:E)=v := by rw [hp,show d v=z from rfl,fz,fv,one_smul,zero_smul,add_zero]
  have hpz : (p z:E)=z := by rw [hp,show d z=0 from hdd v,map_zero,fz,zero_smul,one_smul,zero_add]
  have hav : a v=z+v := by rw [show z=a v+v from rfl,add_assoc,htwo,add_zero]
  have hpav : (p (a v):E)=a v := by rw [hav,map_add]; exact congrArg₂ (·+·) hpz hpv
  have hproj (x:P) : p x=x := by
    apply Subtype.ext
    obtain ⟨r,s,hx⟩ := Submodule.mem_span_pair.mp x.property
    rw [←hx,map_add,p.map_smul,p.map_smul]
    change r • (p v:E) + s • (p (a v):E)=_
    rw [hpv,hpav]
  refine ⟨p.ker,LinearMap.isCompl_of_proj hproj,?_⟩
  intro x hx
  have hx':(p x:E)=0 := congrArg Subtype.val hx
  change p (a x)=0
  apply Subtype.ext
  have hdx : a x=d x+x := by rw [hd,add_assoc,htwo,add_zero]
  have haxz:a z=z := by simp only [z,hd,map_add,haa];rw [add_comm]
  have he:(p (a x):E)=a (p x:E) := by
    rw [hp,hdx,map_add,map_add,hdd,map_zero,zero_add]
    rw [hp]
    simp only [map_add,LinearEquiv.map_smul,hav,haxz,smul_add,add_smul]
    abel
  rw [he,hx',map_zero]
  rfl

