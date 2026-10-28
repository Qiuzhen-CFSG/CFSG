module
public import Theory.GroupTheory.CyclicExtension
import Mathlib.Tactic.Group

/-!
# Comparing cubic-involution extensions through a common core

A core and two actors with cubic, involution, inversion, and specified core
conjugation relations have at most six core cosets.  Collecting a graph subgroup
therefore compares two generated extensions of the full possible order, with
both actors and every core element preserved.  This elementary presentation
lemma is used for the marked second endpoint in Aschbacher–Smith F.1.12/J.4.5.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CubicInvolutionExtension
variable {A G H : Type*} [Group A] [Group G] [Group H]

structure Relations (f:A→*G) (c b:G) (γ β:MulAut A) : Prop where
  cube : c^3=1
  square : b^2=1
  invert : b*c*b⁻¹=c⁻¹
  cubic (a:A) : f (γ a)=c*f a*c⁻¹
  involution (a:A) : f (β a)=b*f a*b⁻¹

def generated (f:A→*G) (c b:G) : Subgroup G :=
  closure (insert b (insert c (Set.range f)))

def normalForm (f:A→*G) (c b:G) (p:A×Fin 3×Fin 2) : G :=
  f p.1*c^p.2.1.val*b^p.2.2.val

theorem normalForm_mem (f:A→*G) (c b:G) (p:A×Fin 3×Fin 2) :
    normalForm f c b p∈generated f c b := by
  exact (generated f c b).mul_mem
    ((generated f c b).mul_mem (subset_closure (Or.inr (Or.inr ⟨p.1,rfl⟩)))
      ((generated f c b).pow_mem (subset_closure (Or.inr (Or.inl rfl))) _))
    ((generated f c b).pow_mem (subset_closure (Or.inl rfl)) _)

theorem normalForm_surjective [Finite G] (f:A→*G) (c b:G) (γ β:MulAut A)
    (h:Relations f c b γ β) {x:G} (hx:x∈generated f c b) :
    ∃p:A×Fin 3×Fin 2,normalForm f c b p=x := by
  let C:=closure (insert c (Set.range f))
  have hb:∀y∈insert c (Set.range f),b*y*b⁻¹∈C := by
    rintro y (rfl|⟨a,rfl⟩)
    · rw [h.invert]
      exact C.inv_mem (subset_closure (Or.inl rfl))
    · rw [←h.involution]
      exact subset_closure (Or.inr ⟨β a,rfl⟩)
  obtain ⟨y,hy,j,hj⟩:=exists_mul_pow_of_mem_closure_insert
    (insert c (Set.range f)) b 2 (by decide) h.square hb hx
  have hc:∀y∈Set.range f,c*y*c⁻¹∈closure (Set.range f) := by
    rintro y ⟨a,rfl⟩
    rw [←h.cubic]
    exact subset_closure ⟨γ a,rfl⟩
  obtain ⟨z,hz,i,hi⟩:=exists_mul_pow_of_mem_closure_insert
    (Set.range f) c 3 (by decide) h.cube hc hy
  change z∈closure (f.range:Set G) at hz
  rw [closure_eq] at hz
  obtain ⟨a,rfl⟩:=hz
  exact ⟨(a,i,j),by change f a*c^i.val*b^j.val=x; rw [hi,hj]⟩

theorem generated_card_le [Finite A] [Finite G]
    (f:A→*G) (c b:G) (γ β:MulAut A) (h:Relations f c b γ β) :
    Nat.card (generated f c b)≤Nat.card A*6 := by
  let F:A×Fin 3×Fin 2→generated f c b:=fun p=>⟨normalForm f c b p,normalForm_mem f c b p⟩
  have hs:Function.Surjective F := by
    intro x
    obtain ⟨p,hp⟩:=normalForm_surjective f c b γ β h x.property
    exact ⟨p,Subtype.ext hp⟩
  have hh:=Nat.card_le_card_of_surjective F hs
  simpa only [Nat.card_prod,Nat.card_fin] using hh

theorem Relations.prod {f:A→*G} {g:A→*H} {c b:G} {d t:H} {γ β:MulAut A}
    (hf:Relations f c b γ β) (hg:Relations g d t γ β) :
    Relations (f.prod g) (c,d) (b,t) γ β where
  cube:=Prod.ext hf.cube hg.cube
  square:=Prod.ext hf.square hg.square
  invert:=Prod.ext hf.invert hg.invert
  cubic a:=Prod.ext (hf.cubic a) (hg.cubic a)
  involution a:=Prod.ext (hf.involution a) (hg.involution a)

theorem exists_equiv [Finite A] [Finite G] [Finite H]
    (f:A→*G) (g:A→*H) (c b:G) (d t:H) (γ β:MulAut A)
    (hf:Relations f c b γ β) (hg:Relations g d t γ β)
    (gf:generated f c b=⊤) (gg:generated g d t=⊤)
    (hG:Nat.card G=Nat.card A*6) (hH:Nat.card H=Nat.card A*6) :
    ∃e:G≃*H,(∀a,e (f a)=g a)∧e c=d∧e b=t := by
  let K:=generated (f.prod g) (c,d) (b,t)
  let q₁:K→*G:=(MonoidHom.fst G H).comp K.subtype
  let q₂:K→*H:=(MonoidHom.snd G H).comp K.subtype
  have hq₁:Function.Surjective q₁ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [←gf]
    apply (closure_le _).mpr
    rintro z hz
    rcases hz with hz|hz|⟨a,ha⟩
    · subst z
      exact ⟨⟨(b,t),subset_closure (Or.inl rfl)⟩,rfl⟩
    · subst z
      exact ⟨⟨(c,d),subset_closure (Or.inr (Or.inl rfl))⟩,rfl⟩
    · subst z
      exact ⟨⟨(f a,g a),subset_closure (Or.inr (Or.inr ⟨a,rfl⟩))⟩,rfl⟩
  have hq₂:Function.Surjective q₂ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [←gg]
    apply (closure_le _).mpr
    rintro z hz
    rcases hz with hz|hz|⟨a,ha⟩
    · subst z
      exact ⟨⟨(b,t),subset_closure (Or.inl rfl)⟩,rfl⟩
    · subst z
      exact ⟨⟨(c,d),subset_closure (Or.inr (Or.inl rfl))⟩,rfl⟩
    · subst z
      exact ⟨⟨(f a,g a),subset_closure (Or.inr (Or.inr ⟨a,rfl⟩))⟩,rfl⟩
  have hcard:=generated_card_le (f.prod g) (c,d) (b,t) γ β (hf.prod hg)
  let e₁:K≃*G:=MulEquiv.ofBijective q₁ (hq₁.bijective_of_nat_card_le (by rwa [hG]))
  let e₂:K≃*H:=MulEquiv.ofBijective q₂ (hq₂.bijective_of_nat_card_le (by rwa [hH]))
  refine ⟨e₁.symm.trans e₂,?_,?_,?_⟩
  · intro a
    have he:e₁ ⟨(f a,g a),subset_closure (Or.inr (Or.inr ⟨a,rfl⟩))⟩=f a:=rfl
    change e₂ (e₁.symm (f a))=g a
    rw [←he,e₁.symm_apply_apply]
    rfl
  · have he:e₁ ⟨(c,d),subset_closure (Or.inr (Or.inl rfl))⟩=c:=rfl
    change e₂ (e₁.symm c)=d
    rw [←he,e₁.symm_apply_apply]
    rfl
  · have he:e₁ ⟨(b,t),subset_closure (Or.inl rfl)⟩=b:=rfl
    change e₂ (e₁.symm b)=t
    rw [←he,e₁.symm_apply_apply]
    rfl
end CubicInvolutionExtension
