module

public import Theory.GroupTheory.SubgroupAutomorphismImages
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Detecting conjugate commutation from one point

If C_R(y)=C_R(A), then an involution x normalizing R and commuting with
y on its x-orbit forces A and Aˣ to commute. Conjugate y's centralizer
identity and use x²=1. The companion identities transport a point detector
through an automorphism of an embedded subgroup and ambient conjugation.
These are the group-word and marking steps in Campbell II.6.3, p.31.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem conjugates_commute_of_point_centralizer (R A : Subgroup G) (hAR : A ≤ R)
    (x y : G) (hx : x ∈ normalizer (R : Set G)) (hx2 : x^2=1) (hy : y ∈ R)
    (hC : R ⊓ centralizer ({y} : Set G) = R ⊓ centralizer (A : Set G))
    (hyy : ⁅y,x*y*x⁻¹⁆=1) : ⁅A,A.map (MulAut.conj x).toMonoidHom⁆=⊥ := by
  let c := MulAut.conj x
  have hcyR : c y ∈ R := (mem_normalizer_iff.mp hx y).mp hy
  have hcyC : c y ∈ centralizer (A : Set G) := by
    have hm : c y ∈ R ⊓ centralizer ({y} : Set G) :=
      ⟨hcyR,mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hyy).symm⟩
    exact (hC ▸ hm).2
  have hcc : c (c y)=y := by
    change x*(x*y*x⁻¹)*x⁻¹=y
    have hxx : x*x=1 := by simpa only [pow_two] using hx2
    calc
      x*(x*y*x⁻¹)*x⁻¹ = (x*x)*y*(x*x)⁻¹ := by group
      _ = y := by rw [hxx]; simp
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  rintro z ⟨a,ha,rfl⟩
  have hh : c a ∈ R ⊓ centralizer ({y} : Set G) := by
    refine ⟨(mem_normalizer_iff.mp hx a).mp (hAR ha),mem_centralizer_singleton_iff.mpr ?_⟩
    have he := congrArg c (hcyC a ha)
    simpa only [map_mul,hcc] using he
  exact (hC ▸ hh).2

theorem automorphism_point_centralizer (S A : Subgroup G) (a : MulAut S)
    (v : S) (hv : (v:G) ∈ A)
    (hC : S ⊓ centralizer ({(v:G)} : Set G) = S ⊓ centralizer (A : Set G)) :
    S ⊓ centralizer ({(a v:G)} : Set G) =
      S ⊓ centralizer (automorphismImage S a A : Set G) := by
  apply le_antisymm
  · intro x hx
    let xi := a.symm ⟨x,hx.1⟩
    have hxv : xi*v=v*xi := by
      apply a.injective
      apply Subtype.ext
      have hh := mem_centralizer_singleton_iff.mp hx.2
      simpa only [map_mul,xi,a.apply_symm_apply,Subgroup.coe_mul] using hh
    have hxiC : (xi:G) ∈ centralizer (A : Set G) := by
      have hh : (xi:G) ∈ S ⊓ centralizer ({(v:G)} : Set G) :=
        ⟨xi.property,mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxv)⟩
      exact (hC ▸ hh).2
    refine ⟨hx.1,?_⟩
    rintro z ⟨w,⟨t,ht,rfl⟩,rfl⟩
    have he : t*xi=xi*t := Subtype.ext (hxiC t ht)
    have hm := congrArg (fun s : S => (a s:G)) he
    change (a t:G)*x=x*(a t:G)
    simpa only [map_mul,xi,a.apply_symm_apply,Subgroup.coe_mul] using hm
  · apply inf_le_inf_left
    apply centralizer_le
    exact Set.singleton_subset_iff.mpr (mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom hv))

theorem point_centralizer_conjugate (R A : Subgroup G) (g y : G)
    (hg : g ∈ normalizer (R : Set G)) (hy : y ∈ A)
    (hC : R ⊓ centralizer ({y} : Set G) = R ⊓ centralizer (A : Set G)) :
    R ⊓ centralizer ({g*y*g⁻¹} : Set G) =
      R ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) := by
  let c := MulAut.conj g
  apply le_antisymm
  · intro x hx
    have hxiR : c.symm x ∈ R := by
      have hh := (mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem hg) x).mp hx.1
      change g⁻¹*x*g ∈ R
      simpa only [inv_inv] using hh
    have hxiC : c.symm x ∈ centralizer (A : Set G) := by
      have hh : c.symm x ∈ R ⊓ centralizer ({y} : Set G) := by
        refine ⟨hxiR,mem_centralizer_singleton_iff.mpr ?_⟩
        have he : x*c y=c y*x := mem_centralizer_singleton_iff.mp hx.2
        have he' := congrArg c.symm he
        simpa only [map_mul,c.symm_apply_apply] using he'
      exact (hC ▸ hh).2
    refine ⟨hx.1,?_⟩
    rintro z ⟨t,ht,rfl⟩
    have hh := congrArg c (hxiC t ht)
    change c t*x=x*c t
    simpa only [map_mul,c.apply_symm_apply] using hh
  · apply inf_le_inf_left
    apply centralizer_le
    exact Set.singleton_subset_iff.mpr (mem_map_of_mem (MulAut.conj g).toMonoidHom hy)

end Subgroup
