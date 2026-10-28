module
public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Mathlib.Tactic.Group
/-!
# Central norms for an involution interchanging commuting factors

If two commuting subgroups meet in order two, an involutory automorphism
interchanging them has no nonidentity norm in their intersection. Write a
norm as a product of one element from each factor. Centrality forces the
first factor into the intersection; interchange fixes that line and makes
the second factor equal to the first. The norm is therefore one.

The ambient coset corollary preserves the actual conjugation by a swapping
involution. It is the central-square lift calculation used in Aschbacher,
Sporadic Groups,45.3(5), printed p.243.
-/
@[expose] public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem swap_norm_eq_one_of_mem_intersection (B C : Subgroup G)
    (hicard : Nat.card (B⊓C : Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    (α : MulAut G) (ha : α^2=1)
    (hs : B.map α.toMonoidHom=C)
    (q:G) (hq:q∈B⊔C) (hn:α q*q∈B⊓C) : α q*q=1 := by
  have ha2 (x:G) : α (α x)=x := by
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using DFunLike.congr_fun ha x
  have hBC (b:G) (hb:b∈B) : α b∈C := hs ▸ mem_map_of_mem α.toMonoidHom hb
  have hCB (c:G) (hc:c∈C) : α c∈B := by
    rw [←hs] at hc
    obtain ⟨b,hb,rfl⟩ := hc
    change α (α b)∈B
    rwa [ha2]
  have hI (i:G) (hi:i∈B⊓C) : α i=i := by
    have hai : α i∈B⊓C := ⟨hCB i hi.2,hBC i hi.1⟩
    by_cases hi1:i=1
    · simp [hi1]
    obtain ⟨z,hzne,huniq⟩ := (Nat.card_eq_two_iff' (1:(B⊓C:Subgroup G))).mp hicard
    have hne : (⟨i,hi⟩:(B⊓C:Subgroup G))≠1 := fun he=>hi1 (congrArg Subtype.val he)
    have hane : (⟨α i,hai⟩:(B⊓C:Subgroup G))≠1 := by
      intro he
      exact hi1 (α.injective ((congrArg Subtype.val he).trans α.map_one.symm))
    exact congrArg Subtype.val ((huniq _ hane).trans (huniq _ hne).symm)
  have hp : q∈(B:Set G)*(C:Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right B C
      ((show B≤centralizer (C:Set G) from fun b hb c hc'=> (hc b hb c hc').symm).trans
        (centralizer_le_normalizer _))]
    exact hq
  obtain ⟨b,hb,c,hc',rfl⟩ := hp
  let l:=α c*b
  let r:=α b*c
  have hlB:l∈B := B.mul_mem (hCB c hc') hb
  have hrC:r∈C := C.mul_mem (hBC b hb) hc'
  have he:α (b*c)*(b*c)=l*r := by
    rw [map_mul]
    dsimp [l,r]
    calc
      α b*α c*(b*c) = α b*(α c*b)*c := by group
      _ = (α c*b)*α b*c := by rw [hc (α c*b) hlB (α b) (hBC b hb)]
      _ = _ := by group
  have hlI:l∈B⊓C := by
    refine ⟨hlB,?_⟩
    have hh:=C.mul_mem hn.2 (C.inv_mem hrC)
    rwa [he,mul_inv_cancel_right] at hh
  have hrl:r=l := by
    have hal:α l=l := hI l hlI
    have hall:c*α b=l := by simpa only [l,map_mul,ha2] using hal
    apply mul_left_cancel (a:=c)
    change c*(α b*c)=c*l
    rw [←mul_assoc,hall,hc l hlI.1 c hc']
  have hl2:l^2=1 := by
    have hh:=pow_card_eq_one' (x:=(⟨l,hlI⟩:(B⊓C:Subgroup G)))
    rw [hicard] at hh
    exact congrArg Subtype.val hh
  rw [he,hrl,←pow_two,hl2]

theorem square_eq_one_of_swap_coset (B C : Subgroup G)
    (hi : Nat.card (B⊓C : Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    (r:G) (hr:r^2=1) (hs:B.map (MulAut.conj r).toMonoidHom=C)
    (q:G) (hq:q∈B⊔C) (hn:(r*q)^2∈B⊓C) : (r*q)^2=1 := by
  have he:(r*q)^2=(MulAut.conj r) q*q := by
    have hrr:r*r=1 := by simpa only [pow_two] using hr
    have hri:r⁻¹=r := inv_eq_of_mul_eq_one_left hrr
    simp only [MulAut.conj_apply,hri,pow_two]
    group
  rw [he] at hn ⊢
  exact swap_norm_eq_one_of_mem_intersection B C hi hc (MulAut.conj r)
    (by rw [←map_pow,hr,map_one]) hs q hq hn
end Subgroup
