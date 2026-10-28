module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# The weakly closed abelian sixteen in C₄ wr C₂

An element outside the base of C₄ wr C₂ has centralizer of order eight.
Thus every abelian subgroup of order sixteen equals the base. Transporting
this uniqueness proves that any ambient conjugate of such a subgroup that
remains inside its wreath overgroup is equal to the original subgroup.
The finite check is over the 32 elements and their centralizers, not over
subgroups. Source application: Aschbacher–Smith, before J.4.8, p.443.
-/

@[expose] public section
namespace CyclicFourWreathTwo
open Subgroup
abbrev C2 := Multiplicative (ZMod 2)
abbrev C4 := Multiplicative (ZMod 4)
abbrev W := RegularWreathProduct C4 C2
private instance : Fintype W := Fintype.ofEquiv ((C2 → C4) × C2)
  (RegularWreathProduct.equivProd C4 C2).symm
private instance : DecidableEq W := (RegularWreathProduct.equivProd C4 C2).injective.decidableEq

def base : Subgroup W := (RegularWreathProduct.rightHom : W →* C2).ker
private instance : DecidablePred (· ∈ base) := fun w => inferInstanceAs (Decidable (w.right=1))

theorem base_card : Nat.card base=16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem outside_centralizer_card (x:W) (hx:x.right≠1) :
    Nat.card (centralizer ({x}:Set W))=8 := by
  have h : ∀x:W,x.right≠1 → Fintype.card {y:W // y*x=x*y}=8 := by decide +kernel
  let e : centralizer ({x}:Set W) ≃ {y:W // y*x=x*y} :=
    Equiv.subtypeEquivRight (fun _ => mem_centralizer_singleton_iff)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  exact h x hx

theorem abelian_sixteen_eq_base (A:Subgroup W) (hA:Nat.card A=16)
    (hc:∀x∈A,∀y∈A,x*y=y*x) : A=base := by
  apply eq_of_le_of_card_ge _ (by rw [hA,base_card])
  intro x hx
  by_contra hn
  have hle : A≤centralizer ({x}:Set W) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (hc y hy x hx)
  have hh := Subgroup.card_le_of_le hle
  rw [hA,outside_centralizer_card x hn] at hh
  omega

theorem abelian_sixteen_unique {R:Type*} [Group R] [Finite R] (e:R≃*W)
    (A B:Subgroup R) (hA:Nat.card A=16) (hB:Nat.card B=16)
    (hcA:∀x∈A,∀y∈A,x*y=y*x) (hcB:∀x∈B,∀y∈B,x*y=y*x) : A=B := by
  have he (D:Subgroup R) (hd:Nat.card D=16) (hc:∀x∈D,∀y∈D,x*y=y*x) :
      D.map e.toMonoidHom=base := by
    apply abelian_sixteen_eq_base
    · rw [card_map_of_injective e.injective,hd]
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom,← map_mul] using congrArg e (hc x hx y hy)
  exact map_injective e.injective ((he A hA hcA).trans (he B hB hcB).symm)

/-- An ambient conjugate of the marked abelian sixteen which stays in its
wreath overgroup is the same subgroup. -/
theorem abelian_sixteen_weakly_closed {G:Type*} [Group G] [Finite G]
    (I R:Subgroup G) (hIR:I≤R) (eR:R≃*W) (hI:Nat.card I=16)
    (hcomm:∀x∈I,∀y∈I,x*y=y*x) (g:G) (hg:I.map (MulAut.conj g).toMonoidHom≤R) :
    I.map (MulAut.conj g).toMonoidHom=I := by
  let J := I.map (MulAut.conj g).toMonoidHom
  have hJ : Nat.card J=16 := (card_map_of_injective (MulAut.conj g).injective).trans hI
  have hcommJ : ∀x∈J,∀y∈J,x*y=y*x := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (map_mul (MulAut.conj g) x y).symm.trans
      ((congrArg (MulAut.conj g) (hcomm x hx y hy)).trans (map_mul (MulAut.conj g) y x))
  have hJI : J.subgroupOf R=I.subgroupOf R := abelian_sixteen_unique eR _ _
    ((Nat.card_congr (subgroupOfEquivOfLe hg).toEquiv).trans hJ)
    ((Nat.card_congr (subgroupOfEquivOfLe hIR).toEquiv).trans hI)
    (fun x hx y hy => Subtype.ext (hcommJ x hx y hy))
    (fun x hx y hy => Subtype.ext (hcomm x hx y hy))
  have hh := congrArg (fun D:Subgroup R => D.map R.subtype) hJI
  rwa [map_subgroupOf_eq_of_le hg,map_subgroupOf_eq_of_le hIR] at hh

end CyclicFourWreathTwo
