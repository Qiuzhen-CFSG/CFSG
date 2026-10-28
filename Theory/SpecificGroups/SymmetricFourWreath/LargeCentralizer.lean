module
public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Theory.GroupTheory.NormalSubgroupTwoClassCover
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Large involution centralizers in the dihedral wreath group

In `D₈ wr C₂`, an involution outside the center and the class of a
single-factor central involution has at least four conjugates. A certificate
uses sixteen explicit rotation-and-swap conjugators; the class equation then
bounds its centralizer by 32. Consequently any marked involution with
centralizer order 64 represents the unique noncentral class with a larger
centralizer.

This is the minimal local table used in the exceptional enlargement argument
of Aschbacher--Smith F.4.37, printed p.293. The certificate enumerates only
128 possible elements and sixteen fixed conjugators, not the full pairwise
centralizer table.
-/

@[expose] public section
namespace SymmetricFourWreath.LargeCentralizer
open Subgroup
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq

def first : P := pair (DihedralGroup.r 2,1)
def second : P := pair (1,DihedralGroup.r 2)
def diagonal : P := first * second

private def samples : Finset P := (Finset.univ : Finset (ZMod 4 × ZMod 2 × C2)).image
  (fun a => pair (DihedralGroup.r a.1,DihedralGroup.r (a.2.1.val:ZMod 4)) * RegularWreathProduct.inl a.2.2)

private def conjugates (x : P) : Finset P := samples.image fun g => g*x*g⁻¹

private theorem orbit_test : ∀ x : P, x*x=1 →
    x=1 ∨ x=diagonal ∨ x=first ∨ x=second ∨ 4 ≤ (conjugates x).card := by decide +kernel

private theorem diagonal_central : ∀ x : P, x*diagonal=diagonal*x := by decide +kernel

private theorem first_conjugate_second :
    (RegularWreathProduct.inl turn : P)*first*(RegularWreathProduct.inl turn : P)⁻¹ = second := by
  decide +kernel

private theorem conjugates_card_le (x : P) :
    (conjugates x).card ≤ Nat.card {y : P // IsConj x y} := by
  let f : (conjugates x) → {y : P // IsConj x y} := fun y =>
    ⟨y.val,by
      obtain ⟨g,hg,he⟩ := Finset.mem_image.mp y.property
      exact isConj_iff.mpr ⟨g,he⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun y : {y : P // IsConj x y} => y.val) h)
  simpa using Nat.card_le_card_of_injective f hf

theorem large_centralizer_cases (x : P) (hx : orderOf x = 2) :
    x ∈ center P ∨ IsConj first x ∨ Nat.card (centralizer ({x} : Set P)) ≤ 32 := by
  have hx2 : x*x=1 := by simpa [←pow_two,hx] using pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by intro he; rw [he,orderOf_one] at hx; omega
  obtain he | he | he | he | hc := orbit_test x hx2
  · exact False.elim (hx1 he)
  · left
    rw [he]
    exact mem_center_iff.mpr diagonal_central
  · exact Or.inr (Or.inl (he ▸ IsConj.refl first))
  · right; left
    rw [he]
    exact isConj_iff.mpr ⟨RegularWreathProduct.inl turn,first_conjugate_second⟩
  · right; right
    have hfour := hc.trans (conjugates_card_le x)
    have hmul := ConjClasses.nat_card_carrier_mul_card_centralizer x
    rw [card_P] at hmul
    change Nat.card {y : P // IsConj x y} * Nat.card (centralizer ({x} : Set P)) = 128 at hmul
    nlinarith [Nat.mul_le_mul_right (Nat.card (centralizer ({x} : Set P))) hfour]


theorem large_centralizer_cases_relative (t x : P) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set P)) = 64) (hx : orderOf x = 2) :
    x ∈ center P ∨ IsConj t x ∨ Nat.card (centralizer ({x} : Set P)) ≤ 32 := by
  obtain htZ | htconj | htcard := large_centralizer_cases t ht
  · have he : centralizer ({t} : Set P) = ⊤ := (eq_top_iff' _).mpr fun y =>
      mem_centralizer_singleton_iff.mpr (mem_center_iff.mp htZ y)
    have hcard : Nat.card (centralizer ({t} : Set P)) = 128 := by
      rw [he,Nat.card_congr (topEquiv : (⊤ : Subgroup P) ≃* P).toEquiv,card_P]
    omega
  · obtain hxZ | hxconj | hxcard := large_centralizer_cases x hx
    · exact Or.inl hxZ
    · exact Or.inr (Or.inl (htconj.symm.trans hxconj))
    · exact Or.inr (Or.inr hxcard)
  · omega

variable {G : Type*} [Group G]

theorem large_centralizer_cases_of_equiv (e : G ≃* P) (t x : G)
    (ht : orderOf t = 2) (hc : Nat.card (centralizer ({t} : Set G)) = 64)
    (hx : orderOf x = 2) :
    x ∈ center G ∨ IsConj t x ∨ Nat.card (centralizer ({x} : Set G)) ≤ 32 := by
  have hcard (a : G) : Nat.card (centralizer ({a} : Set G)) =
      Nat.card (centralizer ({e a} : Set P)) := Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e a).toEquiv
  obtain hz | hconj | hsmall := large_centralizer_cases_relative (e t) (e x)
    ((e.orderOf_eq t).trans ht) ((hcard t).symm.trans hc) ((e.orderOf_eq x).trans hx)
  · left
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hz (e y)
  · right; left
    have hh := e.symm.toMonoidHom.map_isConj hconj
    change IsConj (e.symm (e t)) (e.symm (e x)) at hh
    simpa only [e.symm_apply_apply] using hh
  · exact Or.inr (Or.inr ((hcard x).le.trans hsmall))

end SymmetricFourWreath.LargeCentralizer
