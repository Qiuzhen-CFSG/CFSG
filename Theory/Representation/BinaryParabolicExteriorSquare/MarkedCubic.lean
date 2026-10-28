module
public import Theory.Representation.BinaryParabolicExteriorSquare.CubicRestriction
public import Theory.GroupTheory.OddSubgroupLift
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# A single cubic on the original binary sections

A specified order-three matrix lifts through a two-group kernel to a
cyclic subgroup of order three, retaining that exact matrix as generator.
Any such lifted cubic maps onto the normal order-three subgroup of a
cyclic-by-two quotient with two-group kernel. Thus the actors used on
different sections need not be independently stipulated or matched.

Source application: the common cubic on the natural, exterior, dual and
radical sections in Aschbacher–Smith, *The Classification of Quasithin
Groups*, 13.8.31(3), printed p.965.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare.PlaneSpan

def cubicElement : SL(4,Bit) := ⟨planeCubic,by decide⟩

theorem cubicElement_order : orderOf cubicElement = 3 :=
  orderOf_eq_prime (by decide) (by decide)

/-- Retain the exact marked cubic when lifting across a two-group kernel. -/
theorem exists_marked_cubic {G : Type*} [Group G] [Finite G]
    (π : G →* SL(4,Bit)) (hker : IsPGroup 2 π.ker)
    (hcubic : cubicElement ∈ π.range) :
    ∃ (A : Subgroup G) (a : A), Nat.card A = 3 ∧
      (∀ b, b ∈ zpowers a) ∧ π a = cubicElement := by
  let c : π.range := ⟨cubicElement,hcubic⟩
  have hc : orderOf c = 3 := (Subgroup.orderOf_coe c).symm.trans cubicElement_order
  have hk : IsPGroup 2 π.rangeRestrict.ker := by
    have he : π.rangeRestrict.ker = π.ker := by ext x; exact Subtype.ext_iff
    rw [he]
    exact hker
  obtain ⟨A,hA,hfi,hcard,_⟩ := π.rangeRestrict.exists_odd_subgroup_lift
    π.rangeRestrict_surjective hk (zpowers c) (by rw [Nat.card_zpowers,hc]; decide)
  have hm : c ∈ A.map π.rangeRestrict := by rw [hA]; exact mem_zpowers c
  obtain ⟨a,ha,he⟩ := hm
  have hac : Nat.card A = 3 := hcard.trans ((Nat.card_zpowers c).trans hc)
  have han : (⟨a,ha⟩ : A) ≠ 1 := by
    intro hh
    have ha1 : a = 1 := congrArg Subtype.val hh
    rw [ha1,map_one] at he
    have hn := congrArg orderOf he
    rw [orderOf_one,hc] at hn
    contradiction
  refine ⟨A,⟨a,ha⟩,hac,?_,congrArg Subtype.val he⟩
  intro b
  rw [zpowers_eq_top_of_prime_card hac han]
  trivial

/-- Every lifted cubic has the same image in a cyclic-by-two quotient. -/
theorem cubic_image_eq_normal_three
    {D K : Type*} [Group D] [Finite D] [Group K] [Finite K]
    (f : D →* K) (hp : IsPGroup 2 f.ker)
    (A : Subgroup D) (hA : Nat.card A = 3)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) : A.map f = X := by
  let q := QuotientGroup.mk' X
  have hle : A.map f ≤ X := by
    rintro _ ⟨x,hx,rfl⟩
    apply (QuotientGroup.eq_one_iff (f x)).mp
    apply orderOf_eq_one_iff.mp
    have hd : orderOf (q (f x)) ∣ 3 := by
      have hh := orderOf_map_dvd (q.comp (f.comp A.subtype)) (⟨x,hx⟩ : A)
      exact hh.trans (hA ▸ orderOf_dvd_natCard (⟨x,hx⟩ : A))
    exact Nat.eq_one_of_dvd_coprimes
      (hq.orderOf_coprime (by decide : Nat.Coprime 2 3) (q (f x))) dvd_rfl hd
  have hi : Function.Injective (f.comp A.subtype) := by
    apply injective_comp_subtype_of_coprime_ker f ?_ A
      (IsPGroup.of_card (n := 1) (by simpa using hA) : IsPGroup 3 A)
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hc : Nat.card (A.map f) = 3 := by
    let e : A ≃* A.map f := MulEquiv.ofBijective (f.subgroupMap A)
      ⟨fun x y h => hi (congrArg Subtype.val h),f.subgroupMap_surjective A⟩
    exact (Nat.card_congr e.toEquiv).symm.trans hA
  exact eq_of_le_of_card_ge hle (by rw [hX,hc])

end Representation.BinaryParabolicExteriorSquare.PlaneSpan
