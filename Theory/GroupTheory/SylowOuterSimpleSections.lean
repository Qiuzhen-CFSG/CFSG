module
public import Theory.GroupTheory.SylowOuterSolvability
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.GroupTheory.PGroup.FrattiniCubicConjugacy

/-!
# Simple outer sections detected on a small Sylow Frattini quotient

Sylow conjugacy makes the automorphism stabilizer surject onto the outer group.
Its restriction kernel is solvable whenever the pointwise Sylow fixer is.
A nonsolvable simple section therefore survives in the automorphism group of
the Sylow subgroup. The binary Frattini kernel is a two-group; in dimensions
at most five, the general linear group order is not divisible by 27.

This is the narrower model obstruction needed for the perfect actor in
Aschbacher–Smith 4.4.3, printed p.621. It does not assert full outer solvability.
-/

public section
open Subgroup
open scoped Pointwise
namespace MulAut

private theorem section_card_dvd_of_solvable_kernel
    {H Q R S : Type*} [Group H] [Finite H] [Group Q] [Group R] [Finite R]
    [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (q : H →* Q) (hq : Function.Surjective q)
    (r : H →* R) [Group.IsSolvable r.ker]
    (U : Subgroup Q) (f : U →* S) (hf : Function.Surjective f) :
    Nat.card S ∣ Nat.card R := by
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel hS r.ker
    (U.comap q) (f.comp (q.subgroupComap U))
    (hf.comp (q.subgroupComap_surjective_of_surjective U hq))
  have hdiv := (card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv] at hdiv
  exact hdiv.trans r.range.card_subgroup_dvd_card

theorem simple_outer_section_card_dvd_sylow_aut
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G))]
    (hS : ¬ Group.IsSolvable S)
    (U : Subgroup (Outer G)) (f : U →* S) (hf : Function.Surjective f) :
    Nat.card S ∣ Nat.card (MulAut P) := by
  let H := MulAction.stabilizer (MulAut G) (P : Subgroup G)
  let F := fixingSubgroup (MulAut G) (P : Set G)
  let r : H →* MulAut P :=
    { toFun := fun a => (a.val.subgroupMap (P : Subgroup G)).trans
        (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let i : r.ker →* F :=
    (H.subtype.comp r.ker.subtype).codRestrict F (by
      intro a
      apply (mem_fixingSubgroup_iff (MulAut G)).mpr
      intro x hx
      change (a.val.val : MulAut G) x = x
      exact congrArg (fun b : MulAut P => ((b ⟨x,hx⟩ : P) : G)) a.property)
  have hi : Function.Injective i := by
    intro a b hab
    have hab' : (a.val.val : MulAut G) = b.val.val :=
      congrArg (fun z : F => (z : MulAut G)) hab
    exact Subtype.ext (Subtype.ext hab')
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective hi
  let q := (QuotientGroup.mk' (innerSubgroup G)).comp H.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (a • P) P
    have hm : MulAut.conj g * a ∈ H := by
      change (MulAut.conj g * a) • (P : Subgroup G) = (P : Subgroup G)
      rw [mul_smul]
      exact congrArg Sylow.toSubgroup hg
    refine ⟨⟨MulAut.conj g * a,hm⟩,?_⟩
    change QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g * a) = _
    have hi : QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [map_mul,hi,one_mul]
  exact section_card_dvd_of_solvable_kernel hS q hq r U f hf

end MulAut
namespace IsPGroup
variable {Q : Type*} [Group Q] [Finite Q]

theorem not_twentyseven_dvd_card_mulAut_of_frattini_card_le_thirtytwo
    (hQ : IsPGroup 2 Q) (hbound : Nat.card (Q ⧸ frattini Q) ≤ 32) :
    ¬27 ∣ Nat.card (MulAut Q) := by
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨n,hn⟩ := (hQ.to_quotient (frattini Q)).exists_card_eq
  have hn5 : n ≤ 5 := by
    by_contra! h
    have hp : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
    rw [← hn] at hp
    norm_num at hp
    omega
  have hAut : ¬27 ∣ Nat.card (MulAut (Q ⧸ frattini Q)) := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  let f := quotientAut (frattini Q)
  have hcount : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut Q) := by
    rw [← index_ker]
    exact f.ker.card_mul_index
  obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel hQ).exists_card_eq
  have hcop : Nat.Coprime 27 (Nat.card f.ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 27 2).pow_right k
  intro h
  rw [← hcount] at h
  exact hAut ((hcop.dvd_of_dvd_mul_left h).trans f.range.card_subgroup_dvd_card)
end IsPGroup
