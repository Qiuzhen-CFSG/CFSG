module

public import Theory.GroupTheory.SylowOuterSimpleSections

/-!
# Simple outer sections on the Sylow Frattini quotient

A nonsolvable simple section of an outer automorphism group survives both
restriction to a Sylow subgroup and the Burnside basis kernel. Thus its order
divides the automorphism order of the Sylow Frattini quotient. The pointwise
Sylow fixer remains an explicit solvability hypothesis.

This refines the Sylow restriction used in Aschbacher--Smith 4.4.10--11,
printed p.621, without asserting the full Schreier property.
-/

public section
open Subgroup
open scoped Pointwise
namespace MulAut

private theorem solvable_comp_kernel
    {H Q R : Type*} [Group H] [Group Q] [Group R]
    (r : H →* Q) (a : Q →* R) [Group.IsSolvable r.ker] [Group.IsSolvable a.ker] :
    Group.IsSolvable (a.comp r).ker := by
  let k : (a.comp r).ker →* a.ker :=
    { toFun := fun x => ⟨r x.val, x.property⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun x y => Subtype.ext (map_mul r x.val y.val) }
  let i : k.ker →* r.ker :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : r.ker => (z : H)) h))
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective hi
  exact Group.isSolvable_of_ker_le_range k.ker.subtype k (by rw [range_subtype])

/-- A nonsolvable simple outer section survives on the actual Sylow Frattini
quotient, including its entire defining-characteristic part. -/
theorem simple_outer_section_card_dvd_frattini_aut
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G))]
    (hS : ¬ Group.IsSolvable S)
    (U : Subgroup (Outer G)) (f : U →* S) (hf : Function.Surjective f) :
    Nat.card S ∣ Nat.card (MulAut (P ⧸ frattini P)) := by
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
    exact Subtype.ext (Subtype.ext (congrArg (fun z : F => (z : MulAut G)) hab))
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective hi
  let a := quotientAut (frattini P)
  let : Group.IsNilpotent a.ker :=
    (isPGroup_quotientAut_frattini_kernel P.isPGroup').isNilpotent
  let : Group.IsSolvable (a.comp r).ker := solvable_comp_kernel r a
  let q := (QuotientGroup.mk' (innerSubgroup G)).comp H.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (b • P) P
    have hm : MulAut.conj g * b ∈ H := by
      change (MulAut.conj g * b) • (P : Subgroup G) = (P : Subgroup G)
      rw [mul_smul]
      exact congrArg Sylow.toSubgroup hg
    refine ⟨⟨MulAut.conj g * b,hm⟩,?_⟩
    change QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g * b) = _
    have hg' : QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [map_mul,hg',one_mul]
  obtain ⟨W,b,hb⟩ := simple_section_quotient_of_solvable_kernel hS (a.comp r).ker
    (U.comap q) (f.comp (q.subgroupComap U))
    (hf.comp (q.subgroupComap_surjective_of_surjective U hq))
  have hd := (card_dvd_of_surjective b hb).trans W.card_subgroup_dvd_card
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (a.comp r)).toEquiv] at hd
  exact hd.trans (a.comp r).range.card_subgroup_dvd_card

end MulAut

namespace MulAut

/-- With at most eight binary Frattini generators, every nonsolvable simple
outer section has order dividing the order of GL₈(2). -/
theorem simple_outer_section_card_dvd_GL_eight
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    (P : Sylow 2 G) (hP : Nat.card (P ⧸ frattini P) ≤ 256)
    [Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G))]
    (hS : ¬ Group.IsSolvable S)
    (U : Subgroup (Outer G)) (f : U →* S) (hf : Function.Surjective f) :
    Nat.card S ∣ 5348063769211699200 := by
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨n,hn⟩ := (P.isPGroup'.to_quotient (frattini P)).exists_card_eq
  have hn8 : n ≤ 8 := by
    by_contra! h
    have hp : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
    rw [← hn] at hp
    norm_num at hp
    omega
  have hdiv := simple_outer_section_card_dvd_frattini_aut P hS U f hf
  apply hdiv.trans
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn]
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

end MulAut
