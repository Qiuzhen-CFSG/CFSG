module
public import Theory.GroupTheory.SylowOuterSolvability
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.GroupTheory.PGroup.FrattiniCubicConjugacy

/-!
# Whole radical-free outer sections survive Sylow restriction

A solvable kernel has trivial image in a section whose solvable radical is
trivial. Thus the entire section, including a product of nonabelian simple
groups, survives. Apply this to the Sylow stabilizer's surjection onto the
outer automorphism group and its restriction to the Sylow subgroup.

For a binary Sylow subgroup with at most seven Frattini generators, the
Burnside basis kernel is a two-group and the orders of GL(n,2), n ≤ 7,
contain at most one factor five. Its automorphism group therefore has no
section whose order is divisible by twenty-five and whose radical is trivial.

This supplies the original A₅-pair outer-action argument in
Aschbacher–Smith 4.4.10, printed p.621. The pointwise-fixer solvability
hypothesis is retained for the source consumer to discharge.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup

/-- A product of groups with trivial solvable radical has trivial radical. -/
theorem solvableRadical_prod_eq_bot {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (ha : solvableRadical A = ⊥) (hb : solvableRadical B = ⊥) :
    solvableRadical (A × B) = ⊥ := by
  apply bot_unique
  intro x hx
  have hfst := map_solvableRadical_le_of_surjective (MonoidHom.fst A B) Prod.fst_surjective
  have hsnd := map_solvableRadical_le_of_surjective (MonoidHom.snd A B) Prod.snd_surjective
  have h₁ : x.1 = 1 := mem_bot.mp (ha ▸ hfst (mem_map_of_mem _ hx))
  have h₂ : x.2 = 1 := mem_bot.mp (hb ▸ hsnd (mem_map_of_mem _ hx))
  exact Prod.ext h₁ h₂

/-- A nonsolvable simple group has trivial solvable radical. -/
theorem solvableRadical_eq_bot_of_simple_not_solvable
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hs : ¬ Group.IsSolvable S) : solvableRadical S = ⊥ := by
  rcases (inferInstance : (solvableRadical S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hsol : Group.IsSolvable (⊤ : Subgroup S) := h ▸ inferInstanceAs
      (Group.IsSolvable (solvableRadical S))
    let := hsol
    exact (hs (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom)
      (topEquiv : (⊤ : Subgroup S) ≃* S).surjective)).elim

/-- Removing a solvable kernel preserves a whole section with trivial radical. -/
theorem radicalFree_section_card_dvd_of_solvable_kernel
    {H Q R S : Type*} [Group H] [Finite H] [Group Q] [Group R] [Finite R]
    [Group S] [Finite S] (hS : solvableRadical S = ⊥)
    (q : H →* Q) (hq : Function.Surjective q)
    (r : H →* R) [Group.IsSolvable r.ker]
    (U : Subgroup Q) (f : U →* S) (hf : Function.Surjective f) :
    Nat.card S ∣ Nat.card R := by
  let V := U.comap q
  let a : V →* S := f.comp (q.subgroupComap U)
  have ha : Function.Surjective a := hf.comp (q.subgroupComap_surjective_of_surjective U hq)
  let b : V →* R := r.comp V.subtype
  have hk : b.ker ≤ a.ker := by
    let N := b.ker.map a
    have hn : N.Normal := Normal.map inferInstance a ha
    let j : b.ker →* r.ker := {
      toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := fun x y he =>
      Subtype.ext (Subtype.ext (congrArg (fun z : r.ker => (z : H)) he))
    let : Group.IsSolvable b.ker := Group.isSolvable_of_isSolvable_injective hj
    have hsol : Group.IsSolvable N := Group.isSolvable_of_surjective (a.subgroupMap_surjective b.ker)
    have hzero : N = ⊥ := bot_unique ((le_solvableRadical N hn hsol).trans_eq hS)
    exact (map_eq_bot_iff b.ker).mp hzero
  let c : b.range →* S := b.rangeRestrict.liftOfSurjective b.rangeRestrict_surjective ⟨a,by
    simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have hc : Function.Surjective c := by
    intro s
    obtain ⟨v,rfl⟩ := ha s
    exact ⟨b.rangeRestrict v,by simp [c]⟩
  exact (card_dvd_of_surjective c hc).trans b.range.card_subgroup_dvd_card
end Subgroup

namespace MulAut
/-- A section with trivial radical survives restriction to a Sylow subgroup. -/
theorem radicalFree_outer_section_card_dvd_sylow_aut
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G))]
    (hS : solvableRadical S = ⊥)
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
  exact radicalFree_section_card_dvd_of_solvable_kernel hS q hq r U f hf
end MulAut

namespace IsPGroup
variable {Q : Type*} [Group Q] [Finite Q]
/-- Seven Frattini generators allow at most one factor five in Aut(Q). -/
theorem not_twentyfive_dvd_card_mulAut_of_frattini_card_le_128
    (hQ : IsPGroup 2 Q) (hbound : Nat.card (Q ⧸ frattini Q) ≤ 128) :
    ¬25 ∣ Nat.card (MulAut Q) := by
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨n,hn⟩ := (hQ.to_quotient (frattini Q)).exists_card_eq
  have hn7 : n ≤ 7 := by
    by_contra! h
    have hp : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
    rw [← hn] at hp
    norm_num at hp
    omega
  have hAut : ¬25 ∣ Nat.card (MulAut (Q ⧸ frattini Q)) := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  let f := quotientAut (frattini Q)
  have hcount : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut Q) := by
    rw [← index_ker]
    exact f.ker.card_mul_index
  obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel hQ).exists_card_eq
  have hcop : Nat.Coprime 25 (Nat.card f.ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 25 2).pow_right k
  intro h
  rw [← hcount] at h
  exact hAut ((hcop.dvd_of_dvd_mul_left h).trans f.range.card_subgroup_dvd_card)
end IsPGroup
