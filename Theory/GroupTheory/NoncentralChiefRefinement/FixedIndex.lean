module
public import Theory.GroupTheory.NoncentralChiefRefinement.CoprimeFixed
public import Mathlib.GroupTheory.Index

/-!
# Fixed indices on the original coprime fixed section

For a normal section A/B, coprime fixed-point lifting identifies the image
of C_A(E) with the E-fixed subgroup of that very section. Its H-fixed
index is at most the upstairs H-centralizer index. The ambient version
keeps A and B inside their original overgroup J and only uses A ≤ U.
No chiefness, irreducibility, or change of section endpoints is assumed.

The proof uses the literal quotient map, coprime lifting, and monotonicity
of relative indices. The source consumer applies this to the chosen
KX-chief section and its original cubic centralizer.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764.
-/

open Subgroup
namespace NoncentralChiefRefinement
@[expose] public noncomputable section
variable {J : Type*} [Group J]

/-- Fixed elements in the literal section, with the original subgroup actor. -/
def sectionFixed (B A : NormalNode J) (E : Subgroup J) : Subgroup (Section B A) where
  carrier := {w | ∀ e : E, sectionAction B A e w = w}
  one_mem' e := map_one _
  mul_mem' hu hv e := by rw [map_mul,hu e,hv e]
  inv_mem' hu e := by rw [map_inv,hu e]

/-- The original section projection maps its actual centralizer onto the fixed
subgroup when the actor has coprime order. -/
theorem sectionFixed_eq_image [Finite J] (B A : NormalNode J) (hBA : B ≤ A)
    (E : Subgroup J) (hsolv : Group.IsSolvable A.val)
    (hcop : Nat.Coprime (Nat.card E) (Nat.card A.val)) :
    sectionFixed B A E = ((centralizer (E : Set J)).subgroupOf A.val).map
      (QuotientGroup.mk' (B.val.subgroupOf A.val)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨a,ha,rfl⟩ := section_fixed_lift B A hBA E hsolv hcop w hw
    exact mem_map_of_mem _ ha
  · rintro w ⟨a,ha,rfl⟩ e
    rw [sectionAction_mk]
    congr 1
    apply Subtype.ext
    change (e : J) * (a : J) * (e : J)⁻¹ = (a : J)
    have he : (e : J) * (a : J) = (a : J) * (e : J) := ha e e.property
    rw [he,mul_inv_cancel_right]

/-- The fixed-point index on a coprime fixed section is at most the original
centralizer index upstairs. No irreducibility or changed endpoints are used. -/
theorem sectionFixed_relIndex_le [Finite J] (B A : NormalNode J) (hBA : B ≤ A)
    (E H : Subgroup J) (hsolv : Group.IsSolvable A.val)
    (hcop : Nat.Coprime (Nat.card E) (Nat.card A.val)) :
    (sectionFixed B A H).relIndex (sectionFixed B A E) ≤
      (centralizer (H : Set J)).relIndex (A.val ⊓ centralizer (E : Set J)) := by
  let q := QuotientGroup.mk' (B.val.subgroupOf A.val)
  have hc : (centralizer (H : Set J)).subgroupOf A.val ≤
      (sectionFixed B A H).comap q := by
    intro a ha h
    change sectionAction B A h (q a) = q a
    rw [sectionAction_mk]
    congr 1
    apply Subtype.ext
    change (h : J) * (a : J) * (h : J)⁻¹ = (a : J)
    have he : (h : J) * (a : J) = (a : J) * (h : J) := ha h h.property
    rw [he,mul_inv_cancel_right]
  rw [sectionFixed_eq_image B A hBA E hsolv hcop,←relIndex_comap]
  have hb := relIndex_le_of_le_left hc
    (index_ne_zero_of_finite : ((centralizer (H : Set J)).subgroupOf A.val).relIndex
      ((centralizer (E : Set J)).subgroupOf A.val) ≠ 0)
  rw [show ((centralizer (H : Set J)).subgroupOf A.val).relIndex
      ((centralizer (E : Set J)).subgroupOf A.val) =
      (centralizer (H : Set J)).relIndex (A.val ⊓ centralizer (E : Set J)) by
    rw [subgroupOf,relIndex_comap]
    rw [subgroupOf_map_subtype,inf_comm]] at hb
  exact hb

private theorem centralizer_in_subgroup {G : Type*} [Group G]
    (J E : Subgroup G) (hE : E ≤ J) :
    centralizer (E.subgroupOf J : Set J) = (centralizer (E : Set G)).subgroupOf J := by
  ext j
  constructor
  · intro hj e he
    exact congrArg Subtype.val (hj ⟨e,hE he⟩ he)
  · intro hj e he
    exact Subtype.ext (hj e he)

/-- The same comparison in an ambient group. The section endpoints stay in J;
only their upper containment in U is used. -/
theorem sectionFixed_relIndex_le_ambient {G : Type*} [Group G] [Finite G]
    (J U E H : Subgroup G) (hE : E ≤ J) (hH : H ≤ J)
    (B A : NormalNode J) (hBA : B ≤ A) (hAU : A.val ≤ U.subgroupOf J)
    (hsolv : Group.IsSolvable A.val)
    (hcop : Nat.Coprime (Nat.card (E.subgroupOf J)) (Nat.card A.val)) :
    (sectionFixed B A (H.subgroupOf J)).relIndex (sectionFixed B A (E.subgroupOf J)) ≤
      (centralizer (H : Set G)).relIndex (U ⊓ centralizer (E : Set G)) := by
  have hi := sectionFixed_relIndex_le B A hBA (E.subgroupOf J) (H.subgroupOf J) hsolv hcop
  rw [centralizer_in_subgroup J H hH,centralizer_in_subgroup J E hE] at hi
  have hm : (A.val ⊓ (centralizer (E : Set G)).subgroupOf J).map J.subtype ≤
      U ⊓ centralizer (E : Set G) := by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨hAU ha.1,ha.2⟩
  exact hi.trans ((relIndex_comap _ J.subtype _).le.trans
    (relIndex_le_of_le_right hm index_ne_zero_of_finite))
end
end NoncentralChiefRefinement
