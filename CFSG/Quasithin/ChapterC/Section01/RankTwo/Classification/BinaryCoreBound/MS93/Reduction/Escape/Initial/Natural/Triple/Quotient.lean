module

public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.DualCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions

/-!
# The actual quotient action and its dual

For ambient normal H and N, conjugation on H/(H intersect N) linearizes
when the quotient is elementary abelian. The image of [H,A] is exactly
the linear commutator space. Its cardinality is [ [H,A] : [H,A] intersect N ],
so an image of order at most two gives codimension at most one on the dual.

Annihilator duality reverses the two actors: [E*,B] fixed by A is equivalent
to [E,A] fixed by B. Transport back through the quotient then gives
[[H,A],B] contained in N. No assertion that this fixedness always holds is made.

Source: Meierfrankenfeld--Stellmacher (1993), the dual-module step in
(4.3.1)(iii), printed p.883, with the meaning of c(U) on p.881.
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple

variable {G : Type*} [Group G] (H N : Subgroup G) [H.Normal] [N.Normal]

/-- Conjugation on the literal quotient of two ambient normal subgroups. -/
noncomputable def sectionAction : G →* MulAut (H ⧸ N.subgroupOf H) :=
  (Classical.choose (exists_quotient_conjugation_action ⊤ H N
    le_normalizer_of_normal le_normalizer_of_normal inferInstance)).comp
      Subgroup.topEquiv.symm.toMonoidHom

/-- On representatives the action is the original group conjugation. -/
theorem sectionAction_mk (g : G) (h : H) :
    sectionAction H N g (QuotientGroup.mk' (N.subgroupOf H) h) =
      QuotientGroup.mk' (N.subgroupOf H) (MulAut.conjNormal g h) :=
  Classical.choose_spec (exists_quotient_conjugation_action ⊤ H N
    le_normalizer_of_normal le_normalizer_of_normal inferInstance) ⟨g, mem_top g⟩ h

variable [IsElementaryAbelian 2 (H ⧸ N.subgroupOf H)]

/-- Binary linearization of the full ambient conjugation action. -/
noncomputable def sectionRepresentation :
    Representation (ZMod 2) G (Additive (H ⧸ N.subgroupOf H)) :=
  Offenders.linearize (sectionAction H N)

/-- The actual image of D in H/N, viewed as a binary subspace. -/
noncomputable def quotientImage (D : Subgroup G) :
    Submodule (ZMod 2) (Additive (H ⧸ N.subgroupOf H)) :=
  AddSubgroup.toZModSubmodule 2
    (((D.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))).toAddSubgroup)

/-- Linear displacement belongs to the image of the group commutator. -/
theorem commutatorSpace_le_image (A : Subgroup G) :
    Coinvariants.ker ((sectionRepresentation H N).comp A.subtype) ≤
      quotientImage H N ⁅H, A⁆ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, v⟩, rfl⟩
  obtain ⟨h, hv⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) v.toMul
  have hv' : v = Additive.ofMul (QuotientGroup.mk' (N.subgroupOf H) h) := hv.symm
  subst v
  simp only [sub_eq_add_neg]
  change Additive.ofMul
    (sectionAction H N g.val (QuotientGroup.mk' (N.subgroupOf H) h) *
      (QuotientGroup.mk' (N.subgroupOf H) h)⁻¹) ∈ quotientImage H N ⁅H, A⁆
  rw [sectionAction_mk, ← map_inv, ← map_mul]
  refine ⟨MulAut.conjNormal g.val h * h⁻¹, ?_, rfl⟩
  change ⁅g.val, h.val⁆ ∈ ⁅H, A⁆
  rw [commutator_comm]
  exact commutator_mem_commutator g.property h.property

/-- The group and linear commutators have exactly the same quotient image. -/
theorem commutatorSpace_eq_image (A : Subgroup G) :
    Coinvariants.ker ((sectionRepresentation H N).comp A.subtype) =
      quotientImage H N ⁅H, A⁆ := by
  apply le_antisymm (commutatorSpace_le_image H N A)
  let W := Coinvariants.ker ((sectionRepresentation H N).comp A.subtype)
  let K : Subgroup (H ⧸ N.subgroupOf H) := Subgroup.toAddSubgroup.symm W.toAddSubgroup
  let q := QuotientGroup.mk' (N.subgroupOf H)
  have hc : ⁅H, A⁆ ≤ (K.comap q).map H.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha h hh
    let hH : H := ⟨h, hh⟩
    let xH : H := MulAut.conjNormal a hH * hH⁻¹
    refine ⟨xH, ?_, rfl⟩
    have hx := Coinvariants.sub_mem_ker
      (ρ := (sectionRepresentation H N).comp A.subtype) ⟨a, ha⟩ (Additive.ofMul (q hH))
    change Additive.ofMul (q xH) ∈ W
    simp only [sub_eq_add_neg] at hx
    change Additive.ofMul (sectionAction H N a (q hH) * (q hH)⁻¹) ∈ W at hx
    rw [sectionAction_mk, ← map_inv, ← map_mul] at hx
    exact hx
  intro v hv
  obtain ⟨x, hx, he⟩ := hv
  obtain ⟨y, hy, hyx⟩ := hc hx
  have hyx' : y = x := Subtype.ext hyx
  subst y
  change Additive.ofMul (q x) ∈ W at hy
  have he' : Additive.ofMul (q x) = v := congrArg Additive.ofMul he
  exact he' ▸ hy

/-- Duality reverses the order of the two acting subgroups. -/
theorem dual_commutator_fixed_iff {k E : Type*} [Field k]
    [AddCommGroup E] [Module k E] (ρ : Representation k G E) (A B : Subgroup G) :
    Coinvariants.ker (ρ.dual.comp B.subtype) ≤ invariants (ρ.dual.comp A.subtype) ↔
      Coinvariants.ker (ρ.comp A.subtype) ≤ invariants (ρ.comp B.subtype) := by
  have hA := invariants_dual_eq_commutator_annihilator
    (show Representation k A E from ρ.comp A.subtype)
  have hB := invariants_eq_dual_commutator_coannihilator
    (show Representation k B E from ρ.comp B.subtype)
  have hcomp (D : Subgroup G) : Representation.dual (ρ.comp D.subtype) =
      ρ.dual.comp D.subtype := by
    ext g f v
    rfl
  rw [hcomp] at hA hB
  rw [hA, Submodule.le_dualAnnihilator_iff_le_dualCoannihilator, ← hB]

/-- Fixing the dual moving subspace gives the original triple commutator. -/
theorem triple_le_of_dual_fixed (A B : Subgroup G)
    (hd : Coinvariants.ker ((sectionRepresentation H N).dual.comp B.subtype) ≤
      invariants ((sectionRepresentation H N).dual.comp A.subtype)) :
    ⁅⁅H, A⁆, B⁆ ≤ N := by
  have hf := (dual_commutator_fixed_iff (sectionRepresentation H N) A B).mp hd
  rw [commutatorSpace_eq_image] at hf
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb x hx
  let xH : H := ⟨x, (commutator_le_left H A) hx⟩
  let q := QuotientGroup.mk' (N.subgroupOf H)
  have hxW : Additive.ofMul (q xH) ∈ quotientImage H N ⁅H, A⁆ := ⟨xH, hx, rfl⟩
  have hh := hf hxW ⟨b, hb⟩
  have he : sectionAction H N b (q xH) = q xH := congrArg Additive.toMul hh
  rw [sectionAction_mk] at he
  have hone : q (MulAut.conjNormal b xH * xH⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hm : MulAut.conjNormal b xH * xH⁻¹ ∈ N.subgroupOf H :=
    (QuotientGroup.eq_one_iff _).mp hone
  exact hm

omit [H.Normal] in
/-- The cardinality is the relative index, retaining D intersect N. -/
theorem quotientImage_card (D : Subgroup G) (hD : D ≤ H) :
    Nat.card (quotientImage H N D) = N.relIndex D := by
  let e : quotientImage H N D ≃
      ((D.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))) := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun v => ⟨Additive.ofMul v.val, v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, ← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hD]

/-- An image of order at most two gives dual fixed codimension at most one. -/
theorem dual_fixedCodim_le_one [Finite H] (A : Subgroup G)
    (hsmall : N.relIndex ⁅H, A⁆ ≤ 2) :
    Representation.BinaryOffender.fixedCodim (sectionRepresentation H N).dual A ≤ 1 := by
  have hcard : Nat.card (quotientImage H N ⁅H, A⁆) ≤ 2 := by
    rw [quotientImage_card H N _ (commutator_le_left _ _)]
    exact hsmall
  have hdim : Module.finrank (ZMod 2) (quotientImage H N ⁅H, A⁆) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa using hcard)
  let ρA : Representation (ZMod 2) A (Additive (H ⧸ N.subgroupOf H)) :=
    (sectionRepresentation H N).comp A.subtype
  change Module.finrank (ZMod 2)
    (_ ⧸ invariants (Representation.dual ρA)) ≤ 1
  rw [finrank_quotient_dual_invariants_eq_commutator]
  exact (Submodule.finrank_mono (commutatorSpace_le_image H N A)).trans hdim

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
