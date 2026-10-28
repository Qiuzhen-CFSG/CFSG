module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.NonabelianCenter.Layers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderSevenObstruction

/-!
# Excluding small nonabelian binary MS cores

A nonabelian two-group of order at most 32 has no automorphism of order
seven. An element of order seven in L therefore centralizes D = [O₂(J), L].
Its nontrivial image in the simple quotient L/O₂(L) forces the image of the
whole L-action on D to be a two-group. Perfectness of L makes that image
trivial, contradicting noncommutativity of D ≤ L.

In particular, the order-16 alternative in Aschbacher–Smith C.1.34(5)
(combined manuscript, 1 March 2004, pp.136–137) cannot be nonabelian. This
argument uses the actual conjugation action, rather than inferring
commutativity from the order alone. It does not prove the exhaustive
alternatives or the centers in C.1.34(3),(4).
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup
open scoped IsMulCommutative
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- A nonabelian commutator core has order greater than 32; in particular it
cannot realize the central extension of order 16 in C.1.34(5). -/
theorem Input.nonabelianCore_card_gt (h : Input κ L R)
    (hnoncomm : ¬ IsMulCommutative (commutatorCore L)) :
    32 < Nat.card (commutatorCore L) := by
  by_contra hnot
  have hbound : Nat.card (commutatorCore L) ≤ 32 := by omega
  let D := commutatorCore L
  let := h.component_normal
  let : D.Normal := h.commutatorCore_normal
  have hDL : D ≤ L := commutator_le_right _ _
  have htwo : IsPGroup 2 D := h.commutatorCore_twoGroup
  let f : L →* MulAut D := MulAut.conjNormal.comp L.subtype
  have h7L : 7 ∣ Nat.card L := by
    have hd := (pCore 2 L).index_dvd_card
    change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card L at hd
    rw [h.quotient_card] at hd
    exact dvd_trans (by decide : 7 ∣ 168) hd
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 7 h7L
  have hfa : f a = 1 := by
    have hd : orderOf (f a) ∣ 7 := ha ▸ orderOf_map_dvd f a
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with ho | ho
    · exact orderOf_eq_one_iff.mp ho
    · have hz : Nat.card (zpowers (f a)) = 7 := by rw [Nat.card_zpowers, ho]
      exact (SmallNonabelianTwoGroup.not_seven_dvd_odd_actor_card
        htwo hnoncomm hbound (zpowers (f a)) (by rw [hz]; decide)
        (by rw [hz])).elim
  let q := QuotientGroup.mk' (pCore 2 L)
  have hqa : q a ≠ 1 := by
    intro he
    have ham : a ∈ pCore 2 L := (QuotientGroup.eq_one_iff a).mp he
    have hcop := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 7) (⟨a, ham⟩ : pCore 2 L)
    have ho : orderOf (⟨a, ham⟩ : pCore 2 L) = 7 := by
      simpa only [← Subgroup.orderOf_coe] using ha
    rw [ho] at hcop
    norm_num at hcop
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    (h.quotientEquiv.trans Matrix.PSL3Two.equiv).isSimpleGroup
  have hn : (f.ker.map q).Normal := f.normal_ker.map q (QuotientGroup.mk'_surjective _)
  have ht : f.ker.map q = ⊤ := hn.eq_bot_or_eq_top.resolve_left (by
    intro he
    have hm : q a ∈ f.ker.map q := mem_map_of_mem q hfa
    exact hqa (Subgroup.mem_bot.mp (he ▸ hm)))
  have hsup : f.ker ⊔ pCore 2 L = ⊤ := by
    have he := congrArg (fun K => K.comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
  have himage : (pCore 2 L).map f = f.range := by
    have he := congrArg (fun K => K.map f) hsup
    simpa only [Subgroup.map_sup, Subgroup.map_ker_self, bot_sup_eq,
      MonoidHom.range_eq_map] using he
  have himageTwo : IsPGroup 2 f.range := himage ▸ pCore_isPGroup.map f
  let := h.component.perfect
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent f.range himageTwo.isNilpotent
  have hf (l : L) : f l = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict l) 1)
  apply hnoncomm
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  have he := congrArg (fun b : MulAut D => (b y : J))
    (hf ⟨x, hDL x.property⟩)
  change (x : J) * (y : J) * (x : J)⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul).mp he

end CFSG.Quasithin.ChapterC.BinaryMS
