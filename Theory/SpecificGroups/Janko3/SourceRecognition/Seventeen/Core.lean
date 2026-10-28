module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Source
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Complement

/-!
# The two-core and the literal overlap in the seventeen-point amalgam

The complement 3 × D₁₀ has trivial two-core: a two-element and its
commutator with the rotation cannot both have square one unless the
element is trivial. Pulling back the point two-core to the actual H₁ ∩ H₂
therefore gives trivial intersection. The semidirect product projection
computes the point two-core order as sixteen. Counting proves that the
literal overlap complements it.

Consequently the graph faithfulness proof needs only identification of
the edge stabilizer with that overlap, not an assumed faithful action.
These are the local kernel steps used in Baumeister, *A geometry for groups
of J₃-type* (2007), Lemma 2.7, p.497.
-/

@[expose] public section
open Subgroup MulAction
namespace Sporadic.Janko3.SourceRecognition.Seventeen

private theorem complement_card : Nat.card Complement = 30 := by
  norm_num [Complement, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, DihedralGroup.card]

theorem complement_twoCore : pCore 2 Complement = ⊥ := by
  have hpow (x : pCore 2 Complement) : x ^ 2 = 1 := by
    have hd : orderOf x ∣ 2 * 15 := (orderOf_dvd_natCard x).trans
      ((pCore 2 Complement).card_subgroup_dvd_card.trans (by rw [complement_card]))
    have hc := (pCore_isPGroup (p := 2) (G := Complement)).orderOf_coprime
      (by decide : Nat.Coprime 2 15) x
    exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right hd)
  have htest : ∀ x : Complement, x ^ 2 = 1 →
      ((1, DihedralGroup.r 1) * x * (1, DihedralGroup.r 1)⁻¹ * x⁻¹) ^ 2 = 1 →
      x = 1 := by decide +kernel
  apply bot_unique
  intro x hx
  apply htest x (congrArg Subtype.val (hpow ⟨x, hx⟩))
  have hm : (1, DihedralGroup.r 1) * x * (1, DihedralGroup.r 1)⁻¹ * x⁻¹ ∈
      pCore 2 Complement :=
    (pCore 2 _).mul_mem (pCore_normal.conj_mem x hx _) ((pCore 2 _).inv_mem hx)
  exact congrArg Subtype.val (hpow ⟨_, hm⟩)

private theorem core_disjoint_of_core_free {H : Type*} [Group H]
    (C : Subgroup H) (he : C ≃* Complement) : Disjoint C (pCore 2 H) := by
  let N := (pCore 2 H).subgroupOf C
  have hn : N ≤ pCore 2 C := le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  have hc : pCore 2 C = ⊥ := by
    apply Subgroup.map_injective (f := he.toMonoidHom) he.injective
    rw [pCore_map_iso, complement_twoCore, Subgroup.map_bot]
  rw [hc] at hn
  exact (subgroupOf_eq_bot.mp (bot_unique hn)).symm

namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

theorem overlap_core_disjoint : Disjoint (S.H2.subgroupOf S.H1) (pCore 2 S.H1) := by
  apply core_disjoint_of_core_free
  have he : S.H2.subgroupOf S.H1 = (S.H1 ⊓ S.H2).subgroupOf S.H1 :=
    (inf_subgroupOf_left _ _).symm
  exact ((MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe inf_le_left)).trans S.overlap12

theorem core_card : Nat.card (pCore 2 S.H1) = 16 := by
  let M := Plane ⋊[S.action] Complement
  let π : M →* Complement := SemidirectProduct.rightHom
  have hmc : Nat.card M = 480 := by
    rw [SemidirectProduct.card, complement_card]
    norm_num [Plane, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  let : Finite M := Nat.finite_of_card_ne_zero (by rw [hmc]; decide)
  have hker : Nat.card π.ker = 16 := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    norm_num [Plane, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  have hpker : IsPGroup 2 π.ker := IsPGroup.of_card (n := 4) hker
  have hM := π.card_pCore_of_ker_isPGroup
    (fun x => ⟨SemidirectProduct.inr x, rfl⟩) hpker
  rw [complement_twoCore, Subgroup.card_bot, mul_one, hker] at hM
  have hc : Nat.card ((pCore 2 S.H1).map S.pointEquiv.toMonoidHom) =
      Nat.card (pCore 2 S.H1) := Nat.card_congr
        (Subgroup.equivMapOfInjective _ S.pointEquiv.toMonoidHom S.pointEquiv.injective).symm.toEquiv
  rw [pCore_map_iso] at hc
  exact hc.symm.trans hM

theorem overlap_complements_core :
    (pCore 2 S.H1).IsComplement' (S.H2.subgroupOf S.H1) := by
  let : Finite S.H1 := Nat.finite_of_card_ne_zero (by rw [point_card S]; decide)
  apply isComplement'_of_card_mul_and_disjoint
  · have hc : Nat.card (S.H2.subgroupOf S.H1) = 30 := by
      rw [← inf_subgroupOf_left, Nat.card_congr (subgroupOfEquivOfLe
        (show S.H1 ⊓ S.H2 ≤ S.H1 from inf_le_left)).toEquiv]
      exact overlap_card S
    rw [core_card S, hc, point_card S]
  · exact (overlap_core_disjoint S).symm

theorem faithful_of_edge (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1)
    (hedge : CosetGraph.edgeStabilizer (cosetData S b hb hbout) = S.H2.subgroupOf S.H1) :
    FaithfulSMul G (CosetGraph.Vertex (cosetData S b hb hbout)) :=
  faithful S b hb hbout hedge (overlap_core_disjoint S)

theorem third_overlap_card : Nat.card (S.H2 ⊓ S.H3 : Subgroup G) = 12 := by
  rw [Nat.card_congr S.overlap23.toEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_perm, Nat.factorial]

theorem exists_outside_involution :
    ∃ b : G, b * b = 1 ∧ b ∈ S.H2 ∧ b ∈ S.H3 ∧ b ∉ S.H1 := by
  have hnot : ¬ S.H2 ⊓ S.H3 ≤ S.H1 := by
    intro hle
    have hd := card_dvd_of_le (le_inf hle
      (show S.H2 ⊓ S.H3 ≤ S.H2 from inf_le_left))
    rw [third_overlap_card S, overlap_card S] at hd
    norm_num at hd
  obtain ⟨x, hx, hxout⟩ := SetLike.not_le_iff_exists.mp hnot
  have hsquare : x^2 ∈ S.H1 :=
    (S.H1.subgroupOf S.H2).sq_mem_of_index_two (overlap_index_two S) ⟨x, hx.1⟩
  have htest : ∀ y : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2), y^6 = 1 := by
    decide +kernel
  have hsix : x^6 = 1 := by
    have he : (⟨x, hx⟩ : (S.H2 ⊓ S.H3 : Subgroup G))^6 = 1 := by
      apply S.overlap23.injective
      rw [map_pow, map_one]
      exact htest _
    exact congrArg Subtype.val he
  refine ⟨x^3, ?_, S.H2.pow_mem hx.1 3, S.H3.pow_mem hx.2 3, ?_⟩
  · rw [← pow_add]
    exact hsix
  · intro hb
    exact hxout ((S.H1.mul_mem_cancel_left hsquare).mp (by simpa only [pow_succ] using hb))

theorem exists_connected_graph :
    ∃ (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1),
      b ∈ S.H2 ∧ b ∈ S.H3 ∧ (CosetGraph.graph (cosetData S b hb hbout)).Connected := by
  obtain ⟨b, hb, hb2, hb3, hbout⟩ := exists_outside_involution S
  exact ⟨b, hb, hbout, hb2, hb3, connected S b hb hbout hb2⟩

end SourceData
end Sporadic.Janko3.SourceRecognition.Seventeen
