module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SmallCoreAction
public import Theory.GroupTheory.CentralSixteenQuinticSplitting
public import Theory.GroupAction.FiveActionMinimalOrder

/-!
# A quintic complement in the small original A₅ core

Cauchy constructs an actual quintic subgroup in the original component.
Its action on the chosen natural sixteen is nontrivial because the literal
action kernel is the two-core; order counting makes the action fixed-free.
Together with the proved whole-core commutator equality, coprime splitting
makes every original local core of order at most 128 have cyclic derived
subgroup. No actor, fixed-space or splitting data is assumed.

Source application: Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

theorem exists_quintic_module_fixer_eq_bot (d : Context T L V V₁ V₂ V₃) :
    ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = 5 ∧
      V ⊓ centralizer (A : Set G) = ⊥ := by
  have hq : Nat.card (L ⧸ pCore 2 L) = 60 := by
    rw [Nat.card_congr d.quotient.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd : 5 ∣ Nat.card L := by
    have hh := (pCore 2 L).index_dvd_card
    rw [index_eq_card,hq] at hh
    exact (by decide : 5 ∣ 60).trans hh
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 hd
  let A := (zpowers a).map L.subtype
  have hAL : A ≤ L := map_subtype_le _
  have hA : Nat.card A = 5 := by
    rw [card_map_of_injective L.subtype_injective,Nat.card_zpowers,ha]
  have hAV : A ≤ normalizer (V : Set G) := hAL.trans d.chosen.normalizes
  let : Normalizes A V := ⟨hAV⟩
  have hm : FixedPoints.subgroup A V ≠ ⊤ := by
    intro ht
    have hcent : a.val ∈ centralizer (V : Set G) := by
      intro v hv
      have hvf : (⟨v,hv⟩ : V) ∈ FixedPoints.subgroup A V := ht ▸ mem_top _
      have he := congrArg Subtype.val (hvf ⟨a.val,mem_map_of_mem L.subtype (mem_zpowers a)⟩)
      change a.val * v * a.val⁻¹ = v at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hkG : a.val ∈ L.pCoreIn 2 := d.centralizer_eq_core.le ⟨a.property,hcent⟩
    obtain ⟨b,hb,he⟩ := hkG
    have hab : b = a := Subtype.ext he
    have hcop := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 5) ⟨a,hab ▸ hb⟩
    rw [Subgroup.orderOf_mk,ha] at hcop
    norm_num at hcop
  have hf := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen
    hA d.module_card hm
  refine ⟨A,hAL,hA,bot_unique ?_⟩
  intro v hv
  have hvf : (⟨v,hv.1⟩ : V) ∈ FixedPoints.subgroup A V := by
    intro a
    apply Subtype.ext
    change a.val * v * a.val⁻¹ = v
    rw [hv.2 a a.property,mul_inv_cancel_right]
  have hvone := hf.le hvf
  exact congrArg Subtype.val hvone

theorem core_cyclic_derived_of_card_le_oneTwentyEight
    (d : Context T L V V₁ V₂ V₃)
    (hsmall : Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ 128) :
    IsCyclic (_root_.commutator (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))) := by
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  obtain ⟨A,hAL,hA,hfixed⟩ := d.exists_quintic_module_fixer_eq_bot
  have hAQ : A ≤ normalizer (Q : Set G) :=
    (hAL.trans le_sup_left).trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hcomm : ⁅Q,A⁆ ≤ V :=
    (commutator_mono le_rfl hAL).trans_eq
      (d.core_commutator_eq_module_of_card_le_oneTwentyEight hsmall)
  have hcardQ : Nat.card Q ≤ 128 := by
    change Nat.card (H.pCoreIn 2) ≤ 128
    rwa [pCoreIn,card_map_of_injective H.subtype_injective]
  have hcyc := cyclic_derived_of_central_sixteen_quintic Q V A
    (isPGroup_pCoreIn 2 H) d.chosen.le_core
    (le_centralizer_iff.mp d.chosen.core_centralizes) d.module_card hA hAQ
    hcomm hfixed hcardQ
  let a := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hQcyc : IsCyclic (_root_.commutator Q) := by
    apply ((_root_.commutator Q).equivMapOfInjective Q.subtype Q.subtype_injective).isCyclic.mpr
    rwa [map_subtype_commutator]
  let := hQcyc
  have hm : (_root_.commutator (pCore 2 H)).map a.toMonoidHom ≤ _root_.commutator Q := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let f : _root_.commutator (pCore 2 H) →* _root_.commutator Q :=
    (a.toMonoidHom.comp (_root_.commutator (pCore 2 H)).subtype).codRestrict _
      (fun x => hm (mem_map_of_mem a.toMonoidHom x.property))
  exact isCyclic_of_injective f
    (fun x y h => Subtype.ext (a.injective (congrArg Subtype.val h)))

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
