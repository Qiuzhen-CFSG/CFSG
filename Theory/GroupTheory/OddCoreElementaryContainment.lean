module
public import Theory.GroupTheory.OddCoreElementaryTwoCentralizers
public import Theory.GroupTheory.CentralTwoQuotientOddCore
public import Theory.ElementaryAbelian.Injective

/-!
# Odd-core containment from an elementary two-group

A noncyclic elementary two-group contains a four-group. Generation by its
three involution centralizers puts any normalized odd subgroup in a prescribed
local subgroup. If that local subgroup has trivial odd core, normality then
makes the ambient odd core trivial as well. For a normal subgroup W of the
elementary group U, W is central in the normal closure of U. Central
2-quotient descent therefore retains trivial odd core after quotienting
that normal closure by the entire W.

This is the generation-by-centralizers step used in Aschbacher–Smith F.4.42,
printed p.296, with no ambient solvability assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Centralizers of the nonidentity elements of an elementary two-group
absorb every odd subgroup it normalizes. -/
theorem odd_le_of_elementary_centralizers
    (P E X : Subgroup G) [IsElementaryAbelian 2 E]
    (hodd : Odd (Nat.card P)) (hE : 2 < Nat.card E)
    (hEP : E ≤ normalizer (P : Set G))
    (hC : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ X) : P ≤ X := by
  have square (e : E) : e ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) e
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (1 : E)
  obtain ⟨b,hb,hba⟩ := ENat.exists_ne_ne_of_three_le (α := E)
    (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast (by omega : 3 ≤ Nat.card E)) 1 a
  have hab : a*b ≠ 1 := by
    intro he
    apply hba
    exact (eq_inv_of_mul_eq_one_right he).trans
      (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using square a))
  let f : E →* normalizer (P : Set G) := inclusion hEP
  apply le_of_three_odd_centralizers P X hodd (f a) (f b)
    (by rw [←map_pow,square,map_one]) (by rw [←map_pow,square,map_one])
    ((show Commute a b from (IsMulCommutative.is_comm (M := E)).comm a b).map f)
  intro e he
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl
  · exact inf_le_right.trans (hC a a.property (fun hh => ha (Subtype.ext hh)))
  · exact inf_le_right.trans (hC b b.property (fun hh => hb (Subtype.ext hh)))
  · exact inf_le_right.trans (hC (a*b) (a*b).property (fun hh => hab (Subtype.ext hh)))

/-- Absorption into a subgroup with trivial odd core kills the ambient odd core. -/
theorem oddCore_eq_bot_of_elementary_centralizers
    (E X : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : 2 < Nat.card E) (hX : pPrimeCore 2 X = ⊥)
    (hC : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ X) :
    pPrimeCore 2 G = ⊥ := by
  let O := pPrimeCore 2 G
  have hOX : O ≤ X := odd_le_of_elementary_centralizers O E X
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hE le_normalizer_of_normal hC
  have hi : O.subgroupOf X ≤ pPrimeCore 2 X := le_sSup ⟨inferInstance,
    pPrimeCore_coprime_card.of_dvd_right (O.card_comap_dvd_of_injective X.subtype X.subtype_injective)⟩
  apply bot_unique
  intro a ha
  have hh := hi (show (⟨a,hOX ha⟩ : X) ∈ O.subgroupOf X from ha)
  rw [hX,mem_bot] at hh
  exact mem_bot.mpr (congrArg Subtype.val hh)

/-- Quotient the normal closure of an elementary two-group by a normal
subgroup of that elementary group. Its odd core stays trivial because the
kernel is central in the unquotiented normal closure. -/
theorem oddCore_normalClosure_quotient_eq_bot
    (U W : Subgroup G) [IsElementaryAbelian 2 U] [W.Normal]
    (hWU : W ≤ U) (hodd : pPrimeCore 2 G = ⊥) :
    pPrimeCore 2 (normalClosure ((U.map (QuotientGroup.mk' W)) : Set (G ⧸ W))) = ⊥ := by
  let L := normalClosure (U : Set G)
  let q := QuotientGroup.mk' W
  let B := normalClosure (U.map q : Set (G ⧸ W))
  have hWL : W ≤ L := hWU.trans le_normalClosure
  have hUL : U ≤ L := le_normalClosure
  have hLC : L ≤ centralizer (W : Set G) := by
    apply normalClosure_le_normal
    intro u hu w hw
    exact congrArg Subtype.val (mul_comm (⟨w,hWU hw⟩ : U) ⟨u,hu⟩)
  have hOL : pPrimeCore 2 L = ⊥ := by
    apply map_injective L.subtype_injective
    rw [map_bot]
    exact bot_unique ((pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 L).trans_eq hodd)
  have hLB : L.map q = B := by
    change (normalClosure (U : Set G)).map q = normalClosure (U.map q : Set (G ⧸ W))
    rw [map_normalClosure _ q (QuotientGroup.mk'_surjective W)]
    rfl
  let f : L →* B := (q.comp L.subtype).codRestrict B (fun a => hLB ▸ mem_map_of_mem q a.property)
  have hf : Function.Surjective f := by
    intro b
    have hb : b.val ∈ L.map q := hLB.symm ▸ b.property
    obtain ⟨a,ha,he⟩ := hb
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  have hk : f.ker = W.subgroupOf L := by
    ext a
    change f a = 1 ↔ a.val ∈ W
    rw [←Subtype.val_inj]
    exact QuotientGroup.eq_one_iff a.val
  have hkc : f.ker ≤ center L := by
    intro a ha
    apply mem_center_iff.mpr
    intro b
    have haW : a ∈ W.subgroupOf L := hk ▸ ha
    exact Subtype.ext (hLC b.property a.val haW).symm
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact ((IsElementaryAbelian.isPGroup 2 U).to_le hWU).comap_subtype
  have ho := pPrimeCore_quotient_eq_bot_of_central_two_subgroup f.ker hkc hkp hOL
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  rw [←pPrimeCore_map_iso 2 e,ho,map_bot]

end Subgroup
