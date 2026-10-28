module
public import Theory.GroupTheory.IndexTwoFixedSylowComplement
public import Theory.GroupTheory.CentralQuotientOddObstruction
public import Theory.GroupTheory.PPrimeCoreNormalComplement
/-!
# A small abelian Sylow determines a quotient centralizer

In a quotient by a central two-subgroup, suppose the inverse image admits
no nontrivial odd subgroup normalized by E. Let k be an involution outside
the image of E, whose centralizer has an abelian Sylow of order at most
sixteen. If E has image of order four in that Sylow and the Sylow normalizer
fixes it pointwise, transfer gives a normal two-complement. The odd-subgroup
obstruction kills this complement, so the full centralizer is the Sylow.

This is the transfer and odd-complement calculation in Parrott (1972),
printed p.683. The actual quotient map and centralizer embedding are retained.
The source-specific construction of the small Sylow is a separate premise.
-/

open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G]

public theorem quotient_centralizer_eq_sylow_of_small_abelian
    (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hkp : IsPGroup 2 f.ker)
    (E : Subgroup G)
    (hodd : ∀ O : Subgroup G, Odd (Nat.card O) → E ≤ normalizer (O : Set G) → O = ⊥)
    (k : H) (hk2 : orderOf k = 2) (hEc : E.map f ≤ centralizer ({k} : Set H))
    (P : Sylow 2 (centralizer ({k} : Set H))) [IsMulCommutative P]
    (hPcard : Nat.card P ≤ 16)
    (hEP : E.map f ≤ (P : Subgroup (centralizer ({k} : Set H))).map
      (centralizer ({k} : Set H)).subtype)
    (hEcard : Nat.card (E.map f) = 4)
    (hEN : normalizer (P : Set (centralizer ({k} : Set H))) ≤
      centralizer ((E.map f).subgroupOf (centralizer ({k} : Set H)) : Set (centralizer ({k} : Set H))))
    (hkP : (⟨k, mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set H)) ∈ P)
    (hkE : k ∉ E.map f) :
    centralizer ({k} : Set H) =
      (P : Subgroup (centralizer ({k} : Set H))).map (centralizer ({k} : Set H)).subtype := by
  let : Finite H := Finite.of_surjective f hf
  let C := centralizer ({k} : Set H)
  let kC : C := ⟨k, mem_centralizer_singleton_iff.mpr rfl⟩
  let A := (E.map f).subgroupOf C
  have hAP : A ≤ P := by
    intro a ha
    obtain ⟨p, hp, he⟩ := hEP ha
    exact (C.subtype_injective he) ▸ hp
  have hAc : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEc).toEquiv).trans hEcard
  have hkc : kC ∈ center C := mem_center_iff.mpr (fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp c.property))
  have hc := P.hasNormalTwoComplement_of_order_le_sixteen hPcard A hAP hAc hEN
    kC hkP hkc ((orderOf_coe kC).symm.trans hk2) hkE
  have hb : pPrimeCore 2 C = ⊥ := f.quotient_centralizer_oddCore_eq_bot hf hk hkp E hodd k hEc
  have hp := isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 C hc
  have hpC : IsPGroup 2 C := hp.of_injective (QuotientGroup.mk' (pPrimeCore 2 C))
    ((MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' (pPrimeCore 2 C))).mp (by rw [QuotientGroup.ker_mk', hb]))
  have hPt : (P : Subgroup C) = ⊤ := (P.is_maximal' (hpC.to_subgroup ⊤) le_top).symm
  rw [hPt, ← MonoidHom.range_eq_map, range_subtype]
end MonoidHom
