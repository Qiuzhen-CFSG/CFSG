module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.SylowLocalCore

/-!
# The actual rank-one Hall Cartan and the field unit group

Restrict the original Sylow subgroup to L. The odd Hall condition makes
the Cartan a complement in its literal normalizer. The quotient map
L → L/O₂(L) ≃ PSL₂(F) ≃ SL₂(F) has two-group kernel, so the existing
Borel diagonal projection identifies this same Cartan with Fˣ.
Consequently its order is 2ⁿ−1. No order or cyclicity premise is added.

Source: the Cartan in Aschbacher--Smith 5.1.6 and 5.2.2, printed
pp.631--633,647 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

theorem CartanPair.left_equiv_units {T : Sylow 2 G} {L H A B : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ Nonempty (A ≃* Fˣ) := by
  obtain ⟨P, hP⟩ :=
    (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) (sup_le L.le_normalizer hTL)
  have hP : (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using hP
  have hPlit : (P : Subgroup L) = (T : Subgroup G).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP, subgroupOf_map_subtype]
  have hN : (normalizer (P : Set L)).map L.subtype = localBorel T L := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [hPlit, ← localBorel_eq_map]
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  let D := A.subgroupOf L
  have hDN : D ≤ normalizer (P : Set L) := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hN, map_subgroupOf_eq_of_le hAL]
    exact c.left_le
  have hgen : (P : Subgroup L) ⊔ D = normalizer (P : Set L) := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, hP, map_subgroupOf_eq_of_le hAL, hN]
    exact c.left_sup_intersection hTL
  have hAo : ¬ 2 ∣ Nat.card A := by
    intro hd
    apply c.left_hall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ _ rfl
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
  have hDo : ¬ 2 ∣ Nat.card D := by
    simpa only [D, Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv] using hAo
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hd : Disjoint (P : Subgroup L) D := disjoint_of_coprime_natCard (by
    rw [hk]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hDo).pow_left k)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 L := by
    ext x
    exact e'.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨f⟩ := Matrix.SpecialLinearGroup.sylow_normalizer_complement_equiv_units
    q hq P (hker ▸ pCore_isPGroup.le_sylow_of_normal P) D hDN hd hgen
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ⟨(subgroupOfEquivOfLe hAL).symm.trans f⟩⟩

theorem CartanPair.left_card {T : Sylow 2 G} {L H A B : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nat.card A = 2 ^ n - 1 := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := c.left_equiv_units hpsl hTL
  rw [Nat.card_congr e.toEquiv, Nat.card_units, hF]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
