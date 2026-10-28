module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Sylow and unique-maximal facts for the reduced chi-zero block

The full two-core lies in every Sylow subgroup, so its quotient controls
Sylow overgroups. The A₃, A₅ and even-field SL₂ calculations are the pure
quotient argument from E.6 BlockSelection/SylowMaximal, localized here to
avoid importing that later source configuration into C.5. The normal
extension then gives the actual Sylow and unique-maximal statements on KT₁.

Source: Aschbacher–Smith, C.5.9, printed p.161; C.1.12–13, pp.124–125.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
private theorem sylow_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : ∀ S : Sylow 2 A, Order.HasUniqueMaximalOver (S : Subgroup A) ⊤)
    (S : Sylow 2 B) : Order.HasUniqueMaximalOver (S : Subgroup B) ⊤ := by
  have hh := (h (S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective)).map e.mapSubgroup
  rw [OrderIso.map_top] at hh
  change Order.HasUniqueMaximalOver
    (((S : Subgroup B).map e.symm.toMonoidHom).map e.toMonoidHom) ⊤ at hh
  simpa [map_map] using hh

private theorem a3_sylow (S : Sylow 2 (alternatingGroup (Fin 3))) :
    Order.HasUniqueMaximalOver (S : Subgroup (alternatingGroup (Fin 3))) ⊤ := by
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hScard : Nat.card S = 1 := S.isPGroup'.card_eq_or_dvd.resolve_right (by
    intro htwo
    have hh := htwo.trans (card_subgroup_dvd_card (S : Subgroup (alternatingGroup (Fin 3))))
    rw [hcard] at hh
    norm_num at hh)
  have hS : (S : Subgroup (alternatingGroup (Fin 3))) = ⊥ := card_eq_one.mp hScard
  rw [hS]
  have hbot : (⊥ : Subgroup (alternatingGroup (Fin 3))) ≠ ⊤ := by
    intro he
    have hh := congrArg (fun K : Subgroup (alternatingGroup (Fin 3)) => Nat.card K) he
    rw [card_bot, card_top, hcard] at hh
    omega
  have hp : Fact (Nat.Prime (Nat.card (alternatingGroup (Fin 3)))) := ⟨by rw [hcard]; decide⟩
  have hc : (⊥ : Subgroup (alternatingGroup (Fin 3))) ⋖ ⊤ := by
    apply IsCoatom.covBy_top
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hbot, fun K hK _ => ?_⟩
    exact le_of_eq (K.eq_bot_or_eq_top_of_prime_card.resolve_right hK)
  refine ⟨lt_top_iff_ne_top.mpr hbot, ⊥, ⟨le_rfl, hc⟩, ?_⟩
  intro K hK
  exact K.eq_bot_or_eq_top_of_prime_card.resolve_right hK.2.ne

private theorem a5_sylow (S : Sylow 2 (alternatingGroup (Fin 5))) :
    Order.HasUniqueMaximalOver (S : Subgroup (alternatingGroup (Fin 5))) ⊤ := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact sylow_equiv ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).trans e)
    (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2) S

/-- Intrinsic Sylow unique maximality for every chi-zero block, with its full two-core retained. -/
theorem chiZeroBlock_sylow_hasUniqueMaximalOver {L : Type*} [Group L] [Finite L]
    (h : IsChiZeroBlock L) (S : Sylow 2 L) :
    Order.HasUniqueMaximalOver (S : Subgroup L) ⊤ := by
  let π := QuotientGroup.mk' (pCore 2 L)
  apply hasUniqueMaximalOver_of_surjective π (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  · let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
    change Order.HasUniqueMaximalOver (Sb : Subgroup (L ⧸ pCore 2 L)) ⊤
    rcases h with ⟨n, _, _, F, _, _, hF, _, hm⟩ | h | h
    · obtain ⟨e⟩ := hm.quotient_iso
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
        simpa only [Nat.card_eq_fintype_card] using hF)
      exact sylow_equiv e.symm (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2) Sb
    · obtain ⟨e⟩ := h.2.2.quotient_iso
      exact sylow_equiv e.symm a3_sylow Sb
    · obtain ⟨e⟩ := h.2.2.quotient_iso
      exact sylow_equiv e.symm a5_sylow Sb


variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A two-subgroup containing the marked Sylow intersection has exactly that intersection. -/
theorem sylow_block_intersection (K T : Subgroup G) (hT : IsPGroup 2 T)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ T) :
    K ⊓ T = (P : Subgroup K).map K.subtype := by
  have hp : (P : Subgroup K) ≤ T.subgroupOf K := fun p hp => hP (mem_map_of_mem K.subtype hp)
  have he := P.is_maximal' (hT.comap_subtype (K := K)) hp
  change T.subgroupOf K = (P : Subgroup K) at he
  rw [inf_comm,← subgroupOf_map_subtype,he]

/-- The reduced normal extension has a unique maximal overgroup of its two-subgroup. -/
theorem chiZeroBlock_extension_unique (K T : Subgroup G) (hK : IsChiZeroBlock K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ T) :
    Order.HasUniqueMaximalOver T (K ⊔ T) := by
  have hu := hasUniqueMaximalOver_map_subtype (chiZeroBlock_sylow_hasUniqueMaximalOver hK P)
  rw [← sylow_block_intersection K T hT P hP] at hu
  exact hasUniqueMaximalOver_sup_of_normalizes hn hu

/-- The same actual two-subgroup is Sylow in the reduced normal extension. -/
theorem chiZeroBlock_extension_sylow (K T : Subgroup G) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ T) :
    ∃ Q : Sylow 2 (K ⊔ T : Subgroup G), (Q : Subgroup (K ⊔ T : Subgroup G)).map
      (K ⊔ T).subtype = T := by
  have he := sylow_block_intersection K T hT P hP
  have hodd : ¬ 2 ∣ (K ⊓ T).relIndex K := by
    rw [he]
    have hh := relIndex_map_map_of_injective (P : Subgroup K) ⊤ K.subtype_injective
    simp only [← MonoidHom.range_eq_map,K.range_subtype,relIndex_top_right] at hh
    rw [hh]
    exact P.not_dvd_index
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes K T hn
  have hcK := relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ T) K bot_le inf_le_left
  have hcT := relIndex_mul_relIndex (⊥ : Subgroup G) T (K ⊔ T) bot_le le_sup_right
  simp only [relIndex_bot_left] at hcK hcT
  have hi : T.relIndex (K ⊔ T) = (K ⊓ T).relIndex K := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.card_pos (α := ↥(K ⊓ T))) (Nat.card_pos (α := T)))
    calc
      (Nat.card ↥(K ⊓ T) * Nat.card T) * T.relIndex (K ⊔ T) =
          Nat.card ↥(K ⊓ T) * (Nat.card T * T.relIndex (K ⊔ T)) := by ring
      _ = Nat.card ↥(K ⊓ T) * Nat.card ↥(K ⊔ T) := by rw [hcT]
      _ = Nat.card K * Nat.card T := hcard.symm
      _ = (Nat.card ↥(K ⊓ T) * (K ⊓ T).relIndex K) * Nat.card T := by rw [hcK]
      _ = (Nat.card ↥(K ⊓ T) * Nat.card T) * (K ⊓ T).relIndex K := by ring
  refine ⟨(hT.comap_subtype (K := K ⊔ T)).toSylow (show ¬ 2 ∣ T.relIndex (K ⊔ T) by rw [hi]; exact hodd),?_⟩
  exact map_subgroupOf_eq_of_le (show T ≤ K ⊔ T from le_sup_right)
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
