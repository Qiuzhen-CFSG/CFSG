module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.ChapterC.Section01.BlockCentralQuotient
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.Quasithin.EvenCharacteristic

/-!
# Transporting the original short group and natural module

Group equivalences carry the literal two-core, its commutator layer and its
central fixed subgroup. The short-group normal interval and the natural
module model therefore transport together. This supplies the inclusion-image
transport in the solvable C.1.29 argument without selecting a new block.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

omit [Finite A] [Finite B] in
theorem blockU_map_equiv (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective e.toMonoidHom e.surjective]
  rfl

omit [Finite A] [Finite B] in
private theorem center_map_equiv (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (centerCongr e ⟨a, ha⟩).property
  · intro hb
    exact ⟨e.symm b, (centerCongr e.symm ⟨b, hb⟩).property, e.apply_symm_apply b⟩

theorem isShort_of_equiv (e : A ≃* B) (h : IsShort A) : IsShort B := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (blockU A) := h.elementary
  have hu := blockU_map_equiv e
  have hz := center_map_equiv e
  have hui : (blockU A ⊓ center A).map e.toMonoidHom = blockU B ⊓ center B := by
    rw [map_inf _ _ _ e.injective, hu, hz]
  let eQ := QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)
  refine ⟨inferInstance, h.twoPerfect.of_surjective e.toMonoidHom e.surjective,
    ?_, ?_, ?_, ?_, ?_⟩
  · apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp h.fitting)
  · rw [← hu]
    exact IsElementaryAbelian.map e.toMonoidHom
  · rw [← hu, ← pCore_map_iso 2 e,
      ← Theory.Quasithin.map_centralizer e (pCore 2 A)]
    exact map_mono h.central
  · rcases h.quotient with hq | hq
    · let : IsQuasisimple (A ⧸ pCore 2 A) := hq
      exact Or.inl (IsQuasisimple.of_mulEquiv eQ)
    · exact Or.inr ((Nat.card_congr eQ.toEquiv).symm.trans hq)
  · refine ⟨?_, ?_⟩
    · rw [← hui, ← hu]
      exact (map_lt_map_iff_of_injective e.injective).mpr h.irreducible.1
    · intro N hN hlo hhi
      let : N.Normal := hN
      have hcU : (blockU B).comap e.toMonoidHom = blockU A := by
        rw [← hu, comap_map_eq_self_of_injective e.injective]
      have hcI : (blockU B ⊓ center B).comap e.toMonoidHom = blockU A ⊓ center A := by
        rw [← hui, comap_map_eq_self_of_injective e.injective]
      have hlo' : blockU A ⊓ center A ≤ N.comap e.toMonoidHom := by
        rw [← hcI]
        exact comap_mono hlo
      have hhi' : N.comap e.toMonoidHom ≤ blockU A := by
        rw [← hcU]
        exact comap_mono hhi
      rcases h.irreducible.2 (N.comap e.toMonoidHom) inferInstance hlo' hhi' with he | he
      · left
        have hm := congrArg (Subgroup.map e.toMonoidHom) he
        simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective, hui] using hm
      · right
        have hm := congrArg (Subgroup.map e.toMonoidHom) he
        simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective, hu] using hm

theorem isAlternatingBlock_of_equiv (e : A ≃* B) {n : ℕ}
    (h : IsAlternatingBlock A n) : IsAlternatingBlock B n := by
  refine ⟨h.1, isShort_of_equiv e h.2.1, ?_⟩
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := h.2.2
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have hp : IsPGroup 2 e.toMonoidHom.ker := by rw [hk]; exact IsPGroup.of_bot
  obtain ⟨m'⟩ := BlockModuleModel.exists_of_central_two_quotient e.toMonoidHom e.surjective
    h.2.1.twoPerfect hp (hk ▸ bot_le) ρ m
  exact ⟨ρ, ⟨m'⟩, hρ⟩

end CFSG.Quasithin.ChapterC.RankOne.Solvable
