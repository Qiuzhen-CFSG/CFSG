module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The actual binary weak BN-pair

Simultaneously conjugate the point and line stabilizers of the standard
incident flag in SL₃(2). Their intersection is a Sylow two-subgroup and they
generate the group. The ambient two-core is trivial, so no normal subgroup
lies in the intersection. Actual S₄ identifications give self-centralizing
four-element two-cores and quotients isomorphic to SL₂(2). The local Sylow
normalizers have order eight: a larger normalizer would make the Sylow normal
and force it into the four-element core.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), definition on printed pp.827--828, with Pᵢ* = Pᵢ.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Matrix.PSL3Two

theorem modelBorel_eq_map (g : SL) :
    modelBorel g = borelSL.map (MulAut.conj g).toMonoidHom := by
  exact (map_inf _ _ _ (MulAut.conj g).injective).symm

noncomputable def modelBorelSylow (g : SL) : Sylow 2 SL :=
  let B : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  B.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective

theorem coe_modelBorelSylow (g : SL) :
    (modelBorelSylow g : Subgroup SL) = modelBorel g :=
  (modelBorel_eq_map g).symm

theorem card_modelBorel (g : SL) : Nat.card (modelBorel g) = 8 := by
  rw [modelBorel_eq_map]
  exact (Nat.card_congr ((MulAut.conj g).subgroupMap borelSL).toEquiv).symm.trans
    card_borelSL

noncomputable def modelParabolicEquivSymmetric (g : SL) (i : Bool) :
    modelParabolic g i ≃* Equiv.Perm (Fin 4) := by
  cases i
  · exact ((MulAut.conj g).subgroupMap pointParabolicSL).symm.trans
      MarkedAutomorphisms.pointEquivSymmetric
  · exact ((MulAut.conj g).subgroupMap lineParabolicSL).symm.trans
      MarkedAutomorphisms.lineEquivSymmetric

theorem card_modelParabolic (g : SL) (i : Bool) : Nat.card (modelParabolic g i) = 24 := by
  rw [Nat.card_congr (modelParabolicEquivSymmetric g i).toEquiv, Nat.card_perm, Nat.card_fin]
  decide

theorem modelParabolic_generation (g : SL) :
    modelParabolic g false ⊔ modelParabolic g true = ⊤ := by
  have h : pointParabolicSL ⊔ lineParabolicSL = ⊤ := by
    apply isCoatom_pointParabolicSL.2
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    exact lineParabolicSL_not_le_point (he ▸ le_sup_right)
  change pointParabolicSL.map _ ⊔ lineParabolicSL.map _ = ⊤
  rw [← Subgroup.map_sup, h, map_top_of_surjective _ (MulAut.conj g).surjective]

theorem modelParabolic_borel_le (g : SL) (i : Bool) :
    modelBorel g ≤ modelParabolic g i := by
  cases i
  · exact inf_le_left
  · exact inf_le_right

theorem modelBorel_faithful (g : SL) (N : Subgroup SL) (hN : N.Normal)
    (hNB : N ≤ modelBorel g) : N = ⊥ := by
  let := hN
  have hp : IsPGroup 2 N := (modelBorelSylow g).isPGroup'.to_le
    ((coe_modelBorelSylow g).symm ▸ hNB)
  have hle : N ≤ pCore 2 SL := le_sSup ⟨hN, hp⟩
  have hc : pCore 2 SL = ⊥ := by
    have he := pCore_map_iso 2 equiv
    rw [pCore_two_PSL_eq_bot] at he
    exact (map_eq_bot_iff_of_injective _ equiv.injective).mp he
  exact le_bot_iff.mp (hc ▸ hle)

private theorem sylow_normalizer_of_cards {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hG : Nat.card G = 24) (hS : Nat.card S = 8)
    (hc : Nat.card (pCore 2 G) = 4) : normalizer (S : Set G) = (S : Subgroup G) := by
  have hi : (S : Subgroup G).index = 3 := by
    have h := (S : Subgroup G).index_mul_card
    rw [hG, hS] at h
    omega
  have hd := index_dvd_of_le (S : Subgroup G).le_normalizer
  rw [hi] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
  · have hn := normalizer_eq_top_iff.mp (index_eq_one.mp h)
    have hle : (S : Subgroup G) ≤ pCore 2 G := le_sSup ⟨hn, S.isPGroup'⟩
    have hd := card_dvd_of_le hle
    rw [hS, hc] at hd
    norm_num at hd
  · have hm := relIndex_mul_index (S : Subgroup G).le_normalizer
    rw [hi, h] at hm
    have hr : (S : Subgroup G).relIndex (normalizer (S : Set G)) = 1 := by
      change (S : Subgroup G).relIndex (normalizer (S : Set G)) * 3 = 3 at hm
      omega
    exact le_antisymm (relIndex_eq_one.mp hr) (S : Subgroup G).le_normalizer

theorem modelParabolic_borel_normalizer (g : SL) (i : Bool) :
    ∃ S : Sylow 2 (modelParabolic g i),
      (normalizer (S : Set (modelParabolic g i))).map (modelParabolic g i).subtype =
        modelBorel g := by
  have hB : (modelBorelSylow g : Subgroup SL) ≤ modelParabolic g i := by
    rw [coe_modelBorelSylow]
    exact modelParabolic_borel_le g i
  let S := (modelBorelSylow g).subtype hB
  have hc : Nat.card S = 8 := by
    change Nat.card ((modelBorelSylow g : Subgroup SL).subgroupOf (modelParabolic g i)) = 8
    rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv, coe_modelBorelSylow,
      card_modelBorel]
  refine ⟨S, ?_⟩
  rw [sylow_normalizer_of_cards S (card_modelParabolic g i) hc
    (ParabolicCoreModel.core_data (modelParabolicEquivSymmetric g i)).2]
  exact (map_subgroupOf_eq_of_le hB).trans (coe_modelBorelSylow g)

theorem binaryWeakBN (g : SL) : BinaryWeakBN g where
  generation := modelParabolic_generation g
  faithful := modelBorel_faithful g
  local_characteristic i :=
    ParabolicCoreModel.core_selfCentralizing (modelParabolicEquivSymmetric g i)
  rank_one i := by
    obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    exact ⟨(ParabolicCoreModel.coreQuotientEquiv (modelParabolicEquivSymmetric g i)).trans e.symm⟩
  borel_normalizer := modelParabolic_borel_normalizer g
end CFSG.Quasithin.ChapterC.BinaryMS.MS93
