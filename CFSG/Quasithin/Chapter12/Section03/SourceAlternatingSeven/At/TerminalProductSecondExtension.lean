module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductSecondExtension
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductCentralizer

/-!
# TerminalProductSecondExtension at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductSecondExtension`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem pointSecondAction_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : Function.Surjective P.pointSecondAction :=
  Prod.snd_surjective.comp (P.pointBlockAction_surjective_at structural escape)

theorem component_intersection_second_trivial_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.K.subgroupOf P.pointNormalizer ≤ P.pointSecondAction.ker := by
  let N := P.pointNormalizer
  let A := P.K.subgroupOf N
  let : A.Normal := normal_subgroupOf_of_le_normalizer (inf_le_right.trans C.normalizes)
  let f := P.pointSecondAction.comp A.subtype
  have hres : primeToResidual 3 A ≤ f.ker := by
    intro a ha
    let X := P.K ⊓ normalizer (L : Set G)
    let j : A →* X := (N.subtype.comp A.subtype).codRestrict _ (fun x =>
      ⟨x.property,P.pointNormalizer_le_original_at structural x.val.property⟩)
    have hm := mem_map_of_mem X.subtype
      (map_primeToResidual_le_of_hom 3 j (mem_map_of_mem j ha))
    rw [← P.L1_eq_component_intersection_residual_at structural escape C,
      ← P.firstPointResidual_eq_L1_at structural escape C] at hm
    exact P.firstResidual_second_eq_one ⟨a.val,hm⟩
  have hc : Nat.Coprime 3 (Nat.card f.range) := by
    rw [← index_ker]
    exact (primeToResidual_index_coprime 3).coprime_dvd_right (index_dvd_of_le hres)
  have hd : Nat.card f.range ∣ 6 := by
    have hh := f.range.card_subgroup_dvd_card
    rw [Nat.card_perm,Nat.card_fin] at hh
    exact hh
  have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [pow_one] using hc.symm.dvd_of_dvd_mul_left hd)
  have hr : f.range = A.map P.pointSecondAction := by
    rw [MonoidHom.range_comp,range_subtype]
  let : f.range.Normal := hr ▸ Normal.map inferInstance _ (P.pointSecondAction_surjective_at structural escape)
  have hcore : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id _) Function.surjective_id
      (show IsPGroup 2 (MonoidHom.id (Equiv.Perm (Fin 3))).ker from by
        rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa only [MonoidHom.ker_id] using hh.symm
  have hle : f.range ≤ pCore 2 (Equiv.Perm (Fin 3)) := le_sSup ⟨inferInstance,hp⟩
  have hz : f.range = ⊥ := bot_unique (hle.trans hcore.le)
  intro n hn
  have hh : P.pointSecondAction n ∈ f.range := ⟨⟨n,hn⟩,rfl⟩
  exact mem_bot.mp (hz ▸ hh)

theorem exists_second_Y_action_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ∃ q : P.Y →* Equiv.Perm (Fin 3),
      P.K.subgroupOf P.Y ≤ q.ker ∧
      (∀ y : P.Y, (hy : (y : G) ∈ P.pointNormalizer) →
        q y = P.pointSecondAction ⟨y,hy⟩) := by
  obtain ⟨q,hq,hker,hagree⟩ := exists_sup_extension_of_inf_le_kernel
    P.pointNormalizer P.K (inf_le_right.trans C.normalizes)
    P.pointSecondAction (P.pointSecondAction_surjective_at structural escape)
    (P.component_intersection_second_trivial_at structural escape C)
  have hYN : P.Y ≤ P.pointNormalizer ⊔ P.K :=
    sup_le (sup_le le_sup_right ((P.L2_le_Le.trans (P.Le_le_pointNormalizer_at structural C)).trans le_sup_left))
      ((P.sylow_le_pointNormalizer_at structural).trans le_sup_left)
  refine ⟨q.comp (inclusion hYN),?_,?_⟩
  · intro y hy
    have hh : inclusion hYN y ∈ q.ker := by
      rw [hker]
      exact (show P.K ≤ P.K ⊔ P.pointSecondAction.ker.map P.pointNormalizer.subtype from le_sup_left) hy
    exact hh
  · intro y hy
    exact hagree ⟨y,hy⟩

theorem second_Y_action_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (q : P.Y →* Equiv.Perm (Fin 3))
    (hagree : ∀ y : P.Y, (hy : (y : G) ∈ P.pointNormalizer) →
      q y = P.pointSecondAction ⟨y,hy⟩) :
    (P.L2.subgroupOf P.Y).map q = alternatingGroup (Fin 3) := by
  have hL2N := P.L2_le_Le.trans (P.Le_le_pointNormalizer_at structural C)
  have he : (P.L2.subgroupOf P.Y).map q =
      (P.L2.subgroupOf P.pointNormalizer).map P.pointSecondAction := by
    ext a
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hL2N hy⟩,hy,(hagree y (hL2N hy)).symm⟩
    · rintro ⟨n,hn,rfl⟩
      exact ⟨⟨n,P.second_le_Y hn⟩,hn,hagree _ n.property⟩
  rw [he,pointSecondAction,← map_map,← P.secondPointResidual_eq_L2_at structural escape C,
    P.secondPointResidual_block_image_at structural escape]
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx.2
  · intro ha
    exact ⟨(1,a),⟨one_mem _,ha⟩,rfl⟩

theorem second_Y_action_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (q : P.Y →* Equiv.Perm (Fin 3))
    (hagree : ∀ y : P.Y, (hy : (y : G) ∈ P.pointNormalizer) →
      q y = P.pointSecondAction ⟨y,hy⟩) : Function.Surjective q := by
  have hA : alternatingGroup (Fin 3) ≤ q.range := by
    rw [← P.second_Y_action_image_at structural escape C q hagree]
    exact map_le_range _ _
  obtain ⟨j,hj,hj2,hj1⟩ := P.exists_thompson_second_involution_at structural escape
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ h => h.1
  let t : P.Y := ⟨j,P.sylow_le_Y (hJT hj)⟩
  have ht : q t = (P.pointBlockAction j).2 := hagree t j.property
  have htodd : q t ∉ alternatingGroup (Fin 3) := by
    rw [ht]
    intro h
    let a : alternatingGroup (Fin 3) := ⟨(P.pointBlockAction j).2,h⟩
    have hd3 : orderOf a ∣ 3 := by
      have hh := orderOf_dvd_natCard a
      rw [nat_card_alternatingGroup,Nat.card_fin] at hh
      exact hh
    have hd2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext hj2)
    have he : a = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 2) hd3 hd2)
    exact hj1 (congrArg Subtype.val he)
  intro a
  by_cases ha : a ∈ alternatingGroup (Fin 3)
  · exact hA ha
  · have ham : a * (q t)⁻¹ ∈ alternatingGroup (Fin 3) := by
      rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
      exact iff_of_false ha htodd
    obtain ⟨x,hx⟩ := hA ham
    exact ⟨x*t,by rw [map_mul,hx,inv_mul_cancel_right]⟩

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

