module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductMarkedEmbedding
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductSecondExtension

/-!
# TerminalProductMarkedEmbedding at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductMarkedEmbedding`, with structural
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

private theorem three_part_kernel_twoGroup_at {H : Type*} [Group H] [Finite H]
    (q : H →* Equiv.Perm (Fin 3)) (hq : Function.Surjective q)
    (hcard : ∃ n, Nat.card H ∣ 3 * 2^n) : IsPGroup 2 q.ker := by
  obtain ⟨n,hn⟩ := hcard
  have hc : q.ker.index = 6 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hq,Nat.card_congr topEquiv.toEquiv,
      Nat.card_perm,Nat.card_fin]
    decide
  have hd : 3 * Nat.card q.ker ∣ 3 * 2^n := by
    apply dvd_trans ?_ hn
    rw [←q.ker.card_mul_index,hc]
    exact ⟨2,by omega⟩
  exact IsPGroup.of_card_dvd_pow ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hd)

theorem marked_action_twoKernel_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (q : P.Y →* Equiv.Perm (Fin 3)) (hq : Function.Surjective q)
    (hK : P.K.subgroupOf P.Y ≤ q.ker) :
    IsPGroup 2 ((P.firstYAction C).prod q).ker := by
  let K := P.K.subgroupOf P.Y
  let : K.Normal := normal_subgroupOf_of_le_normalizer (P.Y_normalizes_component C)
  let d := QuotientGroup.lift K q hK
  have hd : Function.Surjective d := QuotientGroup.lift_surjective_of_surjective K q hq hK
  have hdp : IsPGroup 2 d.ker := three_part_kernel_twoGroup_at d hd
    (P.quotient_component_card_bound_at structural escape C)
  let B := ((P.firstYAction C).prod q).ker
  let f := (QuotientGroup.mk' K).comp B.subtype
  have him : f.range ≤ d.ker := by
    rintro a ⟨b,rfl⟩
    exact congrArg Prod.snd b.property
  have hfp : IsPGroup 2 f.ker := by
    let j : f.ker →* P.K.pCoreIn 2 :=
      (P.Y.subtype.comp (B.subtype.comp f.ker.subtype)).codRestrict _ (fun x => by
        apply P.component_inf_quotientCentralizer_le_core C
        refine ⟨(QuotientGroup.eq_one_iff x.val.val).mp x.property,?_⟩
        exact (P.firstYAction_mem_ker C x.val.val).mp (congrArg Prod.fst x.val.property))
    exact (isPGroup_pCoreIn 2 P.K).of_injective j (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : P.K.pCoreIn 2 => (x : G)) h)
  have hp := (hdp.to_le him).comap_of_ker_isPGroup f hfp
  rw [MonoidHom.comap_range_self] at hp
  exact hp.of_equiv (topEquiv : (⊤ : Subgroup B) ≃* B)

def secondYAction_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Y →* Equiv.Perm (Fin 3) :=
  Classical.choose (P.exists_second_Y_action_at structural escape C)

theorem secondYAction_component_trivial_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.K.subgroupOf P.Y ≤ (P.secondYAction_at structural escape C).ker :=
  (Classical.choose_spec (P.exists_second_Y_action_at structural escape C)).1

theorem secondYAction_agrees_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (y : P.Y) (hy : (y : G) ∈ P.pointNormalizer) :
    P.secondYAction_at structural escape C y = P.pointSecondAction ⟨y,hy⟩ :=
  (Classical.choose_spec (P.exists_second_Y_action_at structural escape C)).2 y hy

theorem secondYAction_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Function.Surjective (P.secondYAction_at structural escape C) :=
  P.second_Y_action_surjective_at structural escape C _ (P.secondYAction_agrees_at structural escape C)

theorem secondYAction_second_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.L2.subgroupOf P.Y).map (P.secondYAction_at structural escape C) = alternatingGroup (Fin 3) :=
  P.second_Y_action_image_at structural escape C _ (P.secondYAction_agrees_at structural escape C)

def markedProductAction_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Y →* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) :=
  (P.firstYAction C).prod (P.secondYAction_at structural escape C)

theorem markedProductAction_twoKernel_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    IsPGroup 2 (P.markedProductAction_at structural escape C).ker :=
  P.marked_action_twoKernel_at structural escape C _
    (P.secondYAction_surjective_at structural escape C) (P.secondYAction_component_trivial_at structural escape C)

theorem markedProductAction_ker_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.markedProductAction_at structural escape C).ker = pCore 2 P.Y := by
  have hlecore : (P.markedProductAction_at structural escape C).ker ≤ pCore 2 P.Y :=
    le_sSup ⟨inferInstance,P.markedProductAction_twoKernel_at structural escape C⟩
  apply le_antisymm hlecore
  rw [markedProductAction_at,MonoidHom.ker_prod]
  apply le_inf (P.twoCore_le_firstYAction_ker C)
  let q := P.secondYAction_at structural escape C
  let I := (pCore 2 P.Y).map q
  let : I.Normal := Normal.map inferInstance q (P.secondYAction_surjective_at structural escape C)
  have hle : I ≤ pCore 2 (Equiv.Perm (Fin 3)) := le_sSup ⟨inferInstance,pCore_isPGroup.map q⟩
  have hz : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id _) Function.surjective_id
      (show IsPGroup 2 (MonoidHom.id (Equiv.Perm (Fin 3))).ker from by
        rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa only [MonoidHom.ker_id] using hh.symm
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hle.trans hz.le))

theorem markedProductAction_first_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.K.subgroupOf P.Y).map (P.markedProductAction_at structural escape C) =
      (alternatingGroup (Fin 5)).prod ⊥ := by
  apply le_antisymm
  · rintro a ⟨y,hy,rfl⟩
    refine ⟨?_,P.secondYAction_component_trivial_at structural escape C hy⟩
    exact (P.firstYAction_component_image C).le (mem_map_of_mem _ hy)
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨y,hy,he⟩ := (P.firstYAction_component_image C).symm ▸ ha
    refine ⟨y,hy,Prod.ext he ?_⟩
    exact (P.secondYAction_component_trivial_at structural escape C hy).trans (mem_bot.mp hb).symm

theorem markedProductAction_second_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.L2.subgroupOf P.Y).map (P.markedProductAction_at structural escape C) =
      (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)) := by
  apply le_antisymm
  · rintro a ⟨y,hy,rfl⟩
    refine ⟨P.firstYAction_second_trivial C hy,?_⟩
    exact (P.secondYAction_second_image_at structural escape C).le (mem_map_of_mem _ hy)
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨y,hy,he⟩ := (P.secondYAction_second_image_at structural escape C).symm ▸ hb
    refine ⟨y,hy,Prod.ext ?_ he⟩
    exact (P.firstYAction_second_trivial C hy).trans (mem_bot.mp ha).symm

def markedQuotientEmbedding_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.Y ⧸ pCore 2 P.Y) →* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) :=
  QuotientGroup.lift _ (P.markedProductAction_at structural escape C)
    (P.markedProductAction_ker_at structural escape C).ge

theorem markedQuotientEmbedding_apply_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) (y : P.Y) :
    P.markedQuotientEmbedding_at structural escape C (QuotientGroup.mk' (pCore 2 P.Y) y) =
      P.markedProductAction_at structural escape C y := rfl

theorem markedQuotientEmbedding_injective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Function.Injective (P.markedQuotientEmbedding_at structural escape C) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro y hy
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P.Y) y
  have hx : x ∈ (P.markedProductAction_at structural escape C).ker := hy
  rw [P.markedProductAction_ker_at structural escape C] at hx
  exact (QuotientGroup.eq_one_iff x).mpr hx

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

