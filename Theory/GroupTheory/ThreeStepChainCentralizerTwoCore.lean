module

public import Theory.GroupTheory.ChainCentralizerTwoCore

/-!
# Three-step chain stabilizers in a group of characteristic two

Suppose Q is a normal self-centralizing two-subgroup. The stabilizer acting
trivially on Q/F, F/U and U is a normal two-subgroup. Its two-residual D
satisfies [Q,D,D]=[Q,D]; applying this identity twice to the three layers
shows [Q,D]=1. Self-centralization then makes D a two-group, hence trivial.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem three_step_chain_centralizer_le_twoCore
    (Q F U : Subgroup G) [Q.Normal] [F.Normal] [U.Normal]
    (hQ : IsPGroup 2 Q) (hself : centralizer (Q : Set G) ≤ Q) :
    (centralizer (U : Set G) ⊓ commutatorPreimage ⊤ F U) ⊓
      commutatorPreimage ⊤ Q F ≤ pCore 2 G := by
  let H := (centralizer (U : Set G) ⊓ commutatorPreimage ⊤ F U) ⊓
    commutatorPreimage ⊤ Q F
  have hnFU : (commutatorPreimage (⊤ : Subgroup G) F U).Normal := by
    rw [←normalizer_eq_top_iff]
    exact top_unique (commutatorPreimage_normalized ⊤ F U ⊤
      le_normalizer_of_normal le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal)
  have hnQF : (commutatorPreimage (⊤ : Subgroup G) Q F).Normal := by
    rw [←normalizer_eq_top_iff]
    exact top_unique (commutatorPreimage_normalized ⊤ Q F ⊤
      le_normalizer_of_normal le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal)
  let := hnFU
  let := hnQF
  let : H.Normal := inferInstance
  let D := (pResidual 2 H).map H.subtype
  have hDH : D ≤ H := map_subtype_le _
  have hD : IsPPerfect 2 D := isPPerfect_embedded_pResidual 2 H
  have hDU : D ≤ centralizer (U : Set G) := hDH.trans (inf_le_left.trans inf_le_left)
  have hFDU : ⁅F,D⁆ ≤ U := by
    rw [commutator_comm]
    exact (commutator_mono (hDH.trans (inf_le_left.trans inf_le_right)) le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ F U le_normalizer_of_normal)
  have hQDF : ⁅Q,D⁆ ≤ F := by
    rw [commutator_comm]
    exact (commutator_mono (hDH.trans inf_le_right) le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ Q F le_normalizer_of_normal)
  have hid := commutator_isPPerfect_idempotent D Q hD hQ le_normalizer_of_normal
  have hQDU : ⁅Q,D⁆ ≤ U := by
    rw [←hid]
    exact (commutator_mono hQDF le_rfl).trans hFDU
  have hzero : ⁅Q,D⁆ = ⊥ := by
    apply bot_unique
    rw [←hid]
    exact (commutator_mono hQDU le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hDU)).le
  have hDQ : D ≤ Q := (commutator_eq_bot_iff_le_centralizer.mp
    (by rwa [commutator_comm] : ⁅D,Q⁆ = ⊥)).trans hself
  have hdp : IsPGroup 2 D := hQ.to_le hDQ
  have he : (⊥ : Subgroup D) = ⊤ := hD _ inferInstance
    (hdp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
  have hDbot : D = ⊥ := by
    apply bot_unique
    intro d hd
    exact congrArg Subtype.val (mem_bot.mp
      (show (⟨d,hd⟩ : D) ∈ (⊥ : Subgroup D) from he.symm ▸ mem_top _))
  have hres : pResidual 2 H = ⊥ :=
    (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hDbot
  have hp : IsPGroup 2 H := by
    have hh := isPGroup_quotient_pResidual (G := H) 2
    exact hh.of_equiv ((QuotientGroup.quotientMulEquivOfEq hres).trans
      QuotientGroup.quotientBot)
  exact le_sSup ⟨inferInstance,hp⟩

/-- An ambient subgroup acting trivially on three normal layers of a
self-centralizing two-subgroup lies in the relative two-core. -/
theorem le_twoCore_of_relative_three_step_chain (N Q F U A : Subgroup G)
    (hQN : Q ≤ N) (hFN : F ≤ N) (hUN : U ≤ N) (hAN : A ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G)) (hNF : N ≤ normalizer (F : Set G))
    (hNU : N ≤ normalizer (U : Set G))
    (hQ : IsPGroup 2 Q) (hself : N ⊓ centralizer (Q : Set G) ≤ Q)
    (hAU : A ≤ centralizer (U : Set G))
    (hAF : ⁅A,F⁆ ≤ U) (hAQ : ⁅A,Q⁆ ≤ F) :
    A ≤ N.pCoreIn 2 := by
  let Q' := Q.subgroupOf N
  let F' := F.subgroupOf N
  let U' := U.subgroupOf N
  let A' := A.subgroupOf N
  let : Q'.Normal := normal_subgroupOf_of_le_normalizer hNQ
  let : F'.Normal := normal_subgroupOf_of_le_normalizer hNF
  let : U'.Normal := normal_subgroupOf_of_le_normalizer hNU
  have hs : centralizer (Q' : Set N) ≤ Q' := by
    intro n hn
    apply hself
    refine ⟨n.property,?_⟩
    intro q hq
    exact congrArg Subtype.val (mem_centralizer_iff.mp hn ⟨q,hQN hq⟩ hq)
  have hc : A' ≤ centralizer (U' : Set N) := by
    intro a ha u hu
    exact Subtype.ext (hAU ha u hu)
  have hdF : ⁅A',F'⁆ ≤ U' := by
    apply (map_le_map_iff_of_injective (f := N.subtype) N.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hAN,map_subgroupOf_eq_of_le hFN,
      map_subgroupOf_eq_of_le hUN]
    exact hAF
  have hdQ : ⁅A',Q'⁆ ≤ F' := by
    apply (map_le_map_iff_of_injective (f := N.subtype) N.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hAN,map_subgroupOf_eq_of_le hQN,
      map_subgroupOf_eq_of_le hFN]
    exact hAQ
  have hA : A' ≤ pCore 2 N :=
    (le_inf (le_inf hc (le_commutatorPreimage le_top hdF))
      (le_commutatorPreimage le_top hdQ)).trans
        (three_step_chain_centralizer_le_twoCore Q' F' U' hQ.comap_subtype hs)
  have hm := map_mono (f := N.subtype) hA
  rwa [map_subgroupOf_eq_of_le hAN] at hm

end Theory.GroupTheory
