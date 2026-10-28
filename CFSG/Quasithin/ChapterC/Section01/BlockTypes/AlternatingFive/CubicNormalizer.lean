module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Cubic actors in an alternating-five block

The marked A₅ quotient maps each Sylow normalizer onto an A₄ of order
twelve, so the original normalizer contains an element of order three.
Its image modulo O₂ is nontrivial. The commutator with that cubic is
normal and has full image in the simple centerless quotient; two-perfection
then makes the commutator the whole block. No splitting of the block is used.

Source: Aschbacher–Smith, proof of 2.4.25, printed p.542.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {H : Type*} [Group H] [Finite H]

private theorem alternating_sylow_normalizer_card
    (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (normalizer (P : Set (alternatingGroup (Fin 5)))) = 12 := by
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  rw [hi,Nat.card_eq_fintype_card]
  clear P hi
  revert i
  decide +kernel

/-- A Sylow two-subgroup of an alternating-five block is not normal. -/
theorem IsAlternatingBlock.sylow_normalizer_ne_top_five
    (h : IsAlternatingBlock H 5) (P : Sylow 2 H) : normalizer (P : Set H) ≠ ⊤ := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  have hn := P.normalizer_map_surjective q hq
  change (normalizer (P : Set H)).map q = normalizer (Q : Set _) at hn
  intro he
  rw [he,map_top_of_surjective q hq] at hn
  have hc := alternating_sylow_normalizer_card Q
  rw [←hn,card_top,nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

/-- The original Sylow normalizer contains an actual element of order three. -/
theorem IsAlternatingBlock.exists_sylow_normalizer_cubic
    (h : IsAlternatingBlock H 5) (P : Sylow 2 H) :
    ∃ a : H, a ∈ normalizer (P : Set H) ∧ orderOf a = 3 := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  have hn := P.normalizer_map_surjective q hq
  change (normalizer (P : Set H)).map q = normalizer (Q : Set _) at hn
  have hc : Nat.card ((normalizer (P : Set H)).map q) = 12 := by
    rw [hn]
    exact alternating_sylow_normalizer_card Q
  have hd := card_map_dvd (normalizer (P : Set H)) q
  rw [hc] at hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (P : Set H)) 3
    ((by decide : 3 ∣ 12).trans hd)
  exact ⟨a,a.property,(orderOf_injective (normalizer (P : Set H)).subtype
    (normalizer (P : Set H)).subtype_injective a).trans ha⟩

omit [Finite H] in
/-- Every cubic of the original block generates its full commutator subgroup. -/
theorem IsAlternatingBlock.commutator_cubic_eq_top
    (h : IsAlternatingBlock H 5) (a : H) (ha : orderOf a = 3) :
    ⁅(⊤ : Subgroup H),zpowers a⁆ = ⊤ := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hqa : q a ≠ 1 := by
    intro he
    have haK : a ∈ pCore 2 H := hk ▸ he
    have hpow : (⟨a,haK⟩ : pCore 2 H)^3=1 :=
      Subtype.ext (ha ▸ pow_orderOf_eq_one a)
    have h1 : (⟨a,haK⟩ : pCore 2 H)=1 :=
      (pCore_isPGroup.powEquiv (by decide : Nat.Coprime 2 3)).injective (by
        simpa only [IsPGroup.powEquiv_apply,one_pow] using hpow)
    have ha1 : a=1 := congrArg Subtype.val h1
    simp only [ha1,orderOf_one] at ha
    omega
  let N : Subgroup H := ⁅(⊤ : Subgroup H),zpowers a⁆
  let hn : N.Normal := normalizer_eq_top_iff.mp
    (top_unique (normalizer_commutator_ge_left (⊤ : Subgroup H) (zpowers a)))
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (hn.map q hq).eq_bot_or_eq_top with hb | ht
  · have he : ⁅(⊤ : Subgroup (alternatingGroup (Fin 5))),zpowers (q a)⁆ = ⊥ := by
      simpa only [N,map_commutator,map_top_of_surjective q hq,MonoidHom.map_zpowers] using hb
    have hc := commutator_top_left_eq_bot_iff_le_center.mp he (mem_zpowers (q a))
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc
    exact (hqa hc).elim
  · have hs : N ⊔ pCore 2 H = ⊤ := by
      have hh := congrArg (Subgroup.comap q) ht
      simpa only [comap_map_eq,hk,comap_top] using hh
    exact h.2.1.twoPerfect N hn (isPGroup_quotient_of_sup_eq_top N (pCore 2 H) pCore_isPGroup hs)

end CFSG.Quasithin.ChapterC
