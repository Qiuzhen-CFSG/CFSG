module
public import Theory.SpecificGroups.BinaryLinear.SixSubgroupCentralizers
public import Theory.SpecificGroups.Alternating.SixSectionNormalizerBound

/-!
# An A₆ section of small normalizer index in binary five-space has a two-core

If the section's two-core vanished, it would be a centerless subgroup of
order 360, so its GL₅(2) centralizer would be trivial. Its normalizer's
two-subgroups would then embed in Aut(A₆) and have order at most 32.
Index at most four would bound the ambient Sylow order by 128, contradicting
the actual GL₅(2) Sylow order 1024. The original embedding is retained.
Source: Aschbacher--Smith 12.6.17, printed p.827, and A.2.10--11, p.35,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.QuinticNormalizer
open OuterCyclic
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

theorem six_section_core_ne_bot
    (A : Subgroup (LinearGroup 5))
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 (LinearGroup 5))
    (hi : (normalizer (A : Set (LinearGroup 5))).relIndex S ≤ 4) : pCore 2 A ≠ ⊥ := by
  intro hz
  let a : A ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)).trans e
  have hc : centralizer (A : Set (LinearGroup 5)) = ⊥ :=
    FiveComponentCentralizer.centralizer_eq_bot A (by
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]; decide) (by
      apply eq_bot_iff.mpr
      intro x hx
      have hh := (centerCongr a) ⟨x,hx⟩ |>.property
      change a x ∈ center (alternatingGroup (Fin 6)) at hh
      rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
      exact a.map_eq_one_iff.mp hh)
  let P := normalizer (A : Set (LinearGroup 5)) ⊓ (S : Subgroup (LinearGroup 5))
  let f := (MulAut.congr a).toMonoidHom.comp
    (A.normalizerMonoidHom.comp (inclusion (show P ≤ normalizer (A : Set _) from inf_le_left)))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hx0 : A.normalizerMonoidHom (inclusion (show P ≤ normalizer (A : Set _) from inf_le_left) x) = 1 :=
      (MulAut.congr a).injective (hx.trans (map_one _).symm)
    have hxc : (x : LinearGroup 5) ∈ centralizer (A : Set _) := by
      have hh : inclusion (show P ≤ normalizer (A : Set _) from inf_le_left) x ∈
          A.normalizerMonoidHom.ker := hx0
      rwa [normalizerMonoidHom_ker] at hh
    exact Subtype.ext (mem_bot.mp (hc ▸ hxc))
  have hp : IsPGroup 2 P := S.isPGroup'.to_le inf_le_right
  obtain ⟨Q,hQ⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hb : Nat.card P ≤ 32 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact (card_le_of_le hQ).trans_eq (AlternatingSix.ShadowLocal.sylow_card Q)
  have hm : Nat.card P * (normalizer (A : Set (LinearGroup 5))).relIndex S = Nat.card S := by
    rw [relIndex,←((normalizer (A : Set (LinearGroup 5))).subgroupOf S).card_mul_index]
    congr 1
    have he : (normalizer (A : Set (LinearGroup 5))).subgroupOf S = P.subgroupOf S := by
      ext x; simp [P]
    rw [he,Nat.card_congr (subgroupOfEquivOfLe (show P ≤ S from inf_le_right)).toEquiv]
  have hS : Nat.card S = 1024 := by
    rw [S.card_eq_multiplicity]
    have hh : Nat.card (LinearGroup 5) = 9999360 := by
      rw [←Nat.card_congr (matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
      decide
    rw [hh]
    decide +kernel
  have hmul := Nat.mul_le_mul hb hi
  rw [hm,hS] at hmul
  norm_num at hmul
end BinaryLinear.QuinticNormalizer
