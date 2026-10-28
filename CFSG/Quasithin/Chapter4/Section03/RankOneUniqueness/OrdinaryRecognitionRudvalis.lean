module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionRemaining
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.LocalA5Shape
public import Theory.SpecificGroups.Rudvalis.BinaryThreeFixer
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The last Rudvalis row in ordinary rank-one recognition

The fully moved source module restricts the original field degree to two or
three. At degree two the original Sylow-normalized local A₅ section has
core center of order at most two, contradicting its proved noncentral core
center. At degree three the actual R₀ involution fixes a subgroup with order
divisible by 21, impossible in the concrete Rudvalis automorphism group.
No placement, field comparison or action premise is added.

Source: Aschbacher--Smith C.3.1(9), pp.149--151, and 4.3.6, p.614;
the intrinsic model calculations retain their ATLAS attribution.
-/

public section

open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem core_center_small {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (center (pCore 2 A)) ≤ 2) :
    (center (pCore 2 A)).map (pCore 2 A).subtype ≤ center A := by
  let Z := (center (pCore 2 A)).map (pCore 2 A).subtype
  have hz : Nat.card Z ≤ 2 := by rwa [card_map_of_injective (pCore 2 A).subtype_injective]
  let : Z.Normal := by infer_instance
  by_cases h1 : Nat.card Z = 1
  · exact (card_eq_one.mp h1).le.trans bot_le
  · exact central_of_normal_card_two Z (by have := Nat.card_pos (α := Z); omega)

/-- The original local quotient and full Sylow exclude the Rudvalis central quotient. -/
theorem ordinary_no_rudvalis (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* Rudvalis.Model) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  have hd := c.ordinary_model_moved_order_dvd D ho hn hpsl e
  rw [Rudvalis.model_card] at hd
  have hn5 : n < 5 := by
    by_contra! hh
    have h := (pow_dvd_pow 2 (by omega : 15 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd)
    norm_num at h
  have hcases : n = 2 ∨ n = 3 := by
    by_cases h4 : n = 4
    · subst n; norm_num at hd
    · omega
  rcases hcases with rfl | rfl
  · obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv ho e
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
    obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    obtain ⟨P,hP,_,_⟩ := c.ordinary_model_local_data D ho e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hSN : (S : Subgroup Rudvalis.Model) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans (c.ordinaryLocal.le_normalizer_map f)
      rw [hP]
      exact c.ordinary_component_sylow_normalizes_local D
    exact c.ordinary_model_core_center_not_central ho e (core_center_small
      (MainConverse.SporadicLocal.RuEven.normalized_a5_core_center_card_le_two S B hSN (b.trans d)))
  · let := ho.2
    let : IsSimpleGroup (c.K ⧸ center c.K) := IsQuasisimple.simple
    let : IsSimpleGroup Rudvalis.Model := e.isSimpleGroup_congr.mp inferInstance
    obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e
    have h21 : 21 ∣ Nat.card B := (by decide : 21 ∣ 2^3*((2^3)^2-1)).trans
      (c.ordinary_model_local_order_dvd ho e hpsl)
    have he := Rudvalis.eq_one_of_fixes_twentyOne B h21 r
      (hr ▸ pow_orderOf_eq_one r) hfix
    simp only [he,orderOf_one] at hr
    omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
