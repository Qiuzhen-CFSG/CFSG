module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ComponentRank
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# Rank bounds on the nonsingular residual and its automorphisms

Conjugation by the original V has kernel C_V(K_v), so the established corank
bound gives an elementary subgroup of Aut(K_v) of rank at least five.
The original moved group V_v maps to K_v/Z(K_v) with kernel contained in
its one-dimensional L_v-fixed space, giving quotient rank at least four.
Neither argument replaces V by V/C_V(L) or assumes K_v is quasisimple.

Source: Aschbacher--Smith, proof of Lemma 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Conjugation by V gives at least five independent involutory automorphisms. -/
theorem SourceHypothesis.nonsingular_automorphism_rank
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    5 ≤ primeRank 2 (MulAut (Kv (v : G))) := by
  have hn : V ≤ normalizer (Kv (v : G) : Set G) := (V_le_Gv v).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  let f := (Kv (v : G)).normalizerMonoidHom.comp (inclusion hn)
  have hk : f.ker = (centralizer (Kv (v : G) : Set G)).subgroupOf V := by
    ext x
    change inclusion hn x ∈ (Kv (v : G)).normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc : Nat.card f.range = (centralizer (Kv (v : G) : Set G)).relIndex V := by
    rw [← index_ker, hk]
    rfl
  have hr := H.nonsingular_component_centralizer_corank D v hv
  rw [← hc, IsElementaryAbelian.log_card_eq_primeRank] at hr
  exact hr.trans (primeRank_subgroup_le 2 _)

/-- The original order-32 moved group loses at most its fixed line modulo the center. -/
theorem SourceHypothesis.nonsingular_centralQuotient_rank
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    4 ≤ primeRank 2 ((Kv (v : G)) ⧸ center (Kv (v : G))) := by
  let C := Kv (v : G)
  let W := Vv L V (v : G)
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hBC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  let := Vv_elementary H.chosen.normalizes (v : G)
  let f : W →* C ⧸ center C := (QuotientGroup.mk' (center C)).comp (inclusion hWC)
  let j : f.ker → ZV (Lv L (v : G)) W := fun x => ⟨x.val.val, x.val.property, by
    have hz : inclusion hWC x.val ∈ center C := (QuotientGroup.eq_one_iff _).mp x.property
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hBC hb⟩)⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ZV (Lv L (v : G)) W => (z : G)) h
  have hk : Nat.card f.ker ≤ 2 := (Nat.card_le_card_of_injective j hj).trans_eq
    (D.nonsingular_moved_fixed_card H.chosen v hv)
  have hc := f.ker.card_mul_index
  rw [index_ker,D.nonsingular_moved_card H.chosen v hv] at hc
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hi : 16 ≤ Nat.card f.range := by nlinarith
  have hb := (primeRank_le_iff_elementary_card_le (C ⧸ center C)).mp le_rfl
    f.range (inferInstance : IsElementaryAbelian 2 f.range)
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp (hi.trans hb)

end CFSG.Quasithin.Chapter12.Section06
