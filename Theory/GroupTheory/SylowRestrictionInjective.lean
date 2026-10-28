module
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.ElementaryAbelian.Basic

/-!
# Recovering Sylow subgroups from a normal subgroup

If a normal subgroup N has a p-group quotient and self-normalizing Sylow
p-subgroups, the normalizer of an embedded Sylow of N is a p-group.
Consequently distinct ambient Sylows have distinct intersections with N.
If nonidentity elements of exponent p determine Sylows in N, an elementary
subgroup in two distinct ambient Sylows embeds in G/N, bounding its order
by the actual index of N.

The small projective unitary enlargement applies this to the normal
PSU₃(2) image of index at most two. This isolates precisely the possible
order-two shared actor without asserting an invalid full intersection
property for the outer extension. The proof is the usual Sylow restriction
and normalizer argument; source application: DGS, Groups and Graphs (1985),
5.1(c,d) and 8.1(g), pp.104--105,133.
-/

public noncomputable section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact (Nat.Prime p)] in
/-- The ambient normalizer of a self-normalizing Sylow in N is a p-group. -/
theorem normalizer_isPGroup_of_normal_self_normalizing
    (N : Subgroup G) [N.Normal] (hq : IsPGroup p (G ⧸ N))
    (U : Sylow p N) (hU : normalizer (U : Set N) = (U : Subgroup N)) :
    IsPGroup p (normalizer ((U : Subgroup N).map N.subtype : Set G)) := by
  let R := (U : Subgroup N).map N.subtype
  let M := normalizer (R : Set G)
  let f : M →* G ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  have hMN : M.subgroupOf N = U := by
    change (normalizer ((U : Subgroup N).map N.subtype : Set G)).comap N.subtype = _
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective N.subtype_injective]
    exact hU
  have hk : f.ker ≤ R.subgroupOf M := by
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have hxU : (⟨x,hxN⟩ : N) ∈ (U : Subgroup N) := by
      rw [←hMN]
      exact x.property
    exact mem_map_of_mem N.subtype hxU
  have hp : IsPGroup p f.ker := ((U.isPGroup'.map N.subtype).comap_subtype).to_le hk
  have ht := (hq.to_subgroup (⊤ : Subgroup (G ⧸ N))).comap_of_ker_isPGroup f hp
  rw [comap_top] at ht
  exact ht.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup M) ≃* M)

/-- Restriction to N determines each ambient Sylow subgroup. -/
theorem eq_of_restriction_of_normal_self_normalizing
    (N : Subgroup G) [N.Normal] (hq : IsPGroup p (G ⧸ N))
    (hN : ∀ U : Sylow p N, normalizer (U : Set N) = (U : Subgroup N))
    (S T : Sylow p G) (he : (S : Subgroup G) ⊓ N = (T : Subgroup G) ⊓ N) : S = T := by
  obtain ⟨U,hU⟩ := S.exists_sylow_map_eq_inf_of_normal N
  let R := (U : Subgroup N).map N.subtype
  have hSN : (S : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [show R = (S : Subgroup G) ⊓ N from hU]
    exact (le_inf (S : Subgroup G).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [show R = (T : Subgroup G) ⊓ N from hU.trans he]
    exact (le_inf (T : Subgroup G).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hp := normalizer_isPGroup_of_normal_self_normalizing N hq U (hN U)
  exact Sylow.ext ((S.is_maximal' hp hSN).symm.trans (T.is_maximal' hp hTN))

/-- A common elementary subgroup of distinct Sylows has order at most [G:N]. -/
theorem eq_or_card_le_index_of_normal_self_normalizing
    (N : Subgroup G) [N.Normal] (hq : IsPGroup p (G ⧸ N))
    (hN : ∀ U : Sylow p N, normalizer (U : Set N) = (U : Subgroup N))
    (huniq : ∀ U V : Sylow p N, ∀ x : N,
      x ∈ U → x ∈ V → x ≠ 1 → x ^ p = 1 → U = V)
    (S T : Sylow p G) (A : Subgroup G) [IsElementaryAbelian p A]
    (hAS : A ≤ S) (hAT : A ≤ T) : S = T ∨ Nat.card A ≤ N.index := by
  by_cases he : S = T
  · exact Or.inl he
  right
  obtain ⟨U,hU⟩ := S.exists_subgroupOf_eq_of_normal N
  obtain ⟨V,hV⟩ := T.exists_subgroupOf_eq_of_normal N
  have hAN : A ⊓ N = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    by_contra hx1
    have hUV : U = V := huniq U V ⟨x,hx.2⟩
      (by change (⟨x,hx.2⟩ : N) ∈ (U : Subgroup N); rw [hU]; exact hAS hx.1)
      (by change (⟨x,hx.2⟩ : N) ∈ (V : Subgroup N); rw [hV]; exact hAT hx.1)
      (fun hh => hx1 (congrArg Subtype.val hh))
      (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := p) x hx.1))
    apply he
    apply eq_of_restriction_of_normal_self_normalizing N hq hN S T
    have hh := congrArg (fun R : Sylow p N => (R : Subgroup N).map N.subtype) hUV
    rwa [hU,hV,subgroupOf_map_subtype,subgroupOf_map_subtype] at hh
  let f : A →* G ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp (hAN ▸ (show (x : G) ∈ A ⊓ N from
      ⟨x.property,(QuotientGroup.eq_one_iff _).mp hx⟩))
  exact Nat.card_le_card_of_injective f hf
end Sylow
