module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.ElementaryAbelian.Injective
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankProduct
/-!
# Normal elementary centralizers of order a prime

A normal subgroup C inside A embeds in A/O_p(A) when O_p of the
ambient group is trivial. Thus an elementary quotient makes C elementary.
If C centralizes a centerless subgroup of p-rank one in an ambient group
of p-rank at most two, independent ranks bound C by order p. Nontriviality
then gives equality.

Source application: the centralizing cubic in Aschbacher--Smith 12.6.31,
printed p.836, refs/quasithin.pdf. The original-group application retains
the full two-core quotient and the actual L₁-star centralizer.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
/-- Normal subgroups inside an elementary core quotient have no hidden kernel
when the ambient prime core vanishes. -/
theorem normal_elementary_of_core_quotient
    {J : Type*} [Group J] {p q : ℕ} (A C : Subgroup J) [C.Normal]
    (hzero : pCore p J = ⊥) (hCA : C ≤ A)
    [IsElementaryAbelian q (A ⧸ pCore p A)] : IsElementaryAbelian q C := by
  let f := (QuotientGroup.mk' (pCore p A)).comp (inclusion hCA)
  have hker : IsPGroup p f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hCA)
  have hC : pCore p C = ⊥ := by
    rw [pCore_eq_comap_of_normal,hzero,MonoidHom.comap_bot]
    exact C.subtype.ker_eq_bot C.subtype_injective
  have hk : f.ker ≤ pCore p C := le_sSup ⟨inferInstance,hker⟩
  have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
    (bot_unique (hk.trans hC.le))
  exact IsElementaryAbelian.of_injective f hi

/-- A nontrivial elementary centralizer of a centerless rank-one subgroup
in a group of rank at most two has order p. -/
theorem centralizing_elementary_card_prime
    {J : Type*} [Group J] [Finite J] {p : ℕ} [Fact p.Prime]
    (B C : Subgroup J) [IsElementaryAbelian p C]
    (hz : center B = ⊥) (hB : primeRank p B = 1)
    (hJ : primeRank p J ≤ 2) (hc : C ≤ centralizer (B : Set J))
    (hne : C ≠ ⊥) : Nat.card C = p := by
  have hd : Disjoint C B := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hxz : (⟨x,hx.2⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro b
      exact Subtype.ext (hc hx.1 b.val b.property)
    have he : (⟨x,hx.2⟩ : B) = 1 := mem_bot.mp (hz ▸ hxz)
    exact mem_bot.mpr (congrArg (fun b : B => b.val) he)
  have hr := primeRank_subgroup_le p (C ⊔ B)
  rw [C.primeRank_sup_eq_add_of_disjoint_commuting B hd hc,hB] at hr
  have hC : primeRank p C ≤ 1 := by omega
  have hu := (primeRank_le_iff_elementary_card_le C).mp hC ⊤
    (IsElementaryAbelian.of_injective (⊤ : Subgroup C).subtype Subtype.val_injective)
  rw [card_top,pow_one] at hu
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p C).exists_card_eq
  have hnpos : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    exact hne ((eq_bot_iff_card C).mpr (by simpa only [hn0,pow_zero] using hn))
  apply le_antisymm hu
  rw [hn]
  simpa only [pow_one] using
    (show p^1 ≤ p^n from Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le hnpos)
end Theory.GroupTheory
