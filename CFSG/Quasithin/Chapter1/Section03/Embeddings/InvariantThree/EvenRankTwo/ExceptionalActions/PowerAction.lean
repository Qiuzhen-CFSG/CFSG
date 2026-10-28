module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import Theory.GroupAction.OddInvolutionFrattini

/-!
# Power actions on the three-complement

A noncyclic finite group has noncyclic Frattini quotient. A nonidentity
element of that quotient therefore generates a proper nonzero subgroup.
If the pair automizer acts by powers, this subgroup is invariant under the
entire automizer, and hence under each of its two-subgroups. No assertion
about cyclicity of an outer group replaces the actual action hypothesis.

Source: the field-action exclusion in Aschbacher–Smith Proposition 1.3.4,
printed p.511 (PDF p.528 of refs/quasithin.pdf).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions

variable {Q : Type*} [Group Q] [Finite Q]

/-- Power action on the literal Frattini quotient excludes all two-subgroups
of the pair automizer, with a common proper nonzero invariant subgroup. -/
theorem pairReducible_of_quotient_powers (S R : Subgroup Q)
    (hn : ¬ IsCyclic R)
    (hp : ∀ b ∈ pairAutomizer S R, ∀ v : R ⧸ frattini R,
      quotientAut (frattini R) b v ∈ zpowers v) : PairReducible S R := by
  classical
  have hq := OddInvolutionFrattini.noncyclic_frattini_quotient hn
  by_cases hs : Subsingleton (R ⧸ frattini R)
  · let _ := hs
    exact (hq inferInstance).elim
  · let _ := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨v, hv⟩ := exists_ne (1 : R ⧸ frattini R)
    apply pairReducible_of_invariant
    refine ⟨zpowers v, ?_, ?_, ?_⟩
    · intro he
      exact hv (mem_bot.mp (he ▸ mem_zpowers v))
    · intro he
      exact hq (_root_.isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, he⟩)
    · intro b hb x hx
      exact (zpowers_le.mpr hx) (hp b hb x)

/-- A uniform power formula on the complement descends to its Frattini
quotient and supplies the full pair-reducibility conclusion. -/
theorem pairReducible_of_powers (S R : Subgroup Q) (hn : ¬ IsCyclic R)
    (hp : ∀ b ∈ pairAutomizer S R, ∃ k : ℕ, ∀ r : R, b r = r ^ k) :
    PairReducible S R := by
  apply pairReducible_of_quotient_powers S R hn
  intro b hb v
  obtain ⟨k, hk⟩ := hp b hb
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) v
  rw [quotientAut_apply_mk, hk, map_pow]
  exact pow_mem (mem_zpowers _) _

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
