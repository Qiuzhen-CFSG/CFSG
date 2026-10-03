module

public import Stellmacher.SectionThree.LemmaThreeNine

/-!
# Cross-normalization from Stellmacher (3.9)

Suppose the two solvable local-family members `P₁` and `P₂`, their actual
join `H`, and the chosen Sylow subgroup `T` satisfy the hypotheses of (3.9).
If the common local Sylow subgroup `S` equals its Baumann subgroup, then
each local 2-residual normalizes the omega-center commutator of the other.
The public interface constructs the maximal normal subgroup required by the
existing (3.9) theorem, so callers supply only its local-group, omega-center,
Thompson-subgroup, and Baumann hypotheses.

If either residual is trivial, both normalizations are immediate. Otherwise
the trivial subgroup belongs to the finite poset of normal subgroups of `H`
avoiding both residuals. A maximal member supplies the exact (3.9) input.
Its Baumann-containment alternative is impossible: a local 2-core lies in
its Sylow `S`, and local-family membership excludes equality with `S`.
The remaining alternatives either make each cross actor centralize the
commutator, or identify the two commutators. A commutator is normalized by
its own right actor, giving the result in the latter case.

Source: Stellmacher (3.9), Journal of Algebra 190 (1997), pp.23--24,
and its normalizer application in the proof of (6.1), p.30, in
`refs/latex/stellmacher-n-group.tex`. The ambient group need not equal `H`.
-/

namespace Stellmacher.SectionThree
universe u

public theorem threeNine_residual_normalizes_omega_commutators
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hsolv₁ : Group.IsSolvable P₁)
    (hsolv₂ : Group.IsSolvable P₂)
    (T : Sylow 2 H) (hST : S ≤ sylowAmbient T)
    (Q : Subgroup G) (hQ : Q = S ⊓ twoCoreAmbient H)
    (hsolv : Group.IsSolvable H)
    (hOmega : omegaOneCenterAmbient S ≤ Q)
    (hJ : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (sylowAmbient T))
    (hBaumann : S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) = S) :
    twoResidualAmbient P₂ ≤ Subgroup.normalizer
      ((⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆ : Subgroup G) : Set G) ∧
    twoResidualAmbient P₁ ≤ Subgroup.normalizer
      ((⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆ : Subgroup G) : Set G) := by
  classical
  by_cases hR₁ : twoResidualAmbient P₁ = ⊥
  · simp only [hR₁, Subgroup.commutator_bot_right, Subgroup.normalizer_eq_top,
      le_top, bot_le, and_self]
  by_cases hR₂ : twoResidualAmbient P₂ = ⊥
  · simp only [hR₂, Subgroup.commutator_bot_right, Subgroup.normalizer_eq_top,
      le_top, bot_le, and_self]
  let X : Set (Subgroup G) := {N | N ≤ H ∧ (N.subgroupOf H).Normal ∧
    ¬ twoResidualAmbient P₁ ≤ N ∧ ¬ twoResidualAmbient P₂ ≤ N}
  have hbot : (⊥ : Subgroup G) ∈ X := by
    refine ⟨bot_le, ?_, ?_, ?_⟩
    · simp only [Subgroup.bot_subgroupOf]
      infer_instance
    · exact fun hr => hR₁ (le_bot_iff.mp hr)
    · exact fun hr => hR₂ (le_bot_iff.mp hr)
  obtain ⟨N, hNmax⟩ := X.toFinite.exists_maximal ⟨⊥, hbot⟩
  have hN : N ≤ H ∧ (N.subgroupOf H).Normal ∧
      ¬ twoResidualAmbient P₁ ≤ N ∧
      ¬ twoResidualAmbient P₂ ≤ N ∧
      ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
        (N'.subgroupOf H).Normal →
        (¬ twoResidualAmbient P₁ ≤ N' ∧
          ¬ twoResidualAmbient P₂ ≤ N') → N' = N := by
    refine ⟨hNmax.prop.1, hNmax.prop.2.1, hNmax.prop.2.2.1,
      hNmax.prop.2.2.2, ?_⟩
    intro N' hNN' hN'H hN'normal havoid
    exact (hNmax.eq_of_le ⟨hN'H, hN'normal, havoid.1, havoid.2⟩ hNN').symm
  have hCore (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S) :
      ¬ S ≤ twoCoreAmbient P := by
    intro hSCore
    have hCoreS : twoCoreAmbient P ≤ S := by
      obtain ⟨U, hU⟩ := hP.1.2.1
      rw [← hU]
      exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal U)
    exact hP.1.2.2.2 (le_antisymm hSCore hCoreS)
  rcases lemma_three_nine S h P₁ P₂ H N hP₁ hP₂ hH hN hsolv₁ hsolv₂
      T hST Q hQ hsolv hOmega hJ with ha | hb | hc
  · constructor
    · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [Subgroup.commutator_comm]
      exact ha.1
    · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [Subgroup.commutator_comm]
      exact ha.2
  · rw [hBaumann] at hb
    exact (hb.elim (hCore P₁ hP₁) (hCore P₂ hP₂)).elim
  · constructor
    · rw [hc]
      exact Subgroup.normalizer_commutator_ge_right _ _
    · rw [← hc]
      exact Subgroup.normalizer_commutator_ge_right _ _

end Stellmacher.SectionThree
