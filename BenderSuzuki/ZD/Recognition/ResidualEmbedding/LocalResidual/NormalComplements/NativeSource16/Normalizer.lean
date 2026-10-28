module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Normalizer.Maximal

/-!
# The source Section 16 normalizer theorem

Choose a maximal contrary p-subgroup Y, then a maximal p-overgroup W fixing
at least three cosets. The centralizer circle of Y is trivial. The affine
obstruction proves that the normalizer circle of W is nontrivial, so W is
still contrary and maximality forces W=Y. The Bender–Witt theorem makes its
normalizer doubly transitive on the fixed set. The free distinguished
involution and the odd-core factorization then contradict degree at least
three.

The final result constructs the literal `SectionSixteenNormalizer` interface
used by Section 17. Its sole earlier local input is Corollary 16.6(e): trivial
circle subgroups have normal two-complements and cyclic Sylow two-subgroups.

Source: GLS IV, Chapter 2, Lemma 16.7, refs/KGroup/GLS4/Chapter2.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section16.NativeSource
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 MulAction
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- GLS IV, Chapter 2, Lemma 16.7 from the original residual action and the
earlier source 16.6(e) local-complement theorem. -/
public theorem sectionSixteenNormalizer_of_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    Section17.NativeSource.SectionSixteenNormalizer Z M := by
  intro p hp hpodd Y hY hthree
  classical
  by_contra hnot
  let bad : Subgroup G → Prop := fun Q => IsPGroup p Q ∧
    2 < Nat.card (theorem4bFixedPoints M Q) ∧
    ¬ localCircleIn Z (normalizer (Q : Set G)) ≤ centralizer (Q : Set G)
  obtain ⟨Y₀, _, hmaxY⟩ := Finite.exists_le_maximal
    (p := bad) (a := Y) (show bad Y from ⟨hY, hthree, hnot⟩)
  obtain ⟨s, hsZ, hsN, hsC⟩ : ∃ s ∈ Z, s ∈ normalizer (Y₀ : Set G) ∧
      s ∉ centralizer (Y₀ : Set G) := by
    by_contra hn
    push Not at hn
    apply hmaxY.1.2.2
    rw [localCircleIn_eq_closure]
    apply (closure_le _).mpr
    rintro s ⟨hs, hsN⟩
    exact hn s hs hsN
  have hodd : Odd (Nat.card Y₀) := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hmaxY.1.1.exists_card_eq
    rw [hk]
    exact hpodd.pow
  obtain ⟨hstr, hcent⟩ := contrary_normalizer_structure h r ha Y₀ hodd
    hmaxY.1.2.1 hsZ hsN hsC
  obtain ⟨W, hYW, hmaxW⟩ := Finite.exists_le_maximal
    (p := fun Q : Subgroup G => IsPGroup p Q ∧ 2 < Nat.card (theorem4bFixedPoints M Q))
    (a := Y₀) ⟨hmaxY.1.1, hmaxY.1.2.1⟩
  have hWne := maximal_fixed_normalizer_circle_ne_bot h.disconnected ha hlocal hp hpodd W hmaxW
  have hWbad : ¬ localCircleIn Z (normalizer (W : Set G)) ≤ centralizer (W : Set G) := by
    intro hWC
    have hle : localCircleIn Z (normalizer (W : Set G)) ≤
        localCircleIn Z (centralizer (Y₀ : Set G)) := by
      rw [localCircleIn_eq_closure, localCircleIn_eq_closure]
      apply (closure_le _).mpr
      rintro v ⟨hvZ, hvN⟩
      apply Subgroup.subset_closure
      refine ⟨hvZ, ?_⟩
      apply centralizer_le (show (Y₀ : Set G) ⊆ W from hYW)
      apply hWC
      rw [localCircleIn_eq_closure]
      exact Subgroup.subset_closure ⟨hvZ, hvN⟩
    rw [hcent] at hle
    exact hWne (le_bot_iff.mp hle)
  have hWY : W = Y₀ := le_antisymm (hmaxY.2 ⟨hmaxW.1.1, hmaxW.1.2, hWbad⟩ hYW) hYW
  subst W
  let N := normalizer (Y₀ : Set G)
  let F := theorem4bFixedPoints M Y₀
  let : MulAction N F := normalizerFixedPointAction G (G ⧸ M) Y₀
  have htwo : IsMultiplyPretransitive N F 2 := normalizerFixedPointAction_twoPretransitive Y₀
    (chapter1_bender_normalizer_two_pretransitive hp ha.two_transitive Y₀ hmaxW)
  let sN : N := ⟨s, hsN⟩
  have hsi : PFAppendixIII.IsInvolution sN := BenderSuzuki.IsInvolution.subtype (h.disconnected.involutions s hsZ) hsN
  have hfree : ∀ a : F, sN • a ≠ a := by
    intro a hh
    exact normalizer_involution_free h.disconnected ha Y₀ hodd hmaxY.1.2.1 hsZ hsN hsC a
      (congrArg Subtype.val hh)
  exact no_free_involution_of_odd_factor htwo hmaxY.1.2.1 hsi hfree
    (pPrimeCore 2 N) (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (hstr.factor sN hsZ)

/-- The actual Section 17 consumer: the original local data acquires its
literal fixed pair and every required relative normalizer bound. -/
public theorem source16_localData_fixed_pair_and_normalizer
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (d : TwoCoreLocalData Z M) :
    let L := centralizerClosure Z (d.t * ((d.u : M) : G))
    let D₀ := residualPairStabilizer M d.t ⊓ L
    fixedPointsOfSubgroup G (G ⧸ M) D₀ =
      {QuotientGroup.mk 1, QuotientGroup.mk d.t} ∧
    ∀ Y : Subgroup G, Y ≤ D₀ → ⁅Y, zpowers d.t⁆ ≠ ⊥ → ⁅Y, zpowers d.t⁆ ≤ Y →
      fixedPointsOfSubgroup G (G ⧸ M) Y =
        {QuotientGroup.mk 1, QuotientGroup.mk d.t} ∧
      normalizer (Y : Set G) ⊓ L ≤ D₀ ⊔ zpowers d.t :=
  Section17.NativeSource.localData_fixed_pair_and_normalizer h.disconnected
    (sectionSixteenNormalizer_of_source h r ha hlocal) d

end BenderSuzuki.ZD.Section16.NativeSource
