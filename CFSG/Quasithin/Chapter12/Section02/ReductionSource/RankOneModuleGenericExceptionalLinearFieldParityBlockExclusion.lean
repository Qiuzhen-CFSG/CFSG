module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupBlockExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityBlock
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParitySuzukiPair

/-!
# Block exclusion and the actual Chapter12 normalizer span

The selected natural Fundamental Setup now excludes the original block and
core-collapse alternatives. The full point-normalizer span, and every span
under an intermediate H₁, are elementary abelian under solvability of the
literal residual quotient-action kernel. No block-exclusion, abelianness or
natural-module marking is assumed.

The final adapters apply this to F.8.1 and to the completed degree-three
displacement and both terminal critical-pair branches. They retain exactly
residual-normalizer TI and either the original kernel-solvability consequence
or the independent F.1.12 Suzuki containment statement. Full TI and discharge
of that recognition input remain with qt-d-1222-linear-field-parity; these
adapters do not assert unconditional parity or an unconditional Seed.

Source: Aschbacher–Smith 5.1.17, pp.640–642, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The actual Cartan centralizer covers a nonabelian Sylow image. -/
theorem rankOne_odd_cartan_centralizer_nonabelian
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    : ¬ IsMulCommutative ((T : Subgroup G) ⊓ centralizer (A : Set G) : Subgroup G) := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact sylow_cartan_centralizer_nonabelian
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH c hodd hm hnf hlinear

/-- The natural chosen module cannot be the entire component core. -/
theorem rankOne_odd_core_ne_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    : L.pCoreIn 2 ≠ V := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_core_ne_module hi hH c hodd hm hnf hlinear F

/-- Exclude the source natural block on the literal component L. -/
theorem rankOne_odd_not_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    : ¬ ChapterC.IsL2EvenBlock L n := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_not_block hi hH c hodd hm hnf hlinear F hnat

/-- The original full point-normalizer span is abelian. -/
theorem rankOne_odd_normalizer_span_abelian_of_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    : IsMulCommutative (normalizerSetup T L V).U := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_normalizer_span_abelian_of_solvable hi hH c hodd hm hnf hlinear hsolv F hnat

/-- Every intermediate source H₁ has an elementary abelian span. -/
theorem rankOne_odd_intermediate_span_elementary_of_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (J : Subgroup G) (hJN : J ≤ (setup T L V H A).G₁) :
    IsElementaryAbelian 2 (conjugateSpanBy V J) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_intermediate_span_elementary_of_solvable
    hi hH c hodd hm hnf hlinear hsolv F hnat J hJN

/-- All F.8 clauses follow from the remaining residual TI and kernel solvability. -/
theorem rankOne_f8_of_solvable_and_residual_ti
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hti : ∀ g ∈ normalizer (residual H : Set G),
      (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁)
    : (setup T L V H A).Hypothesis := by
  exact D.rankOne_f8_of_normalizer_span h hmany hn hpsl hH hlinear hodd hti
    (D.rankOne_odd_g2 h hmany hn hpsl hH hlinear c hodd)
    (D.rankOne_odd_normalizer_span_abelian_of_solvable h hmany hn hpsl hH hlinear c hodd hsolv)
    (D.rankOne_odd_quotient_kernel h hmany hn hpsl hH hlinear c hodd)

/-- Construct every original Seed field from solvability and residual-normalizer TI. -/
theorem rankOne_odd_seed_of_solvable_and_residual_ti
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hti : ∀ g ∈ normalizer (residual H : Set G),
      (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁)
    : Nonempty (Seed T L H A n) := by
  apply D.rankOne_odd_seed_of_chosen_geometry h hmany hn hpsl hH hlinear c hodd
    (D.rankOne_f8_of_solvable_and_residual_ti h hmany hn hpsl hH hlinear c hodd hsolv hti)
  have ht := D.rankOne_point_global_ti_of_residual_ti h hmany hn hpsl hH hlinear hodd hti
  intro g
  by_cases hg : g ∈ normalizer ((setup T L V H A).V₁ : Set G)
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hg)
  · left
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨y,hy,he⟩ := hx.2
    have hy1 := (ChapterI.Section06To08.isTISubgroup_iff _).mp ht g hg y hy (by
      change (MulAut.conj g).toMonoidHom y ∈ (setup T L V H A).V₁
      rw [he]
      exact hx.1)
    simpa only [hy1,map_one,mem_bot] using he.symm

/-- The parity consumer no longer assumes abelianness of the normalizer span. -/
theorem rankOne_even_exponent_of_solvable_and_residual_ti
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgen : 1 < ChapterE.generationParameter H)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hti : ∀ (A B : Subgroup G) (_c : CartanPair T L H A B) (_ho : Odd n),
      ∀ g ∈ normalizer (residual H : Set G),
        (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁)
    : Even n := by
  apply D.rankOne_even_exponent_of_seed h hmany hn hpsl hH hgen hlinear
  intro A B c ho
  exact D.rankOne_odd_seed_of_solvable_and_residual_ti
    h hmany hn hpsl hH hlinear c ho hsolv (hti A B c ho)

/-- Preserve the exact independent Suzuki source premise in final parity assembly. -/
theorem rankOne_even_exponent_of_suzuki_containment_and_residual_ti
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgen : 1 < ChapterE.generationParameter H)
    (hrec : ∀ R : Subgroup G,
      HypothesisF11 ![L,R] (T : Subgroup G) →
      IsQuasithin (generated ![L,R] (T : Subgroup G)) →
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal →
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ≤ R)
    (hti : ∀ (A B : Subgroup G) (_c : CartanPair T L H A B) (_ho : Odd n),
      ∀ g ∈ normalizer (residual H : Set G),
        (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁)
    : Even n := by
  apply D.rankOne_even_exponent_of_seed h hmany hn hpsl hH hgen hlinear
  intro A B c ho
  have hs := D.rankOne_odd_quotientCentralizerKernel_solvable_of_suzuki_containment
    h hmany hn hpsl hH hlinear c ho hrec
  exact D.rankOne_odd_seed_of_solvable_and_residual_ti
    h hmany hn hpsl hH hlinear c ho hs (hti A B c ho)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
