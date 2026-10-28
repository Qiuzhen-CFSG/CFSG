module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiExchangedSupport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiNormalizedSupport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# Exchanged Suzuki support and the normal residual configuration

A prime in an exchanged binary SL2 support has triple binary displacement
under the commuting original Suzuki component. The support automorphism rank
bound contradicts that displacement; the original degree bound handles the
small primitive-prime exceptions. Combined with the normalized exclusion,
this removes binary SL2 support in every degree and both orientations.

For a nonnormal support component, apply the genuine four-model source to
the semisimple layer joined with a Sylow two-subgroup. The original trivial
two-core transports its actual quotient model back to the support. Binary,
odd-linear, Janko and Suzuki exclusions therefore force support normality in
the full action image. The literal Hall consumer retains both exact kernels,
all earlier rank and degree bounds, and a normal nonbinary support witness.
The normal nonbinary and nonseparated even-linear cases remain to be proved.

Source: Aschbacher--Smith 1.2.1(3), D.3.9 and 10.2.3, in particular the
centralizing-Z branch on printed p.745 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
universe u
variable {Γ : Type u} [Group Γ] [Finite Γ] {T : Sylow 2 Γ} {L : Subgroup Γ}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance exchangedSupportElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup Γ) :=
  source_original_full_moved_elementary D
local instance exchangedSupportFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)) := Module.Finite.of_finite

/-- The original support degree bound removes the two small primitive-prime
exceptions, so every exchanged binary SL2 support is excluded. -/
theorem original_suzuki_no_exchanged_binary_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : componentOrbit J A ≠ ⊥) (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A)
    (hnot : ¬ A ≤ normalizer (J : Set _))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (eJ : J ≃* SL(2,F)) : False := by
  have hd := original_suzuki_even_component_support_degree D c m hm e A J hA hAc hJ hXn hXA
    n hn hF eJ
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponentImage D
  let : Fact (0 < m) := ⟨hm⟩
  let eK := (originalMovedComponentEquiv D c.nonnormal).trans e
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hi := imageRepresentation_isIrreducible ρ (movedStabilizerAction_irreducible D c ht htn hsep)
  let : IsIrreducible (imageRepresentation ρ) := hi
  let := Subrepresentation.irreducible_module_nontrivial (imageRepresentation ρ)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hi K ((Subgroup.nontrivial_iff_ne_bot K).mp inferInstance)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  let : IsSimpleGroup J := eJ.isSimpleGroup
  have hlay := movedStabilizerImage_semisimple_sqtk D (componentLayer (actionImage ρ))
    componentLayer_idempotent
  exact ChapterD.suzuki_no_exchanged_large_binary_support (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hi K hfix m hm eK J A hJ hA
    (le_centralizer_iff.mp (hJc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    (le_centralizer_iff.mp (hAc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    hlay.stronglyQuasithin hnot n (by omega) hF eJ

/-- Binary support is impossible in either orientation for the original
Suzuki quotient-action kernel and the same full starred actor. -/
theorem original_suzuki_no_binary_component_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : componentOrbit J A ≠ ⊥) (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (eJ : J ≃* SL(2,F)) : False := by
  by_cases hAJ : A ≤ normalizer (J : Set _)
  · have heq : componentOrbit J A = J :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hAJ) (le_componentOrbit J A)
    exact original_suzuki_no_normalized_binary_support D c m hm e A J hA hAc hJ hJc hAJ
      (by simpa only [heq] using hXA) n hn hF eJ
  · exact original_suzuki_no_exchanged_binary_support D c m hm e A J hA hAc hJ hJc hXn hXA
      hAJ n hn hF eJ

/-- The four-model source applies inside the layer joined with an actual
Sylow two-subgroup. The relative component and two-core quotient are retained
until the model is transported back to the original component. -/
theorem original_moved_nonnormal_component_model
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    {t : Γ} (ht : t ∈ (T : Subgroup Γ)) (htn : t ∉ normalizer (L : Set Γ))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set Γ) ∨
      D.seed ≤ centralizer (L : Set Γ))
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJ : IsComponent _ J) (hnormal : ¬ J.Normal) :
    Chapter1.Section02.NonnormalCComponentModel J := by
  have hlay := movedStabilizerImage_semisimple_sqtk D
    (componentLayer (actionImage (movedStabilizerAction D))) componentLayer_idempotent
  have hidx := (hJ.normal_or_index_two_of_layer_odd_rank_le_two hlay.stronglyQuasithin).resolve_left hnormal
  let S : Sylow 2 (actionImage (movedStabilizerAction D)) := default
  let A : Subgroup (actionImage (movedStabilizerAction D)) := S
  have hnot : ¬ A ≤ normalizer (J : Set _) := by
    intro hh
    have hd := Subgroup.index_dvd_of_le hh
    rw [hidx] at hd
    exact S.not_dvd_index hd
  let E := componentLayer (actionImage (movedStabilizerAction D))
  let Y := E ⊔ A
  have hJY : J ≤ Y := (show J ≤ E from le_sSup hJ).trans le_sup_left
  let J' := J.subgroupOf Y
  let eJ : J' ≃* J := subgroupOfEquivOfLe hJY
  have hSQY : IsSQTK KnownSimple.IsKnownSimple Y :=
    ChapterB.QuasisimpleSource.IrreducibleBranch.local_sqtk
      ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups E A
      (movedStabilizerImage_semisimple_sqtk D E componentLayer_idempotent)
      S.isPGroup'
  have hnon : ¬ J'.Normal := by
    intro hh
    exact hnot (le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer hJY).mp hh))
  have hmodel := ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (ChapterE.Structure.sqtk_two_quotient hSQY (pCore 2 Y) pCore_isPGroup)
    (hJ.subgroupOf hJY).isCComponent).resolve_left hnon).2
  have hJ2 : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hJ.1,movedStabilizerImage_twoCore_eq_bot D c ht htn hsep]
    exact J.subtype.ker_eq_bot_iff.mpr J.subtype_injective
  have hJ'2 : pCore 2 J' = ⊥ := by
    apply map_injective (f := eJ.toMonoidHom) eJ.injective
    rw [pCore_map_iso,hJ2,Subgroup.map_bot]
  exact hmodel.of_mulEquiv (eJ.symm.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hJ'2.symm)))

/-- Every support component remaining in the original Suzuki kernel is
normal in the full action image; all four nonnormal source models are excluded. -/
theorem original_suzuki_component_support_normal
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : componentOrbit J A ≠ ⊥) (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A) :
    J.Normal := by
  by_contra hnot
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let : IsQuasisimple J := hJ.2
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
  cases original_moved_nonnormal_component_model D c ht htn hsep J hJ hnot with
  | linear_even n hn he =>
    obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact original_suzuki_no_binary_component_support D c m hm e A J hA hAc hJ hJc hXn hXA
      n hn hF (eF.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
  | linear_prime p hp ho he =>
    obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
    have hl := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF ▸ ho) (by
        intro hs
        let := hs
        exact Group.IsPerfect.not_isSolvable J
          (Group.isSolvable_of_isSolvable_injective (f := eF.toMonoidHom) eF.injective))
    exact original_suzuki_no_odd_linear_component_support D c m hm e A J hA hAc hJ hXn hXA
      (by rw [hF]; exact ⟨p,1,hp,ho,by simp⟩) hl eF
  | janko he =>
    apply original_suzuki_no_five_support D c m hm e J hJc
    rw [Nat.card_congr he.some.toEquiv,Janko1.card_model]
    decide
  | suzuki r hr he =>
    have hthree := original_centralizing_starred_support_three_dvd D c ht htn hsep A J hA hJ hJc hXA
    rw [Nat.card_congr he.some.toEquiv] at hthree
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free r (by omega) hthree

/-- The surviving Suzuki support is a normal, nonbinary component in the
full original action image. Every previous kernel and rank bound is retained. -/
@[expose] def OriginalSuzukiNormalNonbinarySupport
    (hn : ¬ (T : Subgroup Γ) ≤ normalizer (L : Set Γ)) : Prop :=
  OriginalSuzukiNoNormalizedBinarySupport D hn ∧
  ∃ (m : ℕ), 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
    ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      A ≤ (originalMovedQuotientAction D hn).ker ∧
      IsComponent _ J ∧ J.Normal ∧ 3 ∣ Nat.card J ∧ Nat.Coprime 5 (Nat.card J) ∧
      J ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≠ ⊥ ∧ ⁅componentOrbit J A,A⁆ = componentOrbit J A ∧
      ⁅J,A⁆ = J ∧ 2*(2*m+1) ≤ primeRank 2 (MulAut J) ∧
      (∀ n : ℕ, 2 ≤ n → ¬ Nonempty (J ≃* SL(2,GaloisField 2 n)))

/-- Apply both orientations and the nonnormal four-model exclusion to the
literal Hall subgroup, without any extra constituent or support premise. -/
theorem original_hall_conclusion_or_normal_nonbinary_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨ OriginalSuzukiNormalNonbinarySupport D c.nonnormal := by
  rcases original_hall_conclusion_or_no_normalized_binary_support D c with hh | he | hs
  · exact Or.inl hh
  · exact Or.inr (Or.inl he)
  · have hsave := hs
    obtain ⟨_,m,hm,⟨e⟩,A,J,hA,hAc,hJ,hthree,hfive,hJc,hXc,hXn,hXA,_,_⟩ := hs
    have hnormal := original_suzuki_component_support_normal D c m hm e A J hA hAc hJ hJc hXn hXA
    let := hnormal
    let := hJ.2
    have hAJ : A ≤ normalizer (J : Set _) := le_top.trans_eq J.normalizer_eq_top.symm
    have heq : componentOrbit J A = J :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hAJ) (le_componentOrbit J A)
    have hJA : ⁅J,A⁆ = J := by simpa only [heq] using hXA
    have hr := original_suzuki_normalized_support_rank D c m hm e A J hA hAc
      (heq ▸ hXn) hAJ hJA
    refine Or.inr (Or.inr ⟨hsave,m,hm,⟨e⟩,A,J,hA,hAc,hJ,hnormal,hthree,hfive,hJc,
      hXc,hXn,hXA,hJA,hr,?_⟩)
    intro n hn ⟨eJ⟩
    exact original_suzuki_no_binary_component_support D c m hm e A J hA hAc hJ hJc hXn hXA
      n hn (GaloisField.card 2 n (by omega)) eJ
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
