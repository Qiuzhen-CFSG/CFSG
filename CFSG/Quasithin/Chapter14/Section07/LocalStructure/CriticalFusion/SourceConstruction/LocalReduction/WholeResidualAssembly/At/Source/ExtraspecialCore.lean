module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCoreDuality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.PointGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointNormality
public import Theory.Representation.BinaryConjugationSection.CentralDuality
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryConjugationSection.PairingCentralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointCore
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.Representation.BinaryConjugationSection.CubicLength
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCoreEquality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ChiefCubicGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialChiefSylow
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.PCoreCentralImage
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.CubicSolvable
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicHeisenbergExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSylowIrreducibility
public import Theory.GroupTheory.PGroup.ExtraspecialThreeStableLineLifts
public import Theory.GroupAction.ElementaryTwoTernaryLine
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointCoreRoots
public import Theory.GroupTheory.PGroup.RankOneSquareRoots
public import Theory.SpecificGroups.HeisenbergPrime.SquareRootCenter
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFixedPlane
public import Theory.Representation.CubicSixSpaceNilpotence
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenActor
public import Theory.LinearAlgebra.OrderFourFixedLine
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceInterchange
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCenterMovement
public import Theory.GroupTheory.PResidual.PrimeToAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCenterControl
public import Theory.GroupTheory.ElementaryThompsonFixedIndex
public import Theory.Representation.BinaryConjugationSection.OffenderQuotientIndex
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# Guarded extraspecial core

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original two-core duality in the extraspecial branch

Irreducibility of the literal U/V₁ section makes the radical of its
commutator pairing with O₂(H) exactly V₁. The residual core O₂(K) also
moves U: otherwise the three-subgroup lemma and U = [U,K] would force
the whole H-core to centralize U, contrary to the original plane movement.
Its pairing therefore has the same radical.

Both core-centralizer quotients have order 64. Their indices give
O₂(H) = O₂(K) C_H(U), and restriction of the full-core coordinate map
identifies both quotients with the same contragredient of U/V₁. Restricting
the functionals to the original seed V gives |O₂(K) : O₂(K) ∩ Q| = 4.
The final application starts with the actual Heisenberg isomorphism and
constructs all section actions, retaining the literal core inclusion and
every functional kernel. It uses no recognition datum or duality premise.

This proves source 14.7.20(1) and the numerical part of (4). The chief-factor
alternative, equality of the point and residual cores, remaining commutator
identification in (4), and the extraspecial exclusion still require proof.
Source: Aschbacher–Smith, 14.7.16(1), 14.7.20, printed pp.1048–1049.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialCoreDuality_irreducible_of_comp {D A W : Type*} [Group D] [Group A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (f : A →* D) [IsIrreducible (ρ.comp f)] :
    IsIrreducible ρ := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial (ρ.comp f)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let S' : Subrepresentation (ρ.comp f) :=
    ⟨S.toSubmodule,fun a _ hv => S.apply_mem_toSubmodule (f a) hv⟩
  rcases eq_bot_or_eq_top S' with he | he
  · left
    apply le_antisymm _ bot_le
    intro v hv
    exact (show v ∈ (⊥ : Subrepresentation (ρ.comp f)) from he ▸ hv)
  · right
    apply top_unique
    intro v _
    exact (show v ∈ S' from he ▸ (show v ∈ (⊤ : Subrepresentation (ρ.comp f)) from trivial))

omit [Finite G] in
private theorem ExtraspecialCoreDuality_core_normalized : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
  F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))

omit [Finite G] in
private theorem ExtraspecialCoreDuality_point_centralizes : F.Vi 1 ≤ centralizer (F.H : Set G) := by
  apply le_centralizer_iff.mp
  exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))

omit [Finite G] in
private theorem ExtraspecialCoreDuality_irreducible_centralizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) F.H W) [IsIrreducible ρ]
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (N : Subgroup G) (hNH : N ≤ F.H) (hN : F.H ≤ normalizer (N : Set G))
    (hmove : ¬ N ≤ centralizer (F.U : Set G)) :
    F.U ⊓ centralizer (N : Set G) = F.Vi 1 := by
  have hZ : F.Vi 1 ≤ F.U ⊓ centralizer (N : Set G) :=
    le_inf s.kernel_le (ExtraspecialCoreDuality_point_centralizes.trans (centralizer_le hNH))
  apply (s.eq_kernel_or_section _ hZ inf_le_left
    ((le_inf s.normalized (hN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf)).resolve_right
  intro he
  have hUC : F.U ≤ centralizer (N : Set G) := he ▸ inf_le_right
  exact hmove (le_centralizer_iff.mp hUC)

/-- The original H-action is irreducible in the extraspecial branch. -/
theorem extraspecial_section_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) : IsIrreducible ρ := by
  obtain ⟨σ,hσ,_,_,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let := hi
  let : IsIrreducible σ := ExtraspecialCoreDuality_irreducible_of_comp σ (pResidual 2 (HStar F.H)).subtype
  exact hσ ▸ ((irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mpr inferInstance)

/-- In the extraspecial branch the core commutator pairing has radical exactly the original point. -/
theorem extraspecial_core_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let := extraspecial_section_irreducible h hab structural previous hex hcard hexp s
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ExtraspecialCoreDuality_irreducible_centralizer ρ s _ (pCoreIn_le 2 F.H) ExtraspecialCoreDuality_core_normalized
    (fun he => plane_moved_of_point_normal h structural hn
      (he.trans (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)))))

omit [Finite G] in
private theorem ExtraspecialCoreDuality_residual_core_normalized :
    F.H ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
  (le_normalizer_embedded_pResidual 2 F.H).trans
    (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))

omit [Finite G] in
private theorem ExtraspecialCoreDuality_residual_core_le_core : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (map_subtype_le _) (le_normalizer_embedded_pResidual 2 F.H)

/-- The residual two-core already moves U; the original core action cannot come only from H/K. -/
theorem residual_core_moves_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ¬ (K F).pCoreIn 2 ≤ centralizer (F.U : Set G) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hcent
  have hcomm : ⁅F.H.pCoreIn 2,K F⁆ ≤ (K F).pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show K F ≤ F.H from map_subtype_le _))
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp
        ((pCoreIn_le 2 F.H).trans (le_normalizer_embedded_pResidual 2 F.H))
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp
        ((show K F ≤ F.H from map_subtype_le _).trans ExtraspecialCoreDuality_core_normalized)
  have h₁ : ⁅⁅F.U,F.H.pCoreIn 2⁆,K F⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm F.U]
    exact (section_core_commutator_le_point h s).trans
      (ExtraspecialCoreDuality_point_centralizes.trans (centralizer_le (map_subtype_le _)))
  have h₂ : ⁅⁅F.H.pCoreIn 2,K F⁆,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hcent)
  have he := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [commutator_comm (K F),commutator_U h F] at he
  exact plane_moved_of_point_normal h structural hn
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))))

/-- The residual core has the same original pairing radical as the full H-core. -/
theorem extraspecial_residual_core_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    F.U ⊓ centralizer ((K F).pCoreIn 2 : Set G) = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let := extraspecial_section_irreducible h hab structural previous hex hcard hexp s
  exact ExtraspecialCoreDuality_irreducible_centralizer ρ s _
    (ExtraspecialCoreDuality_residual_core_le_core.trans (pCoreIn_le 2 F.H)) ExtraspecialCoreDuality_residual_core_normalized
    (residual_core_moves_of_point_normal h hab structural
      (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp))


/-- The original span lies in the intrinsic two-core of the actual residual, before any recognition datum. -/
theorem span_le_residual_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) : F.U ≤ (K F).pCoreIn 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hUK : F.U ≤ K F := by
    rw [←commutator_U h F]
    exact le_normalizer_iff_commutator_le_right.mp
      (s.section_le.trans (le_normalizer_embedded_pResidual 2 F.H))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U) hUK
    ((show K F ≤ F.H from map_subtype_le _).trans s.normalized)

private theorem ExtraspecialCoreDuality_pairing_of_radical
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N : Subgroup G) (hNQ : N ≤ F.H.pCoreIn 2)
    (hUN : F.U ≤ N) (hN : F.H ≤ normalizer (N : Set G))
    (hc : F.U ⊓ centralizer (N : Set G) = F.Vi 1) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sN : BinaryConjugationSection F.H N (N ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (n : N) (u : F.U),
        (sN.coordinates n).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(n : G),(u : G)⁆ = 1) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ₀,⟨s₀⟩⟩ := exists_section F
  obtain ⟨ρ,sU,sN,hpair,_⟩ := BinaryConjugationSection.exists_central_duality
    F.H N F.U (F.Vi 1) (hNQ.trans (pCoreIn_le 2 F.H)) s₀.section_le hN s₀.normalized
    (s₀.kernel_le.trans hUN) ExtraspecialCoreDuality_point_centralizes
    ((commutator_mono hNQ le_rfl).trans (section_core_commutator_le_point h s₀))
    (by simpa using F.card 1 (by decide))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ :=
    { sU with kernel_le := s₀.kernel_le
              kernel_eq := sU.kernel_eq.trans (congrArg (fun C => C.subgroupOf F.U) hc) }
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  exact ⟨_,inferInstance,inferInstance,ρ,s,sN,hd,
    extraspecial_section_irreducible h hab structural previous hex hcard hexp s,hpair⟩

/-- Both original core quotients are the contragredient of the literal six-dimensional U/V₁ section.
The evaluation-zero clause identifies every functional kernel with its actual group centralizer. -/
theorem extraspecial_core_duality
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N : Subgroup G) (hN : N = F.H.pCoreIn 2 ∨ N = (K F).pCoreIn 2) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sN : BinaryConjugationSection F.H N (N ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (n : N) (u : F.U),
        (sN.coordinates n).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(n : G),(u : G)⁆ = 1) := by
  rcases hN with rfl | rfl
  · exact ExtraspecialCoreDuality_pairing_of_radical h hab structural previous hex hcard hexp _ le_rfl
      ((span_le_residual_core h hab).trans ExtraspecialCoreDuality_residual_core_le_core) ExtraspecialCoreDuality_core_normalized
      (extraspecial_core_centralizer h hab structural previous hex hcard hexp)
  · exact ExtraspecialCoreDuality_pairing_of_radical h hab structural previous hex hcard hexp _ ExtraspecialCoreDuality_residual_core_le_core
      (span_le_residual_core h hab) ExtraspecialCoreDuality_residual_core_normalized
      (extraspecial_residual_core_centralizer h hab structural previous hex hcard hexp)

/-- Each of the two core-centralizer quotients has order 64. -/
theorem extraspecial_core_centralizer_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N : Subgroup G) (hN : N = F.H.pCoreIn 2 ∨ N = (K F).pCoreIn 2) :
    (N ⊓ centralizer (F.U : Set G)).relIndex N = 64 := by
  obtain ⟨X,aX,mX,ρ,sU,sN,hd,_,_⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp N hN
  let : Finite X := Finite.of_surjective (fun u : F.U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  change Nat.card (N ⧸ (N ⊓ centralizer (F.U : Set G)).subgroupOf N) = 64
  let := sN.kernel_normal
  rw [Nat.card_congr sN.quotientEquiv.toEquiv]
  change Nat.card (Module.Dual (ZMod 2) X) = 64
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,hd]
  rfl


/-- The full core is generated by the residual core and its actual U-centralizer, as in 14.7.20(1). -/
theorem extraspecial_core_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    (K F).pCoreIn 2 ⊔ centralizer (F.U : Set G) = F.H.pCoreIn 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let P := (K F).pCoreIn 2
  let C := centralizer (F.U : Set G)
  let QH := F.H.pCoreIn 2
  have hCQ : C ≤ QH := centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) s
  have hPQ : P ≤ QH := ExtraspecialCoreDuality_residual_core_le_core
  have hjoin : P ⊔ C ≤ QH := sup_le hPQ hCQ
  let : (C.subgroupOf QH).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 F.H).trans (s.normalized.trans (normalizer_le_normalizer_centralizer _)))
  have hrel : C.relIndex (P ⊔ C) = C.relIndex P := by
    have he := relIndex_sup_right (P.subgroupOf QH) (C.subgroupOf QH)
    rw [←subgroupOf_sup hPQ hCQ,relIndex_subgroupOf hjoin,relIndex_subgroupOf hPQ] at he
    exact he
  have hP := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp P (Or.inr rfl)
  have hQ := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp QH (Or.inl rfl)
  rw [inf_relIndex_left] at hP hQ
  have hm := relIndex_mul_relIndex C (P ⊔ C) QH le_sup_right hjoin
  rw [hrel,hP,hQ] at hm
  have hone : (P ⊔ C).relIndex QH = 1 := by
    omega
  exact le_antisymm hjoin (Subgroup.relIndex_eq_one.mp hone)


/-- The literal residual core meets the original LT-core in index four. -/
theorem extraspecial_residual_core_seed_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ((K F).pCoreIn 2 ⊓ Q T L).relIndex ((K F).pCoreIn 2) = 4 := by
  let P := (K F).pCoreIn 2
  obtain ⟨X,aX,mX,ρ,sU,sP,_,_,hpair⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp P (Or.inr rfl)
  have hi := BinaryConjugationSection.centralizer_index_of_dual_pairing sU sP hpair V
    (le_conjugateSpanBy V F.H)
  rw [sU.imageSpace_card_eq_relIndex V (le_conjugateSpanBy V F.H)] at hi
  have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
  have hZ : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) V bot_le (F.le_seed 1)
  rw [relIndex_bot_left,relIndex_bot_left,hV,hZ] at hm
  have hv : (F.Vi 1).relIndex V = 4 := by omega
  rw [hv] at hi
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hPLT : P ≤ L ⊔ (T : Subgroup G) :=
    (ExtraspecialCoreDuality_residual_core_le_core.trans hQT).trans le_sup_right
  have he : P ⊓ Q T L = P ⊓ centralizer (V : Set G) := by
    change P ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [←h.centralizer_LT_at structural,←inf_assoc,inf_eq_left.mpr hPLT]
  rw [he,inf_relIndex_left]
  exact hi

/-- Original-group application of 14.7.20(1) and its index-four consequence.
Both quotient actions use one literal U/V₁ section; inclusion of the residual
core preserves every coordinate and every functional kernel. -/
theorem extraspecial_core_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 ∧
    F.U ⊓ centralizer ((K F).pCoreIn 2 : Set G) = F.Vi 1 ∧
    (K F).pCoreIn 2 ⊔ centralizer (F.U : Set G) = F.H.pCoreIn 2 ∧
    (centralizer (F.U : Set G)).relIndex (F.H.pCoreIn 2) = 64 ∧
    ((K F).pCoreIn 2 ⊓ Q T L).relIndex ((K F).pCoreIn 2) = 4 ∧
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sQ : BinaryConjugationSection F.H (F.H.pCoreIn 2)
        (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual)
      (sP : BinaryConjugationSection F.H ((K F).pCoreIn 2)
        ((K F).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (q : F.H.pCoreIn 2) (u : F.U),
        (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(q : G),(u : G)⁆ = 1) ∧
      (∀ (p : (K F).pCoreIn 2) (q : F.H.pCoreIn 2),
        (p : G) = q → sP.coordinates p = sQ.coordinates q) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hsup := extraspecial_core_supplement h hab structural previous hex hcard hexp
  have hi := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp
    (F.H.pCoreIn 2) (Or.inl rfl)
  rw [inf_relIndex_left] at hi
  refine ⟨extraspecial_core_centralizer h hab structural previous hex hcard hexp,
    extraspecial_residual_core_centralizer h hab structural previous hex hcard hexp,
    hsup,hi,extraspecial_residual_core_seed_index h hab structural previous hex hcard hexp,?_⟩
  obtain ⟨X,aX,mX,ρ,sU,sQ,hd,hirr,hpair⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp (F.H.pCoreIn 2) (Or.inl rfl)
  have hCQ := centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU
  have hs : (K F).pCoreIn 2 ⊔ (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) = F.H.pCoreIn 2 := by
    rwa [inf_eq_right.mpr hCQ]
  obtain ⟨sP,hcoord⟩ := sQ.restrict_of_sup_kernel ((K F).pCoreIn 2)
    ExtraspecialCoreDuality_residual_core_le_core ExtraspecialCoreDuality_residual_core_normalized hs
  have hk : (K F).pCoreIn 2 ⊓ (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) =
      (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
    rw [←inf_assoc,inf_eq_left.mpr ExtraspecialCoreDuality_residual_core_le_core]
  let sP' : BinaryConjugationSection F.H ((K F).pCoreIn 2)
      ((K F).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual :=
    { sP with kernel_le := inf_le_left
              kernel_eq := sP.kernel_eq.trans (congrArg (fun C => C.subgroupOf ((K F).pCoreIn 2)) hk) }
  refine ⟨X,aX,mX,ρ,sU,sQ,sP',hd,hirr,hpair,?_⟩
  intro p q hpq
  exact (hcoord p).trans (congrArg sQ.coordinates (Subtype.ext hpq))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Six point-residual chief factors in the extraspecial branch

Relative normality of L₁ places U inside O₂(L₁). The three-subgroup
lemma and the original plane movement show that O₂(L₁) moves U.
Irreducibility of U/V₁ then makes the radical of the central commutator
pairing exactly V₁, identifying O₂(L₁)/C_{O₂(L₁)}(U) with the dual
six-space. These are literal conjugation sections with their exact kernels.

An actual order-three subgroup of L₁ maps onto L₁* and acts without
fixed points on both sections. Each contributes three to its cubic length;
the sections are ordered because U is abelian. The original L₁/O₂(L₁)
has order three, so this yields at least six noncentral two-chief factors
in a complete chief series of L₁. The original Heisenberg application
uses earlier 14.7.10 to deduce N_G(Baum(R₁)) ≤ N_G(L).

The genuine earlier Structural1222, Theorem12213 and 14.7.10 implications
remain explicit. Their existing source producers retain these obligations,
with 14.7.10 owned by qt-d-14710-baumann and final discharge at
qt-d-14775-source. No
recognition datum, chief count, duality or point-normality premise is
assumed by that application. The point-central chief intervals and the
remaining extraspecial exclusion are still open.

Source: Aschbacher–Smith, 14.5.21(1), 14.7.16(1),(7), and the use of
14.7.16(7) in 14.7.21, printed pp.1019,1048–1050.
-/

public noncomputable section

open Subgroup Representation NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialPointCore_pointCore_full_core_normalized : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
  F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))

omit [Finite G] in
private theorem ExtraspecialPointCore_pointCore_point_centralizes : F.Vi 1 ≤ centralizer (F.H : Set G) := by
  apply le_centralizer_iff.mp
  exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))

omit [Finite G] in
private theorem ExtraspecialPointCore_pointCore_irreducible_centralizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) F.H W) [IsIrreducible ρ]
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (N : Subgroup G) (hNH : N ≤ F.H) (hN : F.H ≤ normalizer (N : Set G))
    (hmove : ¬ N ≤ centralizer (F.U : Set G)) :
    F.U ⊓ centralizer (N : Set G) = F.Vi 1 := by
  have hZ : F.Vi 1 ≤ F.U ⊓ centralizer (N : Set G) :=
    le_inf s.kernel_le (ExtraspecialPointCore_pointCore_point_centralizes.trans (centralizer_le hNH))
  apply (s.eq_kernel_or_section _ hZ inf_le_left
    ((le_inf s.normalized (hN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf)).resolve_right
  intro he
  have hUC : F.U ≤ centralizer (N : Set G) := he ▸ inf_le_right
  exact hmove (le_centralizer_iff.mp hUC)

/-- The point-residual two-core moves U under relative point normality. -/
theorem point_core_moves_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ¬ (F.Li L 1).pCoreIn 2 ≤ centralizer (F.U : Set G) := by
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hcent
  have hcomm : ⁅F.H.pCoreIn 2,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right))
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp
        ((pCoreIn_le 2 F.H).trans (hln))
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp
        ((show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right).trans ExtraspecialPointCore_pointCore_full_core_normalized)
  have h₁ : ⁅⁅F.U,F.H.pCoreIn 2⁆,F.Li L 1⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm F.U]
    exact (section_core_commutator_le_point h s).trans
      (ExtraspecialPointCore_pointCore_point_centralizes.trans (centralizer_le ((F.Li_le L 1).trans inf_le_right)))
  have h₂ : ⁅⁅F.H.pCoreIn 2,F.Li L 1⁆,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hcent)
  have he := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [commutator_comm (F.Li L 1),commutator_U_point_of_normal h hn] at he
  exact plane_moved_of_point_normal h structural hn
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))))

/-- The point-residual core has the same pairing radical as the full H-core. -/
theorem extraspecial_point_core_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    F.U ⊓ centralizer ((F.Li L 1).pCoreIn 2 : Set G) = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let := extraspecial_section_irreducible h hab structural previous hex hcard hexp s
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  exact ExtraspecialPointCore_pointCore_irreducible_centralizer ρ s _
    ((pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_right))
    (hln.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1))))
    (point_core_moves_of_point_normal h hab structural
      (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp))

/-- The original span lies in the intrinsic two-core of the point residual. -/
theorem span_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : F.U ≤ (F.Li L 1).pCoreIn 2 := by
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hUK : F.U ≤ F.Li L 1 := by
    rw [←commutator_U_point_of_normal h hn]
    exact le_normalizer_iff_commutator_le_right.mp
      (s.section_le.trans (hln))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U) hUK
    ((show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right).trans s.normalized)

private theorem ExtraspecialPointCore_pointCore_pairing_of_radical
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N : Subgroup G) (hNQ : N ≤ F.H.pCoreIn 2)
    (hUN : F.U ≤ N) (hN : F.H ≤ normalizer (N : Set G))
    (hc : F.U ⊓ centralizer (N : Set G) = F.Vi 1) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sN : BinaryConjugationSection F.H N (N ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (n : N) (u : F.U),
        (sN.coordinates n).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(n : G),(u : G)⁆ = 1) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ₀,⟨s₀⟩⟩ := exists_section F
  obtain ⟨ρ,sU,sN,hpair,_⟩ := BinaryConjugationSection.exists_central_duality
    F.H N F.U (F.Vi 1) (hNQ.trans (pCoreIn_le 2 F.H)) s₀.section_le hN s₀.normalized
    (s₀.kernel_le.trans hUN) ExtraspecialPointCore_pointCore_point_centralizes
    ((commutator_mono hNQ le_rfl).trans (section_core_commutator_le_point h s₀))
    (by simpa using F.card 1 (by decide))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ :=
    { sU with kernel_le := s₀.kernel_le
              kernel_eq := sU.kernel_eq.trans (congrArg (fun C => C.subgroupOf F.U) hc) }
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  exact ⟨_,inferInstance,inferInstance,ρ,s,sN,hd,
    extraspecial_section_irreducible h hab structural previous hex hcard hexp s,hpair⟩

/-- The literal point-core quotient is the dual of U/V₁, with its commutator pairing. -/
theorem extraspecial_point_core_duality
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sN : BinaryConjugationSection F.H ((F.Li L 1).pCoreIn 2)
        ((F.Li L 1).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (n : (F.Li L 1).pCoreIn 2) (u : F.U),
        (sN.coordinates n).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(n : G),(u : G)⁆ = 1) := by
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  exact ExtraspecialPointCore_pointCore_pairing_of_radical h hab structural previous hex hcard hexp _
    (pCoreIn_mono_of_normalizes ((F.Li_le L 1).trans inf_le_right) hln)
    (span_le_point_core h hab hn)
    (hln.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1))))
    (extraspecial_point_core_centralizer h hab structural previous hex hcard hexp)

/-- Six noncentral two-chief factors occur in the original point residual. -/
theorem extraspecial_point_six_chief_factors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ∃ t : ChiefSeries (F.Li L 1), t.head = ⊥ ∧ t.last = ⊤ ∧
      6 ≤ t.noncentralTwoCount := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hquot := pointResidual_core_quotient_card (F := F) h structural
  have hdiv : 3 ∣ Nat.card (F.Li L 1) := by
    simpa only [index_eq_card, hquot] using
      (pCore 2 (F.Li L 1)).index_dvd_card
  obtain ⟨A,hA⟩ := Sylow.exists_subgroup_card_pow_prime (G := F.Li L 1) 3 (n := 1)
    (by simpa using hdiv)
  have hA3 : Nat.card A = 3 := by simpa using hA
  let C := A.map (F.Li L 1).subtype
  have hC3 : Nat.card C = 3 := by
    rw [card_map_of_injective (F.Li L 1).subtype_injective,hA3]
  have hCL : C ≤ F.Li L 1 := map_subtype_le _
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hCH : C ≤ F.H := hCL.trans hLH
  have hC : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC3)
  obtain ⟨X,aX,mX,ρ,sU,sN,hd,_,_⟩ :=
    extraspecial_point_core_duality h hab structural previous hex hcard hexp
  let : Finite X := Finite.of_surjective (fun u : F.U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let f : C →* HStar F.H := (starMap F).comp (inclusion hCH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((starMap F).ker.comap (inclusion hCH))
    rw [show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hCH)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (hk.disjoint_of_coprime (hC.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)).le_bot)
  have hrange : f.range = star F (F.Li L 1) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨c,rfl⟩
      exact mem_map_of_mem (starMap F) (hCL c.property)
    · have hrCard : Nat.card f.range = Nat.card C :=
        (Nat.card_congr (Equiv.ofInjective f hf)).symm
      rw [hrCard, pointResidual_star_card_of_normal h structural hn,hC3]
  obtain ⟨σ,hσ⟩ := exists_star_representation h sU
  obtain ⟨z,_,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn sU σ hσ
  let τ : Representation (ZMod 2) C X := ρ.comp (inclusion hCH)
  have hz : z ∈ f.range := by
    rw [hrange,←hgen]
    exact mem_zpowers z
  obtain ⟨c,hc⟩ := hz
  have hfix : τ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply (Submodule.mem_bot _).mpr
    apply hfree v
    rw [←hc]
    change (σ.comp (starMap F)) (inclusion hCH c) v = v
    rw [hσ]
    exact hv c
  have hindex : BinaryFixedPoints.fixedIndex τ = 64 := by
    have hh := BinaryFixedPoints.fixedIndex_mul_card τ
    rw [hfix,Nat.card_unique,mul_one] at hh
    rw [hh,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    rfl
  let : IsCyclic C := isCyclic_of_prime_card hC3
  obtain ⟨c,hc⟩ := IsCyclic.exists_generator (α := C)
  have hdual : BinaryFixedPoints.fixedIndex (ρ.dual.comp (inclusion hCH)) = 64 := by
    change BinaryFixedPoints.fixedIndex τ.dual = 64
    rw [BinaryFixedPoints.fixedIndex_dual τ c hc,hindex]
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hlow : sectionCubicLength C (F.Vi 1) F.U = 3 := by
    rw [sU.sectionCubicLength_eq_fixedIndex C hCH hC (IsElementaryAbelian.isPGroup 2 F.U),hindex]
    norm_num
  have hupp : sectionCubicLength C
      ((F.Li L 1).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ((F.Li L 1).pCoreIn 2) = 3 := by
    rw [sN.sectionCubicLength_eq_fixedIndex C hCH hC (isPGroup_pCoreIn 2 _),hdual]
    norm_num
  have hUC : F.U ≤ (F.Li L 1).pCoreIn 2 ⊓ centralizer (F.U : Set G) :=
    le_inf (span_le_point_core h hab hn) F.U.le_centralizer
  have hm := conjugationCubicLength_mono C hUC
  have hlen : 6 ≤ conjugationCubicLength C ((F.Li L 1).pCoreIn 2) := by
    unfold sectionCubicLength at hlow hupp
    omega
  obtain ⟨t,ht0,ht1⟩ := exists_chiefSeries (⊥ : NormalNode (F.Li L 1)) ⊤ bot_le
  refine ⟨t,ht0,ht1,?_⟩
  rw [CubicComparison.count_of_core_quotient_card_three hquot A hA3 t ht0 ht1]
  rw [←CubicComparison.length_map_injective (F.Li L 1).subtype
    (F.Li L 1).subtype_injective A (pCore 2 (F.Li L 1))]
  exact hlen

/-- Source 14.7.16(7), applied to the literal Heisenberg residual. -/
theorem extraspecial_baumann_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨s,hs0,hs1,hcount⟩ :=
    extraspecial_point_six_chief_factors h hab structural previous hex hcard hexp
  rcases earlier G T L V F d h hab with hsmall | hnormal
  · have hb := hsmall s hs0 hs1
    omega
  · exact hnormal

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Residual core equality in the extraspecial branch

The literal point-core duality first gives
O₂(H) = O₂(L₁) C_H(U). In the central alternative of 14.7.20(2), this
makes [O₂(K),K] lie in O₂(L₁). The central Sylow image in K/O₂(L₁)
is trivial by transfer and two-perfectness, proving O₂(L₁) = O₂(K).

If L₁ moves C_H(U)/U, its moved chief interval is absorbed modulo
O₂(L₁). The already proved localization of K-movement above and below
that interval, together with residual commutator idempotence, gives the
same core equality. All cores and subgroup inclusions are in the original
group, and point normality is derived from the extraspecial hypothesis.

The original Heisenberg application combines these conclusions with the
literal order-four and order-sixteen point-central alternatives, preserving
their action kernels and Sylow markings. Those alternatives still require
exclusion; this module does not assert unconditional 14.7.20(2) or (3).
The earlier Structural1222 and Theorem12213 implications remain explicit,
with final discharge retained by qt-d-14775-source.

Source: Aschbacher–Smith, 14.7.20(1)–(3), printed p.1049.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialCoreEquality_coreEq_point_normalized
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    F.H ≤ normalizer ((F.Li L 1).pCoreIn 2 : Set G) :=
  ((normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1)))

omit [Finite G] in
private theorem ExtraspecialCoreEquality_coreEq_point_le_residual
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    (F.Li L 1).pCoreIn 2 ≤ (K F).pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (pointResidual_le F)
    ((map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn))

/-- The intrinsic point core supplements the full U-centralizer in O₂(H). -/
theorem extraspecial_point_core_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    (F.Li L 1).pCoreIn 2 ⊔ centralizer (F.U : Set G) = F.H.pCoreIn 2 := by
  obtain ⟨X,aX,mX,ρ,sU,sN,hd,_,_⟩ :=
    extraspecial_point_core_duality h hab structural previous hex hcard hexp
  let : Finite X := Finite.of_surjective (fun u : F.U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let N := (F.Li L 1).pCoreIn 2
  let C := centralizer (F.U : Set G)
  let QH := F.H.pCoreIn 2
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hNQ : N ≤ QH :=
    pCoreIn_mono_of_normalizes ((F.Li_le L 1).trans inf_le_right)
      ((normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn)
  have hCQ : C ≤ QH := centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU
  have hjoin : N ⊔ C ≤ QH := sup_le hNQ hCQ
  let : (C.subgroupOf QH).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 F.H).trans (sU.normalized.trans (normalizer_le_normalizer_centralizer _)))
  have hN : (N ⊓ C).relIndex N = 64 := by
    change Nat.card (N ⧸ (N ⊓ C).subgroupOf N) = 64
    let := sN.kernel_normal
    rw [Nat.card_congr sN.quotientEquiv.toEquiv]
    change Nat.card (Module.Dual (ZMod 2) X) = 64
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,hd]
    rfl
  have hQ := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp QH (Or.inl rfl)
  rw [inf_relIndex_left] at hN hQ
  have hrel : C.relIndex (N ⊔ C) = C.relIndex N := by
    have he := relIndex_sup_right (N.subgroupOf QH) (C.subgroupOf QH)
    rw [←subgroupOf_sup hNQ hCQ,relIndex_subgroupOf hjoin,relIndex_subgroupOf hNQ] at he
    exact he
  have hm := relIndex_mul_relIndex C (N ⊔ C) QH le_sup_right hjoin
  rw [hrel,hN,hQ] at hm
  have hone : (N ⊔ C).relIndex QH = 1 := by omega
  exact le_antisymm hjoin (Subgroup.relIndex_eq_one.mp hone)

private theorem ExtraspecialCoreEquality_coreEq_of_centralizer_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ (F.Li L 1).pCoreIn 2) :
    (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 := by
  let N := (F.Li L 1).pCoreIn 2
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hHN : F.H ≤ normalizer (N : Set G) := ExtraspecialCoreEquality_coreEq_point_normalized hn
  have hNH : N ≤ F.H := (pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_right)
  have hNK : N ≤ K F := (pCoreIn_le 2 _).trans (pointResidual_le F)
  have hKH : K F ≤ F.H := map_subtype_le _
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hCH : centralizer (F.U : Set G) ≤ F.H :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) s).trans (pCoreIn_le 2 _)
  have hQK : ⁅F.H.pCoreIn 2,K F⁆ ≤ N := by
    rw [←extraspecial_point_core_supplement h hab structural previous hex hcard hexp]
    exact commutator_sup_le_of_relative_normal F.H N _ (K F) N hHN hNH hCH
      (le_normalizer_iff_commutator_le_left.mp (hKH.trans hHN)) hc
  have hPQ : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hKH (le_normalizer_embedded_pResidual 2 F.H)
  have hPK : ⁅(K F).pCoreIn 2,K F⁆ ≤ N := (commutator_mono hPQ le_rfl).trans hQK
  let R := N.subgroupOf (K F)
  let : R.Normal := normal_subgroupOf_of_le_normalizer (hKH.trans hHN)
  have hp : IsPPerfect 2 (K F) := isPPerfect_embedded_pResidual 2 F.H
  have hcomm : ⁅pCore 2 (K F),(⊤ : Subgroup (K F))⁆ ≤ R := by
    intro x hx
    have hm := mem_map_of_mem (K F).subtype hx
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hPK hm
  have hle := pCore_le_of_commutator_le_of_coprime_index hp
    (show Nat.Coprime 2 (pCore 2 (K F)).index by rw [index_eq_card,hcard]; decide) R hcomm
  apply le_antisymm (ExtraspecialCoreEquality_coreEq_point_le_residual hn)
  rintro _ ⟨x,hx,rfl⟩
  exact hle hx

/-- In the central alternative of 14.7.20(2), the two literal residual cores agree. -/
theorem extraspecial_core_eq_of_centralizer_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 :=
  ExtraspecialCoreEquality_coreEq_of_centralizer_commutator h hab structural previous hex hcard hexp
    (hc.trans (span_le_point_core h hab
      (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp)))


omit [Finite G] in
private theorem ExtraspecialCoreEquality_coreEq_chief_captured
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hBQ : B.val.map F.H.subtype ≤ F.H.pCoreIn 2)
    (hm : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype) :
    B.val.map F.H.subtype ≤ N.val.map F.H.subtype ⊔ (F.Li L 1).pCoreIn 2 := by
  let P : NormalNode F.H := ⟨((F.Li L 1).pCoreIn 2).subgroupOf F.H,
    normal_subgroupOf_of_le_normalizer (ExtraspecialCoreEquality_coreEq_point_normalized hn)⟩
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hBH : B.val.map F.H.subtype ≤ F.H := map_subtype_le _
  have hBN : F.H ≤ normalizer (B.val.map F.H.subtype : Set G) := by
    have he : (B.val.map F.H.subtype).subgroupOf F.H = B.val :=
      comap_map_eq_self_of_injective F.H.subtype_injective B.val
    exact (normal_subgroupOf_iff_le_normalizer hBH).mp (by rw [he]; exact B.property)
  have hc : ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤
      B.val.map F.H.subtype ⊓ (F.Li L 1).pCoreIn 2 := by
    have hb : ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ B.val.map F.H.subtype :=
      le_normalizer_iff_commutator_le_right.mp (hLH.trans hBN)
    have hl : ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ F.Li L 1 :=
      le_normalizer_iff_commutator_le_left.mp
        (hBH.trans ((normal_subgroupOf_iff_le_normalizer hLH).mp hn))
    exact le_inf hb ((le_inf hl (hb.trans hBQ)).trans (inf_pCoreIn_le_of_le 2 hLH))
  have hnode : B ≤ N ⊔ P := by
    obtain he | he := hNB.eq_or_eq (c := N ⊔ (B ⊓ P)) le_sup_left
      (sup_le hNB.le inf_le_left)
    · exfalso
      apply hm
      intro x hx
      obtain ⟨b,hb,hbx⟩ := (hc hx).1
      have hbP : b ∈ P.val := by
        change F.H.subtype b ∈ (F.Li L 1).pCoreIn 2
        rw [hbx]
        exact (hc hx).2
      have hbN : b ∈ N.val := (he ▸ (show B ⊓ P ≤ N ⊔ (B ⊓ P) from le_sup_right)) ⟨hb,hbP⟩
      exact ⟨b,hbN,hbx⟩
    · rw [←he]
      exact sup_le le_sup_left (inf_le_right.trans le_sup_right)
  have hh := map_mono (f := F.H.subtype) hnode
  change B.val.map F.H.subtype ≤ (N.val ⊔ P.val).map F.H.subtype at hh
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le
    ((pCoreIn_le 2 _).trans hLH)] at hh
  exact hh

/-- The faithful chief interval also forces O₂(L₁)=O₂(K): its moved
point action absorbs that interval modulo the point core, and residual
commutator idempotence removes both central flanking sections. -/
theorem extraspecial_core_eq_of_point_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hm : ¬ ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U) :
    (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 := by
  obtain ⟨N,B,hNB,_,hBC,hmove,_,_,hupper,hlower⟩ :=
    extraspecial_exists_point_moved_chief h hab structural previous hex hcard hexp hm
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let P := (F.Li L 1).pCoreIn 2
  let C := centralizer (F.U : Set G)
  have hCQ : C ≤ F.H.pCoreIn 2 :=
    centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) s
  have hPH : P ≤ F.H := (pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_right)
  have hHP : F.H ≤ normalizer (P : Set G) := ExtraspecialCoreEquality_coreEq_point_normalized hn
  have hUP : F.U ≤ P := span_le_point_core h hab hn
  have hbound := ExtraspecialCoreEquality_coreEq_chief_captured hn N B hNB (hBC.trans hCQ) hmove
  have hBK : ⁅B.val.map F.H.subtype,K F⁆ ≤ P :=
    (commutator_mono hbound le_rfl).trans
      (commutator_sup_le_of_relative_normal F.H (N.val.map F.H.subtype) P (K F) P hHP
        (map_subtype_le _) hPH (hlower.trans hUP)
        (le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans hHP)))
  have hid : ⁅⁅C,K F⁆,K F⁆ = ⁅C,K F⁆ :=
    commutator_isPPerfect_idempotent (K F) C (isPPerfect_embedded_pResidual 2 F.H)
      ((isPGroup_pCoreIn 2 F.H).to_le hCQ)
      ((map_subtype_le _).trans (s.normalized.trans (normalizer_le_normalizer_centralizer _)))
  apply ExtraspecialCoreEquality_coreEq_of_centralizer_commutator h hab structural previous hex hcard hexp
  rw [←hid]
  exact (commutator_mono hupper le_rfl).trans hBK

/-- Source 14.7.20(3) is discharged in both the central and the faithful
chief branches. The only remaining branches retain the literal point-central
interval, exact kernel, and order-four Sylow obstruction. -/
theorem extraspecial_centralizer_core_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) ∨
    (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker ∧
        ((Nat.card (Section N B) = 4 ∧
          (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3 ∧
          IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
          Nat.card (star F (T : Subgroup G)) = 4 ∧
          Nat.card (star F (F.Ri L 1)) = 2) ∨
         (Nat.card (Section N B) = 16 ∧
          (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U))) := by
  classical
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  by_cases hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U
  · exact Or.inl ⟨extraspecial_core_eq_of_centralizer_central h hab structural previous
      hex hcard hexp hc,Or.inl hc⟩
  by_cases hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hker,h4 | h16⟩ := extraspecial_point_central_interval_kernels
      h hab structural previous hex hcard hexp hp hc
    · exact Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,hker,Or.inl ⟨h4.1,h4.2,
        extraspecial_four_interval_star_orders h hab structural previous hex hcard hexp
          N B hNB hUN hBC hp hm h4.1⟩⟩
    · exact Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,hker,Or.inr h16⟩
  · exact Or.inl ⟨extraspecial_core_eq_of_point_movement h hab structural previous hex hcard hexp hp,
      Or.inr (extraspecial_exists_point_moved_chief h hab structural previous hex hcard hexp hp)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Cubic containment and the order-four chief-interval exclusion

In the normal-point branch, O₂(H) moves V₂ while the plane-parabolic
core fixes V₂ and has index two in T. Thus those two cores generate T.
For an escaping cubic Y, the solvable-model reduction and the binary
Heisenberg norm calculation make both vertex cores equal O₂(D).
Consequently Y normalizes the plane core as well as O₂(H), so it
normalizes T. This is impossible in the literal S₃ quotient of YT.

This proves the normal-point specialization of 14.5.3(2) needed by the
original extraspecial reduction. Applied to the escaping cubic constructed
from an order-four chief interval, it excludes that interval. The final
original-group reduction preserves the exact order-sixteen kernel and
both central flanks, together with the established central and faithful
order-sixty-four alternatives. The order-sixteen exclusion and the full
residual classification through 14.7.52 remain required.

Source: Aschbacher–Smith, 14.5.3(2), printed p.1013; 14.5.12–13,
pp.1016–1017; 14.7.4(1), p.1043; and 14.7.20, p.1049,
refs/quasithin.pdf. No Data or extra local classification premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem CubicContainment_plane_core_sylow_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ((F.P L).pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
  let P := F.P L
  let S := T.subtype (F.binary_sylow_le_P L)
  let e := planeParabolicQuotientEquiv (F := F) h structural
  have hi := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal S)
  rw [SymmetricThreeTwoCore.core_index e,SymmetricThreeTwoCore.sylow_index_three e S] at hi
  have hi2 : (pCore 2 P).relIndex (S : Subgroup P) = 2 := by
    dsimp only [P]
    omega
  have he := relIndex_map_map_of_injective (pCore 2 P) (S : Subgroup P) P.subtype_injective
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.binary_sylow_le_P L)] at he
  exact he.trans hi2

/-- The point-normalizer core supplements the literal plane core in T. -/
theorem cubic_point_core_plane_core_generate_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    F.H.pCoreIn 2 ⊔ (F.P L).pCoreIn 2 = (T : Subgroup G) := by
  let := h.chosen.elementary
  let A := F.H.pCoreIn 2
  let B := (F.P L).pCoreIn 2
  have hAT : A ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.invariant 1))
  have hBT : B ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (F.P L) (T.subtype (F.binary_sylow_le_P L))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.binary_sylow_le_P L))
  have hBC : B ≤ centralizer (F.Vi 2 : Set G) := by
    change (F.P L).pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)
    rw [←(F.binary_parabolic_core (by decide) L h.chosen.normalizes
      (h.full_LT_action_at structural) (h.centralizer_LT_at structural)).1]
    exact inf_le_right
  have hnot : ¬ A ≤ B := fun hh => plane_moved_of_point_normal h structural hn (hh.trans hBC)
  have hi : B.relIndex (T : Subgroup G) = 2 := CubicContainment_plane_core_sylow_index h structural
  have hjoin := sup_le hAT hBT
  have hd : (A ⊔ B).relIndex (T : Subgroup G) ∣ 2 := by
    have hd := relIndex_dvd_of_le_left (T : Subgroup G) (show B ≤ A ⊔ B from le_sup_right)
    rwa [hi] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact le_antisymm hjoin (relIndex_eq_one.mp h1)
  · have hh := relIndex_mul_relIndex B (A ⊔ B) (T : Subgroup G) le_sup_right hjoin
    rw [hi,h2] at hh
    have h1 : B.relIndex (A ⊔ B) = 1 := by omega
    exact (hnot (le_sup_left.trans (relIndex_eq_one.mp h1))).elim

/-- In the normal-point branch, the source's T-invariant symmetric-three
subgroup is contained in the original normalizer. -/
theorem cubic_containment_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hYP : Y ≤ normalizer ((F.P L).pCoreIn 2 : Set G) := by
    rw [(cubic_generated_equal_two_cores h hab structural previous faithful hn
      Y hYH hYp hYT hout he).1]
    exact (show Y ≤ D from le_sup_left.trans le_sup_right).trans
      (D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  have hYHcore : Y ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    hYH.trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
  have hYTnorm : Y ≤ normalizer (T : Set G) := by
    change Y ≤ normalizer ((T : Subgroup G) : Set G)
    rw [←cubic_point_core_plane_core_generate_sylow h structural hn]
    exact (le_inf hYHcore hYP).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let B := Y ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ B from le_sup_right)
  have hBnorm : B ≤ normalizer (T : Set G) := sup_le hYTnorm (T : Subgroup G).le_normalizer
  have hSnorm : (S : Subgroup B).Normal := normal_subgroupOf_of_le_normalizer hBnorm
  have hs : (S : Subgroup B) = ⊤ := by
    rw [←SymmetricThreeTwoCore.sylow_self_normalizing he.some S]
    exact (normalizer_eq_top_iff.mpr hSnorm)
  have hi := SymmetricThreeTwoCore.sylow_index_three he.some S
  rw [hs,index_top] at hi
  omega

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original point-central chief interval cannot have order four. -/
theorem extraspecial_no_four_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype) :
    Nat.card (Section N B) ≠ 4 := by
  intro hc
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact hout (cubic_containment_of_point_normal h hab structural previous faithful hn Y hYH hYp hYT he)

open NoncentralChiefRefinement in
/-- The original centralizer-core reduction with the order-four interval removed.
The order-sixteen interval retains its exact kernel and both central flanks. -/
theorem extraspecial_centralizer_core_reduction_no_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) ∨
    (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        Nat.card (Section N B) = 16 ∧
        (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) := by
  rcases extraspecial_centralizer_core_reduction h hab structural previous he with hc | hp
  · exact Or.inl hc
  obtain ⟨hp,N,B,hNB,hUN,hBC,hm,hker,h4 | h16⟩ := hp
  · obtain ⟨e⟩ := he
    have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
      (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
    have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
    have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
    exact (extraspecial_no_four_interval h hab structural previous faithful hex hcard hexp
      N B hNB hUN hBC hp hm h4.1).elim
  · exact Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,h16⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Irreducibility of the original extraspecial Sylow action

A stable proper subgroup of the literal extraspecial Frattini quotient
lifts to two T-normalized, two-perfect cubic subgroups generating K.
The selected critical actor gives each Sylow overgroup its actual S₃
quotient. Normal-point cubic containment places both lifts in N_G(L),
contradicting H's escape. Thus T* acts irreducibly on K*/Φ(K*).

An elementary two-actor on a ternary plane always preserves a cubic
line, so T* is not elementary. All original quotient maps and intrinsic
cubic kernels are retained; no local-recognition premise is introduced.
Source: Aschbacher–Smith, 14.7.9 and 14.7.15(2), printed pp.1045,1047.
The remaining point-core structure and the order-sixteen interval still
require proof before 14.7.20 and the residual classification can close.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal star Sylow acts irreducibly on the extraspecial Frattini quotient. -/
theorem extraspecial_star_sylow_frattini_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (J : Subgroup ((pResidual 2 (HStar F.H)) ⧸ frattini (pResidual 2 (HStar F.H))))
    (hs : ∀ a : star F (T : Subgroup G), ∀ x ∈ J,
      quotientAut (frattini (pResidual 2 (HStar F.H)))
        (MulAut.conjNormal (a : HStar F.H)) x ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  by_contra! hnJ
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hk : IsPGroup 2 (starMap F).ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 F.H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨A,B,hAB,hA,hB⟩ := IsExtraspecial.exists_cubic_lifts_of_stable_frattini_line
    (starMap F) (QuotientGroup.mk'_surjective _) hk hP heP
    ((T : Subgroup G).subgroupOf F.H) T.isPGroup'.comap_subtype J hnJ.1 hnJ.2 hs
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have contained (A : Subgroup F.H) (hAK : A ≤ pResidual 2 F.H)
      (hperfect : IsPPerfect 2 A)
      (hAT : (T : Subgroup G).subgroupOf F.H ≤ normalizer (A : Set F.H))
      (hc : Nat.card (A.map (starMap F)) = 3)
      (hZ : A.map (starMap F) ≠ (center P).map P.subtype)
      (hker : ((starMap F).comp A.subtype).ker = pCore 2 A)
      (hquot : Nat.card (A ⧸ pCore 2 A) = 3) :
      A.map F.H.subtype ≤ normalizer (L : Set G) := by
    let Y := A.map F.H.subtype
    have hYH : Y ≤ F.H := map_subtype_le A
    let e : A ≃* Y := equivMapOfInjective A F.H.subtype F.H.subtype_injective
    have hstar : star F Y = A.map (starMap F) := by
      change ((A.map F.H.subtype).comap F.H.subtype).map (starMap F) = _
      rw [comap_map_eq_self_of_injective F.H.subtype_injective]
    have hYT : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
      rw [←map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
      exact (map_mono hAT).trans (le_normalizer_map F.H.subtype)
    let f := (starMap F).comp (inclusion hYH)
    have hke : f.ker.comap e.toMonoidHom = pCore 2 A := hker
    have hkY : f.ker = pCore 2 Y := by
      calc
        f.ker = (f.ker.comap e.toMonoidHom).map e.toMonoidHom :=
          (map_comap_eq_self_of_surjective e.surjective _).symm
        _ = (pCore 2 A).map e.toMonoidHom := congrArg (map e.toMonoidHom) hke
        _ = pCore 2 Y := pCore_map_iso 2 e
    have hqY : Nat.card (Y ⧸ pCore 2 Y) = 3 :=
      (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hquot
    have he := extraspecial_cubic_sylow_quotient h hab structural previous hex hcard hexp
      Y hYH (map_mono hAK) hYT (hstar.symm ▸ hc) (hstar.symm ▸ hZ) hkY hqY
    exact cubic_containment_of_point_normal h hab structural previous faithful hn Y hYH
      (hperfect.of_surjective e.toMonoidHom e.surjective) hYT he
  have hAM := contained A (le_sup_left.trans_eq hAB) hA.1 hA.2.1 hA.2.2.1
    hA.2.2.2.1 hA.2.2.2.2.1 hA.2.2.2.2.2
  have hBM := contained B (le_sup_right.trans_eq hAB) hB.1 hB.2.1 hB.2.2.1
    hB.2.2.2.1 hB.2.2.2.2.1 hB.2.2.2.2.2
  apply h.flag_escape_at F previous
  rw [residual_product F]
  apply sup_le _ (h.sylow_normalizes_at structural)
  change (pResidual 2 F.H).map F.H.subtype ≤ _
  rw [←hAB,Subgroup.map_sup]
  exact sup_le hAM hBM

/-- The original star Sylow is not elementary: an elementary actor always
preserves a cubic line on the literal Frattini quotient. -/
theorem extraspecial_star_sylow_not_elementary
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ¬ IsElementaryAbelian 2 (star F (T : Subgroup G)) := by
  intro hel
  let := hel
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hE : Nat.card (P ⧸ frattini P) = 9 := by
    have hm := (frattini P).card_eq_card_quotient_mul_card_subgroup
    rw [IsExtraspecial.frattini_eq_center_three,IsExtraspecial.center_order_p 3 P,hP] at hm
    rw [IsExtraspecial.frattini_eq_center_three]
    omega
  let α : star F (T : Subgroup G) →* MulAut (P ⧸ frattini P) :=
    ((quotientAut (frattini P)).comp MulAut.conjNormal).comp
      (star F (T : Subgroup G)).subtype
  obtain ⟨J,hJ,hs⟩ := MulAut.exists_stable_three_of_elementary_two α hE
  rcases extraspecial_star_sylow_frattini_irreducible h hab structural previous faithful
      hex hcard hexp J hs with he | he
  · rw [he,card_bot] at hJ
    omega
  · rw [he,card_top,hE] at hJ
    omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Square roots in the original extraspecial point core

The faithful star Sylow action and its nontrivial action on the extraspecial
center rule out an order-two point core: that case would make the Sylow
an elementary four, contradicting its proved Frattini irreducibility.
The rank-one bound then supplies an order-four square root of every
nonidentity point-core involution. The equality Q* = R₁* lifts that root
to an element of the literal original Q.

The selected critical-actor application retains its original representative,
its nontrivial extraspecial action and its center fixation. Only the genuine
earlier structural and faithful classification implications remain explicit.
This supplies the root needed to test the remaining order-sixteen interval;
it does not assert the full C₄/Q₈ classification of R₁*.

Source: Aschbacher–Smith, 14.7.15(2), printed p.1047.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The original point-core star image is not of order two. -/
theorem extraspecial_point_core_card_ne_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    Nat.card (star F (F.Ri L 1)) ≠ 2 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  let P := pResidual 2 (HStar F.H)
  let S := star F (T : Subgroup G)
  let R := star F (F.Ri L 1)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  let eP : P ≃* HeisenbergPrime 3 := (residualStarEquiv F).symm.trans e
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hR : R = S ⊓ centralizer ((center P).map P.subtype : Set (HStar F.H)) := by
    dsimp only [R,S,P]
    rw [point_core_star_eq_centralizer_of_normal h structural hn,
      point_star_eq_center_of_extraspecial_residual h hab structural previous hex hcard hexp]
  have hRS : R ≤ S := hR ▸ inf_le_left
  intro hc
  change Nat.card R = 2 at hc
  have hSc : Nat.card S = 4 := by
    have hm := relIndex_mul_card_of_le hRS
    rw [point_core_star_index_two_of_normal h structural hn,hc] at hm
    exact hm.symm
  have hS2 : IsPGroup 2 S := T.isPGroup'.comap_subtype.map (starMap F)
  let α : S →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp S.subtype
  have hf : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply bot_unique
    intro a ha
    have hcp : (a : HStar F.H) ∈ centralizer (P : Set (HStar F.H)) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer P]
      exact ha
    have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) hcp
    exact Subtype.ext ((hS2.disjoint_of_coprime (IsExtraspecial.isPGroup 3 P)
      (by decide : Nat.Coprime 2 3)).le_bot ⟨a.property,hp⟩)
  have hm : ¬ ∀ a : S, ∀ z ∈ center P, α a z = z := by
    intro hh
    have hSR : S ≤ R := by
      rw [hR]
      refine le_inf le_rfl ?_
      intro a ha z hz
      obtain ⟨z,hz,rfl⟩ := hz
      have hfz := congrArg (fun p : P => (p : HStar F.H)) (hh ⟨a,ha⟩ z hz)
      change a * (z : HStar F.H) * a⁻¹ = (z : HStar F.H) at hfz
      exact (mul_inv_eq_iff_eq_mul.mp hfz).symm
    have heq := le_antisymm hRS hSR
    have hc' : Nat.card R = 4 := heq ▸ hSc
    omega
  have hel := IsExtraspecial.four_actor_elementary_of_center_movement eP α hf hSc hm
  exact extraspecial_star_sylow_not_elementary h hab structural previous faithful hex hcard hexp hel

/-- Every nonidentity star involution in the point core has an order-four
square root represented in the literal original Q. -/
theorem extraspecial_point_core_square_root
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (a : F.H) (ha : (a : G) ∈ F.Ri L 1)
    (hane : starMap F a ≠ 1) (ha2 : (starMap F a)^2=1) :
    ∃ b : F.H, (b : G) ∈ Q T L ∧
      (starMap F b)^2=starMap F a ∧ orderOf (starMap F b)=4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let R := star F (F.Ri L 1)
  let z : R := ⟨starMap F a,mem_map_of_mem (starMap F) ha⟩
  have hz : z≠1 := fun hh => hane (congrArg Subtype.val hh)
  let : Nontrivial R := nontrivial_of_ne z 1 hz
  have hc : 2<Nat.card R := by
    have hpos : 1<Nat.card R := (one_lt_card_iff_ne_bot R).mpr
      (fun hh => hane (mem_bot.mp (hh ▸ z.property)))
    have hne := extraspecial_point_core_card_ne_two h hab structural previous faithful ⟨e⟩
    change Nat.card R ≠ 2 at hne
    omega
  have hRS : R ≤ star F (T : Subgroup G) := by
    dsimp only [R]
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hR2 : IsPGroup 2 R :=
    (T.isPGroup'.comap_subtype.map (starMap F)).to_le hRS
  obtain ⟨b,hb,hbo⟩ := hR2.exists_square_root_of_rank_one
    (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
    hc z hz (Subtype.ext ha2)
  have hbQ : (b : HStar F.H) ∈ star F (Q T L) := by
    rw [(core_product_of_point_normal h hab structural hn).2]
    exact b.property
  obtain ⟨q,hq,heq⟩ := hbQ
  refine ⟨q,hq,?_,?_⟩
  · rw [heq]
    exact congrArg Subtype.val hb
  · rw [heq,orderOf_coe]
    exact hbo

/-- The selected original critical actor admits a square root in Q, retaining
its nontrivial extraspecial action and its center fixation. -/
theorem exists_extraspecial_critical_actor_square_root
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ a b : F.H, (a : G) ∈ c.Uα ∧ starMap F a ≠ 1 ∧ (starMap F a)^2=1 ∧
      (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) ≠ 1 ∧
      (∀ z ∈ center (pResidual 2 (HStar F.H)),
        (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) z = z) ∧
      (b : G) ∈ Q T L ∧ (starMap F b)^2=starMap F a ∧
      orderOf (starMap F b)=4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨a,ha,hane,ha2,hnontrivial,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  obtain ⟨b,hb,hba,hbo⟩ := extraspecial_point_core_square_root h hab structural previous faithful
    ⟨e⟩ a (critical_le_Ri_at h structural c ha) hane ha2
  exact ⟨a,b,ha,hane,ha2,hnontrivial,hcenter,hb,hba,hbo⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original fixed plane and critical commutator

The square root of a selected critical involution lies in the literal Q.
Its star action commutes with the fixed-free cubic and has a two-dimensional
fixed space, equal to its square's displacement. Q centralizes the natural
seed V, so that fixed plane is precisely V/V₁. The known point containment
then lifts the image equality to [U,Uα] = V in the original group.

This proves 14.7.16(3)'s commutator identity in the actual Heisenberg residual
branch, using only the stated earlier source implications. Both the original
section coordinates and star-map representatives are retained.
Source: Aschbacher–Smith, printed pp.1047–1048, refs/quasithin.pdf.
-/
public noncomputable section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem extraspecial_critical_root_fixed_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (a b : F.H) (ha : (a : G) ∈ c.Uα) (hane : starMap F a ≠ 1)
    (hb : (b : G) ∈ Q T L) (hba : (starMap F b)^2 = starMap F a)
    (hfour : (starMap F b)^4 = 1) :
    (ρ b-1).ker = s.imageSpace V ∧ (ρ a-1).range = s.imageSpace V := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
  have hZ : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hz)
  have hfixed : invariants (σ.comp (zpowers z).subtype) = ⊥ := by
    apply bot_unique
    intro v hv
    exact hfree v (hv ⟨z,mem_zpowers z⟩)
  have hbR : starMap F b ∈ star F (F.Ri L 1) := by
    rw [←(core_product_of_point_normal h hab structural hn).2]
    exact mem_map_of_mem (starMap F) hb
  have hcomm : ∀ z' : zpowers z, Commute (σ z') (σ (starMap F b)) := by
    intro z'
    have hc := point_core_star_centralizes_of_normal h structural hn hbR
    exact (show Commute (z' : HStar F.H) (starMap F b) from
      hc z' (hgen ▸ z'.property)).map σ
  have haQ : a ∉ pCore 2 F.H := fun hh => hane ((QuotientGroup.eq_one_iff _).mpr hh)
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hr : Module.finrank (ZMod 2) (σ (starMap F a)-1).range = 2 := by
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a-1).range = 2
    rw [hσ]
    exact critical_displacement_two_of_normal_card_two h hab structural
      (h.flag_escape_at F previous) hn s c hs htwo a ha haQ
  have hsq : (σ (starMap F b))^2=σ (starMap F a) := by rw [←map_pow,hba]
  have h4 : (σ (starMap F b))^4=1 := by
    rw [←map_pow,show (starMap F b)^4=1 from hfour,map_one]
  obtain ⟨heq,hk⟩ := Representation.order_four_fixed_plane_of_commuting_three_group
    σ (zpowers z) hZ hfixed hd _ h4 (by rw [hsq]; exact hr) hcomm
  have hsq' : σ (starMap F a)=ρ a := congrArg (fun f => f a) hσ
  have hb' : σ (starMap F b)=ρ b := congrArg (fun f => f b) hσ
  rw [hsq,hsq',hb'] at heq
  rw [hb'] at hk
  have hQV : Q T L ≤ centralizer (V : Set G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    rw [←h.centralizer_LT_at structural]
    exact inf_le_right
  have hle : s.imageSpace V ≤ (ρ b-1).ker := by
    intro v hv
    exact sub_eq_zero.mpr (s.fixed_on_imageSpace_of_commutator_le (Q T L) V
      ((commutator_eq_bot_iff_le_centralizer.mpr hQV).le.trans bot_le) b hb v hv)
  have hdim : Module.finrank (ZMod 2) (s.imageSpace V) = 2 := by
    apply s.imageSpace_finrank_of_index V (le_conjugateSpanBy V F.H) 2
    have hc := relIndex_mul_card_of_le (F.le_seed 1)
    have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hV,hP] at hc
    norm_num at hc ⊢
    omega
  have hker := (Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hk.symm)).symm
  exact ⟨hker,heq.symm.trans hker⟩

/-- The full original critical commutator is the natural seed. -/
theorem extraspecial_critical_commutator_eq_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅F.U,c.Uα⁆ = V := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨a,b,ha,hane,_,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful he c hs
  have hr := (extraspecial_critical_root_fixed_plane h hab structural previous he s c hs
    a b ha hane hb hba (hbo ▸ pow_orderOf_eq_one _)).2
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hp : F.Vi 1 ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_reverse_intersection_commutator_of_normal_card_two h hab structural
      (h.flag_escape_at F previous) hn s c hs htwo,commutator_comm]
    exact commutator_mono le_rfl inf_le_left
  have him : s.imageSpace V ≤ s.imageSpace ⁅F.U,c.Uα⁆ := by
    rw [←hr]
    exact s.displacement_range_le_imageSpace_of_commutator_le c.Uα ⁅F.U,c.Uα⁆
      (commutator_comm _ _).le a ha
  have hVC : V ≤ ⁅F.U,c.Uα⁆ := by
    intro v hv
    let vU : F.U := ⟨v,le_conjugateSpanBy V F.H hv⟩
    apply (s.coordinates_mem_imageSpace_iff_of_kernel_le _ hp vU).mp
    exact him ((s.mem_imageSpace_iff V _).mpr ⟨vU,hv,rfl⟩)
  apply (eq_of_le_of_card_ge hVC ?_).symm
  rw [critical_commutator_card_of_normal_card_two h hab structural
    (h.flag_escape_at F previous) hn s c hs htwo,h.seed_card]
  decide

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The order-four actor on the remaining order-sixteen interval

The original point core supplies a square root in Q of the selected critical
involution. On a point-central chief four-space, the square moves at least
two dimensions. Its root has order four and a fixed line. Consequently Q
cannot fix the reciprocal centralizer modulo the lower chief endpoint:
that would put a two-dimensional displacement inside the fixed line.

The final application constructs the literal binary chief action and
strengthens the existing original-group alternatives. It retains the exact
kernel O₂(H)L₁, both central flanks, and the central and faithful order-64
branches. No recognition callback or later Data is assumed.
The remaining ambient containment [Q,C_{Uα}(U)] ≤ U would exclude the
order-sixteen branch, but is not proved here. The residual classification
and four-input source assembly through 14.7.52 remain open.

Source: Aschbacher–Smith, 14.7.15(2), 14.7.16(3), and 14.7.20(2),
printed pp.1047–1049. The linear fixed-line argument is structural.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- On the remaining four-dimensional chief section, a literal Q-element
squares to the critical actor and has a one-dimensional fixed space. -/
theorem extraspecial_four_chief_order_four_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 4)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ a b : F.H, (a : G) ∈ c.Uα ∧ (b : G) ∈ Q T L ∧
      (starMap F b)^2=starMap F a ∧ orderOf (starMap F b)=4 ∧
      (ρ b)^2=ρ a ∧ (ρ b)^4=1 ∧
      2 ≤ Module.finrank (ZMod 2) (ρ a-1).range ∧
      Module.finrank (ZMod 2) (ρ b-1).ker=1 := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  subst ρ
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  obtain ⟨a,b,ha,_,ha2,hne,hcenter,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful ⟨e⟩ c hs
  have hlower := extraspecial_center_kernel_dimension_bound σ P hP hZ hmP
    (starMap F a) ha2 hne hcenter
  have hr : 2 ≤ Module.finrank (ZMod 2) (σ (starMap F a)-1).range := by
    rw [hd] at hlower
    omega
  have hsq : (σ (starMap F b))^2=σ (starMap F a) := by rw [←map_pow,hba]
  have hb4 : (starMap F b)^4=1 := hbo ▸ pow_orderOf_eq_one (starMap F b)
  have h4 : (σ (starMap F b))^4=1 := by rw [←map_pow,hb4,map_one]
  have h2ne : (σ (starMap F b))^2≠1 := by
    intro hzero
    rw [hsq] at hzero
    rw [hzero,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  have hrank : Module.finrank (ZMod 2) ((σ (starMap F b))^2-1).range≠1 := by
    rw [hsq]
    omega
  exact ⟨a,b,ha,hb,hba,hbo,hsq,h4,hr,
    LinearMap.order_four_fixed_line hd _ h4 h2ne hrank⟩

/-- An order-sixteen chief section forces Q to move the reciprocal centralizer
modulo its literal lower endpoint. -/
theorem extraspecial_four_chief_core_moves_reciprocal_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 4)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ¬ ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ N := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨a,b,ha,hb,_,_,_,_,hr,hfix⟩ := extraspecial_four_chief_order_four_actor
    h hab structural previous faithful he hB hUN s hp hm hd c hs
  intro hcomm
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hA := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hmove : ⁅c.Uα,B⁆ ≤ c.Uα ⊓ centralizer (F.U : Set G) := by
    rw [commutator_comm]
    exact (commutator_mono hB le_rfl).trans
      (centralizer_critical_commutator_of_normal_card_two h hab structural
        (h.flag_escape_at F previous) hn sU c hs hA)
  have hle : (ρ a-1).range ≤ (ρ b-1).ker := by
    intro v hv
    change ρ b v-v=0
    exact sub_eq_zero.mpr (s.fixed_on_imageSpace_of_commutator_le (Q T L)
      (c.Uα ⊓ centralizer (F.U : Set G)) hcomm b hb v
      (s.displacement_range_le_imageSpace_of_commutator_le c.Uα
        (c.Uα ⊓ centralizer (F.U : Set G)) hmove a ha hv))
  have hdim := Submodule.finrank_mono hle
  omega

open NoncentralChiefRefinement in
/-- Construct the action on the actual order-sixteen interval and apply the
order-four-root obstruction to its literal reciprocal centralizer. -/
theorem extraspecial_sixteen_interval_core_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 16)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ¬ ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ N.val.map F.H.subtype := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let C := (centralizer (F.U : Set G)).subgroupOf F.H
  have hC : IsPGroup 2 C :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
  have hBC' : B.val ≤ C := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hC.to_le hBC')
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hd : Module.finrank (ZMod 2) (Additive (Section N B)) = 4 := by
    have hh : Nat.card (Additive (Section N B)) = 16 := hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hh
  exact extraspecial_four_chief_core_moves_reciprocal_centralizer h hab structural previous faithful
    he hBC hUN s ((commutator_mono hBC le_rfl).trans (hp.trans hUN)) hm hd c hs

open NoncentralChiefRefinement in
/-- The original centralizer-core alternatives, retaining the exact interval
kernel and both central flanks, now require Q-movement of every selected
reciprocal centralizer in the order-sixteen branch. -/
theorem extraspecial_centralizer_core_reduction_with_reciprocal_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) ∨
    (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        Nat.card (Section N B) = 16 ∧
        (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U ∧
        ∀ c : CriticalPath (L := L) F, c.RankSelection →
          ¬ ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ N.val.map F.H.subtype) := by
  rcases extraspecial_centralizer_core_reduction_no_four h hab structural previous faithful he
    with hcase | ⟨hp,N,B,hNB,hUN,hBC,hm,hc,hker,hupper,hlower⟩
  · exact Or.inl hcase
  · refine Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,hc,hker,hupper,hlower,?_⟩
    intro c hs
    exact extraspecial_sixteen_interval_core_movement h hab structural previous faithful he
      N B hNB hUN hBC hp hm hc c hs
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Excluding the original order-sixteen centralizer interval

Even kernel growth bounds every original point-core actor by order four.
Rank one makes each nontrivial actor either the critical involution or a
square root of it. Its action therefore gives [Q,C_U(Uα)] ≤ V. The actual
L-interchange of the two critical spans preserves Q and V, yielding the
reciprocal containment [Q,C_{Uα}(U)] ≤ V. This contradicts the order-sixteen
interval's previously proved movement obstruction.

The final application removes that interval from the original centralizer
series. It proves O₂(L₁) = O₂(K), retaining the central branch and the faithful
order-64 interval with exact kernel O₂(H) and both central flanks. It assumes
no later Data or recognition record. The remaining extraspecial exclusion,
residual classification and four-input assembly through 14.7.52 are still open.
Source: Aschbacher–Smith, 14.7.15(2), 14.7.16(3),(5) and 14.7.20(2),(3),
printed pp.1047–1049, refs/quasithin.pdf.
-/
public noncomputable section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual point-core image has exponent dividing four. -/
theorem extraspecial_core_fourth_power
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (b : F.H) (hb : (b : G) ∈ Q T L) : (starMap F b)^4=1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,hf,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
  have hZ : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hz)
  have hfixed : invariants (σ.comp (zpowers z).subtype) = ⊥ := by
    apply bot_unique
    intro v hv
    exact hfree v (hv ⟨z,mem_zpowers z⟩)
  have hbR : starMap F b ∈ star F (F.Ri L 1) := by
    rw [←(core_product_of_point_normal h hab structural hn).2]
    exact mem_map_of_mem (starMap F) hb
  have hcomm : ∀ z' : zpowers z, Commute (σ z') (σ (starMap F b)) := by
    intro z'
    have hc := point_core_star_centralizes_of_normal h structural hn hbR
    exact (show Commute (z' : HStar F.H) (starMap F b) from
      hc z' (hgen ▸ z'.property)).map σ
  have hRS : star F (F.Ri L 1) ≤ star F (T : Subgroup G) := by
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hp : IsPGroup 2 (star F (F.Ri L 1)) :=
    (T.isPGroup'.comap_subtype.map (starMap F)).to_le hRS
  obtain ⟨n,hnpow⟩ := hp.exists_orderOf_eq_pow ⟨starMap F b,hbR⟩
  have hpow : (σ (starMap F b))^(2^n)=1 := by
    rw [←map_pow]
    have hh : (starMap F b)^(2^n)=1 := congrArg Subtype.val
      (hnpow ▸ pow_orderOf_eq_one (⟨starMap F b,hbR⟩ : star F (F.Ri L 1)))
    rw [hh,map_one]
  have hc := Representation.two_power_cube_zero_of_commuting_three_group
    σ (zpowers z) hZ hfixed hd _ hpow hcomm
  have h4 : (σ (starMap F b)-1)^4=0 := by rw [show 4=3+1 from rfl,pow_succ,hc,zero_mul]
  let : Nontrivial (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) :=
    Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)))
  let : CharP (Module.End (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U))) 2 :=
    charP_of_injective_algebraMap' (ZMod 2) 2
  apply hf
  rw [map_pow,map_one]
  have heq : (σ (starMap F b)-1)^4=(σ (starMap F b))^4-1 := by
    simpa only [show 2^2=4 from rfl,one_pow] using
      sub_pow_char_pow_of_commute 2 2 (Commute.one_right (σ (starMap F b)))
  exact sub_eq_zero.mp (heq.symm.trans h4)

/-- The core moves the critical centralizer only inside the original seed. -/
theorem extraspecial_core_critical_centralizer_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅Q T L,F.U ⊓ centralizer (c.Uα : Set G)⁆ ≤ V := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨a,b,ha,hane,ha2,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful he c hs
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let R := star F (F.Ri L 1)
  have hRS : R ≤ star F (T : Subgroup G) := by
    dsimp only [R]
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hp : IsPGroup 2 R := (T.isPGroup'.comap_subtype.map (starMap F)).to_le hRS
  let z : R := ⟨starMap F a,mem_map_of_mem (starMap F) (critical_le_Ri_at h structural c ha)⟩
  have hz : z ≠ 1 := fun hh => hane (congrArg Subtype.val hh)
  let : Nontrivial R := nontrivial_of_ne z 1 hz
  have hr := (primeRank_le_iff_elementary_card_le R).mp
    (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
  obtain ⟨t,_,_,huniq⟩ := hp.exists_central_involution_of_no_elementary_four
    (fun E hE hEcard => by have hh := hr E hE; norm_num [hEcard] at hh)
  have hzt : z=t := (huniq z (Subtype.ext ha2)).resolve_left hz
  have hcases (q : F.H) (hq : (q : G) ∈ Q T L) :
      starMap F q=1 ∨ starMap F q=starMap F a ∨ (starMap F q)^2=starMap F a := by
    have hqR : starMap F q ∈ R := by
      dsimp only [R]
      rw [←(core_product_of_point_normal h hab structural hn).2]
      exact mem_map_of_mem (starMap F) hq
    let x : R := ⟨starMap F q,hqR⟩
    have hx4 : x^4=1 := Subtype.ext (extraspecial_core_fourth_power h hab structural previous ⟨e⟩ q hq)
    rcases huniq (x^2) (by simpa only [←pow_mul] using hx4) with hx|hx
    · rcases huniq x hx with hx|hx
      · exact Or.inl (congrArg Subtype.val hx)
      · exact Or.inr (Or.inl (congrArg Subtype.val (hx.trans hzt.symm)))
    · exact Or.inr (Or.inr (congrArg Subtype.val (hx.trans hzt.symm)))
  have hmove (q : F.H) (hq : (q : G) ∈ Q T L)
      (v : Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) (hv : ρ a v=v) :
      ρ q v-v ∈ s.imageSpace V := by
    rcases hcases q hq with hq1|hqa|hqa
    · have hq' : ρ q=1 := by
        rw [←hσ]
        change σ (starMap F q)=1
        rw [hq1,map_one]
      simp only [hq',Module.End.one_apply,sub_self,Submodule.zero_mem]
    · have hq' : ρ q=ρ a := by
        rw [←hσ]
        change σ (starMap F q)=σ (starMap F a)
        rw [hqa]
      simp only [hq',hv,sub_self,Submodule.zero_mem]
    · have hk := (extraspecial_critical_root_fixed_plane h hab structural previous ⟨e⟩ s c hs
        a q ha hane hq hqa (extraspecial_core_fourth_power h hab structural previous ⟨e⟩ q hq)).1
      have hsquare : (ρ q)^2=ρ a := by
        rw [←hσ]
        change (σ (starMap F q))^2=σ (starMap F a)
        rw [←map_pow,hqa]
      let : Nontrivial (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) :=
        Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank (ZMod 2)
          (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)))
      let : CharP (Module.End (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U))) 2 :=
        charP_of_injective_algebraMap' (ZMod 2) 2
      have hsquare' : (ρ q-1)^2=ρ a-1 := by
        rw [sub_pow_char_of_commute 2 (Commute.one_right (ρ q)),hsquare,one_pow]
      rw [←hk]
      change (ρ q-1) ((ρ q-1) v)=0
      change ((ρ q-1)^2 : Module.End (ZMod 2) _) v=0
      rw [hsquare']
      exact sub_eq_zero.mpr hv
  apply commutator_le.mpr
  intro q hq v hv
  let qH : F.H := ⟨q,Q_le_H F hq⟩
  let vU : F.U := ⟨v,hv.1⟩
  have hfix : ρ a (s.coordinates vU).toAdd=(s.coordinates vU).toAdd := by
    have hc : ⁅c.Uα,F.U ⊓ centralizer (c.Uα : Set G)⁆ ≤ F.Vi 1 :=
      ((commutator_comm _ _).trans
        (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right)).le.trans bot_le
    exact s.fixed_on_imageSpace_of_commutator_le c.Uα
      (F.U ⊓ centralizer (c.Uα : Set G)) hc a ha _
      ((s.mem_imageSpace_iff _ _).mpr ⟨vU,hv,rfl⟩)
  have hcU : ⁅q,v⁆ ∈ F.U :=
    (le_normalizer_iff_commutator_le_right.mp ((Q_le_H F).trans s.normalized))
      (commutator_mem_commutator hq hv.1)
  apply (s.coordinates_mem_imageSpace_iff_of_kernel_le V (F.le_seed 1) ⟨⁅q,v⁆,hcU⟩).mp
  change (s.coordinates ((⟨q*v*q⁻¹,
    (mem_normalizer_iff.mp (s.normalized qH.property) v).mp vU.property⟩ : F.U)*vU⁻¹)).toAdd ∈ s.imageSpace V
  rw [map_mul,map_inv]
  change (s.coordinates ⟨q*v*q⁻¹,_⟩).toAdd + -(s.coordinates vU).toAdd ∈ s.imageSpace V
  rw [s.equivariant qH vU,←sub_eq_add_neg]
  exact hmove qH hq _ hfix

/-- The original critical point lies in the seed, and an element of L
interchanges the two spans without changing the core Q. -/
theorem extraspecial_critical_interchange
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    c.Zα ≤ V ∧ c.b=3 ∧
      ∃ g ∈ L, F.U.conjBy g=c.Uα ∧ c.Uα.conjBy g=F.U ∧
        (Q T L).conjBy g=Q T L ∧ V.conjBy g=V := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hZ : c.Zα ≤ V := by
    rw [←critical_intersection_commutator_of_normal_card_two h hab structural
      (h.flag_escape_at F previous) hn s c hs htwo]
    exact (commutator_mono inf_le_left le_rfl).trans_eq
      (extraspecial_critical_commutator_eq_seed h hab structural previous faithful ⟨e⟩ c hs)
  obtain ⟨g,hg,hfirst,hsecond,_⟩ := G2Source.critical_span_core_interchange h c hZ
  have hQN : L ≤ normalizer (Q T L : Set G) :=
    (le_sup_left : L ≤ L ⊔ (T : Subgroup G)).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  exact ⟨hZ,G2Source.critical_length_three h c hZ,g,hg,hfirst,hsecond,
    mem_normalizer_iff_map_conj_eq.mp (hQN hg),
    mem_normalizer_iff_map_conj_eq.mp (h.chosen.normalizes hg)⟩

/-- The literal reciprocal centralizer is moved by Q only inside V. -/
theorem extraspecial_core_reciprocal_centralizer_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ V := by
  obtain ⟨_,_,g,_,hfirst,hsecond,hQ,hV⟩ :=
    extraspecial_critical_interchange h hab structural previous faithful he c hs
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
    (extraspecial_core_critical_centralizer_commutator h hab structural previous faithful he c hs)
  have hcent : (centralizer (c.Uα : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer (c.Uα.conjBy g : Set G) := by
    apply le_antisymm
    · exact map_centralizer_le_centralizer_image _ _
    · intro x hx
      refine ⟨(MulAut.conj g).symm x,?_,(MulAut.conj g).apply_symm_apply x⟩
      intro y hy
      apply (MulAut.conj g).injective
      simpa only [map_mul,MulEquiv.apply_symm_apply] using
        hx ((MulAut.conj g) y) (mem_map_of_mem _ hy)
  rw [map_commutator,map_inf _ _ _ (MulAut.conj g).injective,hcent] at hh
  change ⁅(Q T L).conjBy g,F.U.conjBy g ⊓ centralizer (c.Uα.conjBy g : Set G)⁆ ≤ V.conjBy g at hh
  rwa [hQ,hfirst,hsecond,hV] at hh

open NoncentralChiefRefinement in
/-- Exclude the actual order-sixteen interval with its original quotient map. -/
theorem extraspecial_sixteen_interval_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 16) : False := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  exact extraspecial_sixteen_interval_core_movement h hab structural previous faithful ⟨e⟩
    N B hNB hUN hBC hp hm hc c hs
    ((extraspecial_core_reciprocal_centralizer_commutator h hab structural previous faithful ⟨e⟩ c hs).trans
      ((le_conjugateSpanBy V F.H).trans hUN))

open NoncentralChiefRefinement in
/-- The original centralizer series is K-central or has one faithful six-space.
Both central flanks and the exact action kernel of the surviving interval
are retained; neither the central nor the faithful branch is discarded. -/
theorem extraspecial_centralizer_core_reduction_no_small_intervals
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) := by
  rcases extraspecial_centralizer_core_reduction_no_four h hab structural previous faithful he
    with hh | ⟨hp,N,B,hNB,hUN,hBC,hm,hc,_⟩
  · exact hh
  · exact (extraspecial_sixteen_interval_impossible h hab structural previous faithful he
      N B hNB hUN hBC hp hm hc).elim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original residual-core center and its moved chief factor

Put P = O₂(K) and Z = Z(P), both embedded in the original group. The
commutator pairing gives U ∩ Z = V₁. In the central alternative of
14.7.20, [Z,K] lies in V₁; two-perfect commutator idempotence therefore
proves Z ≤ Z(K).

In the faithful alternative, K acts on the abelian Z through its odd
quotient. Coprime splitting separates [Z,K] from the fixed subgroup.
The lower central flank meets Z only in that fixed subgroup, so the
literal inclusion of [Z,K] into the chief numerator has trivial kernel.
If Z is not central in K, chiefness makes this inclusion surjective onto
the original order-64 interval. The resulting equivariant isomorphism
proves [Z,K] is elementary of order 64 and has exact H-action kernel O₂(H).
No moved-center witness or later Data is assumed in the original application.

This supplies the center reduction in Aschbacher–Smith 14.7.21(2), printed
p.1050, refs/quasithin.pdf. Excluding this moved center by Thompson–Baumann
control, the maximal-normalizer clause, and the remaining local reductions
through 14.7.52 are not asserted here. Genuine earlier structural and
faithful-classification inputs retain their existing source producers.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialCenterMovement_centerControl_normalized :
    F.H ≤ normalizer ((center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype : Set G) :=
  (le_normalizer_embedded_pResidual 2 F.H).trans
    ((normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))).trans
      (normalizer_le_normalizer_characteristic_image ((K F).pCoreIn 2)
        (center ((K F).pCoreIn 2))))

/-- The literal core center meets U precisely in the original point. -/
theorem extraspecial_core_center_inf_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    F.U ⊓ (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype = F.Vi 1 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hUP : F.U ≤ (K F).pCoreIn 2 := span_le_residual_core h hab
  rw [map_center_subtype_eq_inf_centralizer,←inf_assoc,inf_eq_left.mpr hUP]
  exact extraspecial_residual_core_centralizer h hab structural previous hex hcard hexp

/-- The central branch of 14.7.20 implies the center clause of 14.7.21. -/
theorem extraspecial_core_center_central_of_centralizer_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
      (center (K F)).map (K F).subtype := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  have hZP : Z ≤ P := map_subtype_le _
  have hZK : Z ≤ K F := hZP.trans (pCoreIn_le 2 _)
  have hnorm : K F ≤ normalizer (Z : Set G) :=
    (map_subtype_le _).trans ExtraspecialCenterMovement_centerControl_normalized
  have hZC : Z ≤ centralizer (F.U : Set G) := by
    have hz : Z ≤ centralizer (P : Set G) := by
      rw [show Z = P ⊓ centralizer (P : Set G) from map_center_subtype_eq_inf_centralizer P]
      exact inf_le_right
    exact hz.trans (centralizer_le (span_le_residual_core h hab))
  have hmove : ⁅Z,K F⁆ ≤ F.Vi 1 := by
    rw [←extraspecial_core_center_inf_span h hab structural previous he]
    exact le_inf ((commutator_mono hZC le_rfl).trans hc)
      (le_normalizer_iff_commutator_le_left.mp hnorm)
  have hpoint : F.Vi 1 ≤ centralizer (K F : Set G) :=
    (le_centralizer_iff.mp (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))).trans (centralizer_le (map_subtype_le _))
  have hid := commutator_isPPerfect_idempotent (K F) Z
    (isPPerfect_embedded_pResidual 2 F.H) ((isPGroup_pCoreIn 2 _).to_le hZP) hnorm
  have hz : ⁅Z,K F⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [←hid]
    exact (commutator_mono hmove le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hpoint).le
  rw [map_center_subtype_eq_inf_centralizer (K F)]
  exact le_inf hZK (commutator_eq_bot_iff_le_centralizer.mp hz)
private theorem ExtraspecialCenterMovement_centerControl_splitting
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let P := (K F).pCoreIn 2
    let Z := (center P).map P.subtype
    ⁅Z,K F⁆ ⊔ (Z ⊓ centralizer (K F : Set G)) = Z ∧
      ⁅Z,K F⁆ ⊓ (Z ⊓ centralizer (K F : Set G)) = ⊥ := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  let : IsMulCommutative Z := map_isMulCommutative _ _
  have hn : K F ≤ normalizer (Z : Set G) :=
    (map_subtype_le _).trans ExtraspecialCenterMovement_centerControl_normalized
  let f := Z.normalizerMonoidHom.comp (inclusion hn)
  have hk : pCore 2 (K F) ≤ f.ker := by
    intro p hp
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (p : G) * (z : G) * (p : G)⁻¹ = (z : G)
    have hz : (z : G) ∈ P ⊓ centralizer (P : Set G) := by
      simpa only [Z,map_center_subtype_eq_inf_centralizer] using z.property
    rw [hz.2 p (mem_map_of_mem (K F).subtype hp),mul_inv_cancel_right]
  have hc : Nat.card f.range ∣ 27 := by
    obtain ⟨e⟩ := he
    have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
    rw [←index_ker]
    simpa only [index_eq_card,hcard] using index_dvd_of_le hk
  have hf : IsPGroup 3 f.range := isPGroup_iff_card_dvd_pow.mpr ⟨3,hc⟩
  have hz : IsPGroup 2 Z := (isPGroup_pCoreIn 2 (K F)).to_le (map_subtype_le _)
  exact commutator_centralizer_decomposition_of_coprime_image Z (K F) hn
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) f.range Z hf hz)

open NoncentralChiefRefinement in
/-- Both central flanks disappear on the moved core center. This retains
its literal inclusion in the faithful chief numerator and trivial lower kernel. -/
theorem extraspecial_moved_core_center_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H)
    (hupper : ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype)
    (hlower : ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) :
    let Z := (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype
    ⁅Z,K F⁆ ≤ B.val.map F.H.subtype ∧
      ⁅Z,K F⁆ ⊓ N.val.map F.H.subtype = ⊥ := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  have hZP : Z ≤ P := map_subtype_le _
  have hnZ : F.H ≤ normalizer (Z : Set G) := ExtraspecialCenterMovement_centerControl_normalized
  have hKZ := (show K F ≤ F.H from map_subtype_le _).trans hnZ
  have hDZ : ⁅Z,K F⁆ ≤ Z := le_normalizer_iff_commutator_le_left.mp hKZ
  have hZC : Z ≤ centralizer (F.U : Set G) := by
    have hz : Z ≤ centralizer (P : Set G) := by
      rw [show Z = P ⊓ centralizer (P : Set G) from map_center_subtype_eq_inf_centralizer P]
      exact inf_le_right
    exact hz.trans (centralizer_le (span_le_residual_core h hab))
  have hNN : F.H ≤ normalizer (N.val.map F.H.subtype : Set G) := by
    have hh := (map_mono (f := F.H.subtype)
      (show (⊤ : Subgroup F.H) ≤ normalizer (N.val : Set F.H) from le_normalizer_of_normal)).trans
        (N.val.le_normalizer_map F.H.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  let A := Z ⊓ N.val.map F.H.subtype
  have hKA : K F ≤ normalizer (A : Set G) :=
    ((map_subtype_le _).trans (le_inf hnZ hNN)).trans inf_normalizer_le_normalizer_inf
  have hAP : A ≤ P := inf_le_left.trans hZP
  have hmove : ⁅A,K F⁆ ≤ F.Vi 1 := by
    rw [←extraspecial_core_center_inf_span h hab structural previous he]
    exact le_inf ((commutator_mono inf_le_right le_rfl).trans hlower)
      ((le_normalizer_iff_commutator_le_left.mp hKA).trans inf_le_left)
  have hpoint : F.Vi 1 ≤ centralizer (K F : Set G) :=
    (le_centralizer_iff.mp (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))).trans (centralizer_le (map_subtype_le _))
  have hid := commutator_isPPerfect_idempotent (K F) A
    (isPPerfect_embedded_pResidual 2 F.H) ((isPGroup_pCoreIn 2 _).to_le hAP) hKA
  have hAC : A ≤ centralizer (K F : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [←hid]
    exact (commutator_mono hmove le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hpoint).le
  refine ⟨(commutator_mono hZC le_rfl).trans hupper,?_⟩
  apply le_bot_iff.mp
  exact (le_inf inf_le_left (le_inf (inf_le_left.trans hDZ)
    ((inf_le_inf hDZ le_rfl).trans hAC))).trans (ExtraspecialCenterMovement_centerControl_splitting he).2.le

omit [Finite G] in
private theorem ExtraspecialCenterMovement_centerControl_moved_normalized :
    F.H ≤ normalizer
      ((⁅(center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype,K F⁆ : Subgroup G) : Set G) := by
  intro x hx
  have hk : (K F).map (MulAut.conj x).toMonoidHom = K F :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_embedded_pResidual 2 F.H hx)
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (ExtraspecialCenterMovement_centerControl_normalized hx)]
  exact congrArg (fun A : Subgroup G =>
    ⁅(center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype,A⁆) hk

open NoncentralChiefRefinement in
omit [Finite G] in
private theorem ExtraspecialCenterMovement_centerControl_chief_coordinates
    (N B : NormalNode F.H) (hNB : N ⋖ B) (D : Subgroup G)
    (hDB : D ≤ B.val.map F.H.subtype) (hn : F.H ≤ normalizer (D : Set G))
    (hcap : D ⊓ N.val.map F.H.subtype = ⊥) (hne : D ≠ ⊥) :
    ∃ f : D →* Section N B, Function.Bijective f ∧
      ∀ (a : F.H) (d : D),
        f (D.normalizerMonoidHom (inclusion hn a) d) = sectionAction N B a (f d) := by
  have hBH : B.val.map F.H.subtype ≤ F.H := map_subtype_le _
  let j : D →* B.val := {
    toFun := fun d => ⟨⟨d,hBH (hDB d.property)⟩,
      (mem_map_iff_mem F.H.subtype_injective).mp (hDB d.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let f := (QuotientGroup.mk' (N.val.subgroupOf B.val)).comp j
  have he (a : F.H) (d : D) :
      f (D.normalizerMonoidHom (inclusion hn a) d) = sectionAction N B a (f d) := rfl
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro d hd
    apply Subtype.ext
    have hdN : (d : G) ∈ N.val.map F.H.subtype := by
      have hh := (QuotientGroup.eq_one_iff (N := N.val.subgroupOf B.val) (j d)).mp hd
      exact mem_map_of_mem F.H.subtype hh
    have hh := hcap ▸ (show (d : G) ∈ D ⊓ N.val.map F.H.subtype from ⟨d.property,hdN⟩)
    exact hh
  have ht : f.range = ⊤ := by
    apply (chief_irreducible N B hNB f.range ?_).resolve_left
    · intro hb
      apply hne
      apply bot_unique
      intro d hd
      change d=1
      have hd1 : (⟨d,hd⟩ : D)=1 := hi (by
        have hh : f ⟨d,hd⟩ ∈ f.range := ⟨⟨d,hd⟩,rfl⟩
        rw [hb] at hh
        exact hh.trans (map_one f).symm)
      exact congrArg Subtype.val hd1
    · intro a x hx
      obtain ⟨d,rfl⟩ := hx
      exact ⟨D.normalizerMonoidHom (inclusion hn a) d,he a d⟩
  exact ⟨f,⟨hi,MonoidHom.range_eq_top.mp ht⟩,he⟩

open NoncentralChiefRefinement in
/-- If the original core center is not central in K, its moved subgroup
is the faithful six-dimensional chief factor itself, with its actual action.
This is the remaining obstruction in the center argument of 14.7.21(2). -/
theorem extraspecial_noncentral_core_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
      (center (K F)).map (K F).subtype) :
    let Z := (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype
    let D := ⁅Z,K F⁆
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
      Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
      D ≤ B.val.map F.H.subtype ∧ D ⊓ N.val.map F.H.subtype = ⊥ ∧
      Nat.card D = 64 ∧ IsElementaryAbelian 2 D ∧
      ∃ hn : F.H ≤ normalizer (D : Set G),
        (D.normalizerMonoidHom.comp (inclusion hn)).ker = pCore 2 F.H ∧
        ∃ e : D ≃* Section N B, ∀ (a : F.H) (d : D),
          e (D.normalizerMonoidHom (inclusion hn a) d) = sectionAction N B a (e d) := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  let D := ⁅Z,K F⁆
  have hne : D ≠ ⊥ := by
    intro hb
    apply hnc
    rw [map_center_subtype_eq_inf_centralizer (K F)]
    exact le_inf ((map_subtype_le _).trans (pCoreIn_le 2 _))
      (commutator_eq_bot_iff_le_centralizer.mp hb)
  obtain ⟨_,hc | ⟨N,B,hNB,hUN,hBC,hm,hcard,hker,hu,hl⟩⟩ :=
    extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he
  · exact (hnc (extraspecial_core_center_central_of_centralizer_central
      h hab structural previous he hc)).elim
  obtain ⟨hDB,hcap⟩ := extraspecial_moved_core_center_interval h hab structural previous he N B hu hl
  have hn : F.H ≤ normalizer (D : Set G) := ExtraspecialCenterMovement_centerControl_moved_normalized
  obtain ⟨f,hf,heq⟩ := ExtraspecialCenterMovement_centerControl_chief_coordinates N B hNB D hDB hn hcap hne
  let e := MulEquiv.ofBijective f hf
  have hDC : Nat.card D = 64 := (Nat.card_congr e.toEquiv).trans hcard
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hBQ : B.val.map F.H.subtype ≤ F.H.pCoreIn 2 := hBC.trans
    (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) s)
  have hBtwo : IsPGroup 2 B.val := by
    have hh := (isPGroup_pCoreIn 2 F.H).to_le hBQ
    apply hh.of_injective ((F.H.subtype).subgroupMap B.val)
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : B.val.map F.H.subtype => (x : G)) hab
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB hBtwo
  have hDe : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective f hf.1
  have hact : (D.normalizerMonoidHom.comp (inclusion hn)).ker = pCore 2 F.H := by
    rw [←hker]
    ext a
    change D.normalizerMonoidHom (inclusion hn a) = 1 ↔ sectionAction N B a = 1
    constructor
    · intro ha
      apply MulEquiv.ext
      intro w
      obtain ⟨d,rfl⟩ := hf.2 w
      exact (heq a d).symm.trans (congrArg f (DFunLike.congr_fun ha d))
    · intro ha
      apply MulEquiv.ext
      intro d
      apply hf.1
      rw [heq,ha]
      rfl
  exact ⟨N,B,hNB,hUN,hBC,hm,hcard,hker,hDB,hcap,hDC,hDe,hn,hact,e,heq⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Center control in the original Heisenberg branch

The moved center D = [Z(O₂(K)),K], if nontrivial, is the actual faithful
six-dimensional chief factor constructed in ExtraspecialCenterMovement.
Its coordinates have trivial kernel, and its H-action has kernel exactly
O₂(H).

Every elementary subgroup of the point-core image has order at most two
and centralizes the point cubic. The latter acts without fixed points on
the chief module. Both the whole module and each such actor's fixed space
therefore have even dimension, excluding an FF offender. The maximum
elementary subgroup index bound now puts J(R₁) in O₂(H). Consequently
D lies in Ω₁(Z(J(R₁))), so Baum(R₁) lies in C_H(D) = O₂(H).
Baumann heredity gives Baum(R₁) = Baum(O₂(H)), normalized by H.
This contradicts the original Baumann-normalizer bound of 14.7.16(7).
Thus the whole center of O₂(K) is central in K.

This proves the center clause 14.7.21(2) of Aschbacher–Smith, printed
p.1050, refs/quasithin.pdf. The maximal-overgroup clause 14.7.21(1)
and the subsequent residual exclusion remain separate source steps.
The genuine earlier structural, faithful-classification and 14.7.10
inputs remain explicit with their existing producers; their final
source discharge belongs to qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

private theorem ExtraspecialCenterControl_centerControl_not_offender {X W : Type*} [Group X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) X W) (hf : Function.Injective σ)
    (Z A : Subgroup X) (hZ : IsPGroup 3 Z)
    (hz : invariants (σ.comp Z.subtype) = ⊥)
    (hc : A ≤ centralizer (Z : Set X)) (hcard : Nat.card A ≤ 2) : ¬ IsOffender σ A := by
  intro hA
  let I : Subrepresentation (σ.comp Z.subtype) := {
    toSubmodule := fixedSpace σ A
    apply_mem_toSubmodule z v hv a := by
      change σ a (σ z v)=σ z v
      have he := congrArg (fun x => σ x v) (hc a.property z z.property)
      simp only [map_mul,Module.End.mul_apply] at he
      rw [←he]
      exact congrArg (σ z) (hv a) }
  have hI : invariants I.toRepresentation = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    have hh : (v : W) ∈ invariants (σ.comp Z.subtype) :=
      fun z => congrArg Subtype.val (hv z)
    change (v : W) = 0
    simpa only [hz,Submodule.mem_bot] using hh
  have hdim := orderOf_two_dvd_finrank_of_isPGroup (σ.comp Z.subtype)
    Nat.prime_three (by decide) hZ hz
  have hfixed := orderOf_two_dvd_finrank_of_isPGroup I.toRepresentation
    Nat.prime_three (by decide) hZ hI
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at hdim hfixed
  have heq := fixedCodim_add_finrank σ A
  have hpos := fixedCodim_pos_of_faithful σ hf hA.1.1
  have hr : rank A ≤ 1 := by
    simpa only [rank,show Nat.log 2 2 = 1 from rfl] using
      (Nat.log_mono_right (b := 2) hcard)
  have hb := hA.2
  change 2 ∣ Module.finrank (ZMod 2) (fixedSpace σ A) at hfixed
  omega

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialCenterControl_centerControl_point_not_offender
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W) [σ.IsIrreducible]
    (hf : Function.Injective σ) (A : Subgroup (HStar F.H))
    (hAR : A ≤ star F (F.Ri L 1)) : ¬ IsOffender σ A := by
  intro hA
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let Z := star F (F.Li L 1)
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZcard : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hn
  have hZ : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hz : invariants (σ.comp Z.subtype) = ⊥ := by
    by_contra hfix
    have hk := le_ker_of_normal_invariants_ne_bot σ Z hfix
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf] at hk
    have hb : Z = ⊥ := le_bot_iff.mp hk
    rw [hb,Nat.card_unique] at hZcard
    contradiction
  have hsmall : Nat.card A ≤ 2 := by
    let := hA.1.2
    have ha := (primeRank_le_iff_elementary_card_le (star F (F.Ri L 1))).mp
      (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
      (A.subgroupOf (star F (F.Ri L 1))) (IsElementaryAbelian.subgroupOf hAR)
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv,pow_one] using ha
  exact ExtraspecialCenterControl_centerControl_not_offender σ hf Z A hZ hz
    (hAR.trans (point_core_star_centralizes_of_normal h structural hn)) hsmall hA


private theorem ExtraspecialCenterControl_centerControl_baumann_eq
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W) [σ.IsIrreducible]
    (hf : Function.Injective σ) (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hDQ : D ≤ F.H.pCoreIn 2)
    (hn : F.H ≤ normalizer (D : Set G))
    (hker : (D.normalizerMonoidHom.comp (inclusion hn)).ker = pCore 2 F.H)
    (s : BinaryConjugationSection F.H D ⊥ (σ.comp (starMap F))) :
    ChapterB.baumann (F.Ri L 1) = ChapterB.baumann (F.H.pCoreIn 2) := by
  have hkerC : (centralizer (D : Set G)).subgroupOf F.H = pCore 2 F.H := by
    rw [←hker,←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  have hQC : F.H.pCoreIn 2 = F.H ⊓ centralizer (D : Set G) := by
    change (pCore 2 F.H).map F.H.subtype = _
    rw [←hkerC,subgroupOf_map_subtype,inf_comm]
  have hDC : D ≤ centralizer (F.H.pCoreIn 2 : Set G) := by
    apply le_centralizer_iff.mp
    rw [hQC]
    exact inf_le_right
  have hRQ : F.H.pCoreIn 2 ≤ F.Ri L 1 := core_le_point_core
  have hRH : F.Ri L 1 ≤ F.H := (pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hJ : Stellmacher.elementaryAbelianMaxJ (F.Ri L 1) ≤ F.H.pCoreIn 2 := by
    apply sSup_le
    intro A hA
    by_contra hAQ
    let : IsElementaryAbelian 2 A := hA.2.1
    have hAH : A ≤ F.H := hA.1.trans hRH
    have hEA : IsElementaryTwo (star F A) := by
      let : IsElementaryAbelian 2 (A.subgroupOf F.H) := IsElementaryAbelian.subgroupOf hAH
      refine ⟨?_,IsElementaryAbelian.map (starMap F)⟩
      intro hb
      have hh : A.subgroupOf F.H ≤ pCore 2 F.H := by
        simpa only [CriticalFusion.Source.star,Subgroup.map_eq_bot_iff,starMap,QuotientGroup.ker_mk'] using hb
      apply hAQ
      change A ≤ (pCore 2 F.H).map F.H.subtype
      simpa only [map_subgroupOf_eq_of_le hAH] using map_mono (f := F.H.subtype) hh
    have hi : (centralizer (A : Set G)).relIndex D ≤ Nat.card (star F A) := by
      have hh := Stellmacher.maxElementary_fixedIndex_le_relIndex (F.Ri L 1)
        (F.H.pCoreIn 2) A D hRQ hDQ hDC hA
      apply (hh.1.trans hh.2).trans_eq
      change _ = Nat.card ((A.subgroupOf F.H).map (starMap F))
      rw [←relIndex_ker,show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
      have hc : (F.H.pCoreIn 2).subgroupOf F.H = pCore 2 F.H :=
        comap_map_eq_self_of_injective F.H.subtype_injective _
      rw [←hc,relIndex_subgroupOf hAH]
    have ho := s.offender_of_section_index σ (starMap F) A (centralizer (A : Set G))
      (by rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr le_rfl]) hEA hi
    exact ExtraspecialCenterControl_centerControl_point_not_offender h hab structural previous he σ hf (star F A)
      (map_mono (subgroupOf_mono _ hA.1)) ho
  have hDα := Stellmacher.elementary_centralizer_maxJ_le_omegaCenter (F.Ri L 1) D
    (hDQ.trans hRQ) (hDC.trans (centralizer_le hJ))
  have hB : ChapterB.baumann (F.Ri L 1) ≤ F.H.pCoreIn 2 := by
    rw [hQC]
    exact le_inf (inf_le_left.trans hRH) (inf_le_right.trans (centralizer_le hDα))
  exact (Stellmacher.baumann_eq_of_intermediate (F.Ri L 1) (F.H.pCoreIn 2) hB hRQ).symm

open NoncentralChiefRefinement in
/-- The source center conclusion, for the original Heisenberg residual. -/
theorem extraspecial_core_center_central
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
      (center (K F)).map (K F).subtype := by
  by_contra hnc
  obtain ⟨N,B,hNB,hUN,hBC,hm,_,_,hDB,_,_,hDe,hn,hker,e,heq⟩ :=
    extraspecial_noncentral_core_center h hab structural previous faithful he hnc
  let D := ⁅(center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype,K F⁆
  let : IsElementaryAbelian 2 D := hDe
  let : IsElementaryAbelian 2 (Section N B) := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let ρ := binarySectionRepresentation N B
  let s := ambientBinarySection F.H N B hNB.le
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  have hecopy := he
  obtain ⟨ee⟩ := hecopy
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv ee.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr ee.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv ee).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ,hfaith,_,_⟩ := extraspecial_point_noncentral_chief h hab structural previous
    hex hcard hexp hBC hUN s hm
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (starMap F) (QuotientGroup.mk'_surjective _) σ).mp
      (hσ.symm ▸ inferInstanceAs ρ.IsIrreducible)
  have hDH : D ≤ F.H := hDB.trans (map_subtype_le _)
  let sd : BinaryConjugationSection F.H D ⊥ (σ.comp (starMap F)) := {
    section_le := hDH
    kernel_le := bot_le
    normalized := hn
    coordinates := {
      toFun := fun x => Multiplicative.ofAdd (Additive.ofMul (e x))
      map_one' := e.map_one
      map_mul' := e.map_mul }
    onto := e.surjective
    kernel_eq := by
      ext x
      change e x = 1 ↔ (x : G) = 1
      exact e.map_eq_one_iff.trans Subtype.val_inj.symm
    equivariant := by
      intro a x
      rw [hσ]
      exact congrArg Additive.ofMul (heq a x) }
  have hDQ : D ≤ F.H.pCoreIn 2 := by
    let := h.chosen.elementary
    let := hab
    let := elementary_U F
    obtain ⟨ρ₀,⟨s₀⟩⟩ := exists_section F
    exact hDB.trans (hBC.trans
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) s₀))
  have hBaum := ExtraspecialCenterControl_centerControl_baumann_eq h hab structural previous he σ hfaith D hDQ hn hker sd
  apply h.flag_escape_at F previous
  apply le_trans ?_ (extraspecial_baumann_normalizer d h hab structural previous earlier he)
  rw [hBaum]
  exact (F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))).trans
      (Stellmacher.normalizer_le_normalizer_baumann _)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
