module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.BinaryMarked
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.SourceAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.TerminalExclusion
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Excluding both binary star models on the original source

The binary marking theorem constructs the actual positive-rank parabolic
from an unmarked L₄(2) or L₅(2) star equivalence. Its cubic-residual identity
makes X normal in I and puts the original K in C_X(ZS).

Nontriviality of the star action descends to the intrinsic module of X by
A.4.8. The preliminary normal-perfect exclusion in 15.2.23 therefore proves
X is outside Mc. The original Omega action then supplies the exact NI
quotient and kernel. Terminal original-U recognition and corrected
15.2.21(3) give the contradiction, including all binary module subcases.

Only the genuine earlier HStar quotient, Kc orbit, S₃-square quotient,
restricted action, plane involution and no-chi premises remain explicit.
Their source producers and final discharge remain with plane uniqueness.
This proves the binary rows, not the exhaustive marked C.2.7 reduction.

Source: Aschbacher--Smith 15.2.18--23, printed pp.1113--1117;
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X R N : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

omit [Finite G] in
private theorem input_perfect (h : Input KnownSimple.IsKnownSimple I R N X) :
    Group.IsPerfect X := by
  let : Group.IsPerfect (X.subgroupOf I) := h.component.2.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component.1).toMonoidHom)
    (subgroupOfEquivOfLe h.component.1).surjective

/-- Nontriviality of the actual star action detects movement on the intrinsic
signalizer module of the original component, by A.4.8. This also applies
to the remaining nonbinary source rows. -/
theorem input_intrinsic_movement (h : Input KnownSimple.IsKnownSimple I R N X) :
    intrinsicSignalizerModule X ≠ ⊥ := by
  let : Group.IsPerfect X := input_perfect h
  have hp : IsPPerfect 2 X := by
    intro A hA hq
    let := hA
    let := hq.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ A)
  let J := X ⊔ R
  let Q := J.pCoreIn 2
  have hXJ : X ≤ J := le_sup_left
  have hsub : (X.subgroupOf J).IsSubnormal :=
    (normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer h.normalizes)).isSubnormal
  have hn : X ≤ normalizer (Q : Set G) :=
    hXJ.trans (J.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore J))
  have hsig : IsTwoSignalizer X J Q := (isTwoSignalizer_iff _ _ _).mpr
    ⟨pCoreIn_le 2 J,isPGroup_pCoreIn 2 J,hn⟩
  apply (signalizerModule_ne_bot_iff_intrinsic X Q hp (isPGroup_pCoreIn 2 J) hn
    (pCoreAmbient_mono_of_isSubnormalIn X J 2 hXJ hsub)
    (signalizer_commutator_le_pCore X J Q hXJ hsub hp hsig)).mp
  intro hz
  have hc : X ≤ centralizer (omegaOneCenterAmbient Q : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [←signalizerModule_eq_commutator_omegaCenter]
  have hstar : starImage X R X = ⊥ := by
    change (X.subgroupOf J).map (QuotientGroup.mk' (starKernel X R)) = ⊥
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    intro x hx
    change x ∈ centralizer (starV X R : Set J)
    intro v hv
    apply Subtype.ext
    apply hc hx
    change (v : G) ∈ omegaOneCenterAmbient ((pCore 2 J).map J.subtype)
    rw [omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective]
    exact mem_map_of_mem J.subtype hv
  exact starImage_ne_bot_of_bound h.normalizes h.quasisimple
    (kernel_offender_from_source h).1.upper hstar

include d in
/-- The original binary component cannot lie in Mc: its cubic-residual
identity and intrinsic movement invoke the first preliminary exclusion. -/
theorem binary_not_le_partner
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {n : ℕ} (b : BinaryBranch M I X n) :
    ¬ X ≤ Mc := by
  let : Group.IsPerfect X := input_perfect b.source
  have hX := binary_eq_threeResidual (hsource := hsource) hI b
  have hr : primeToResidual 3 X = ⊤ := by
    apply map_injective X.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    have hh := congrArg (Subgroup.map I.subtype)
      (embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 I) le_rfl)
    rw [map_embedded_primeToResidual_of_hom,←hX] at hh
    exact hh
  intro hx
  exact d.no_normal_perfect_threeResidual horbit hI b.source.component.1
    (binary_normalized (hsource := hsource) hI b) hx hr (input_intrinsic_movement b.source)

include d in
/-- Exclude either binary star model on the same selected component.
The marked parabolic, component escape, NI action and terminal seed are
constructed, and corrected 15.2.21(3) supplies the contradiction. -/
theorem normalized_binary_false
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2))
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) : False := by
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  have hs := normalized_component_input (hsource := hsource) hI hcore s
  let b : BinaryBranch M I X n :=
    ⟨hs,hn,binary_model_marked_parabolic d hI hs (s.toSelected.not_chi hno) hn e⟩
  exact SmallActionsSource.binaryBranch_false_from_smallActions d hquotient horbit hI hfit
    (binary_normalized (hsource := hsource) hI b) (binary_not_le_partner d horbit hI b) b
    (binary_eq_threeResidual (hsource := hsource) hI b)
    ((binary_residual_le_M1 d hI b).trans inf_le_left) hpair hNI eNI ho

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
