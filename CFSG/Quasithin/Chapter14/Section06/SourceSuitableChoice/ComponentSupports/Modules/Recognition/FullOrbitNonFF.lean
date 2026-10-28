module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeNonFF
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source
public import Theory.Representation.BinaryOffender.AmbientSubspaceNonFF

/-!
# Faithful non-FF action on the full original seed orbit

The actual component orbit contains the two-residual, and14.6.19 makes the
original actor quotient radical-free. Any action detecting that component
is therefore faithful. Best offenders on an invariant space containing the
marked natural--dual orbit normalize the component and fix that smaller
orbit; generalized Fitting self-centralization then excludes them.

Apply this to the full H-orbit of the same seed in the original U/Z.
F.9.18(6)'s alternatives involving FF on the orbit itself are eliminated.
Either this full orbit is the residual commutator support, or its literal
quotient has faithful action and a strong FF offender. The terminal
exchanged-component application constructs the seed, marking and quadratic
bound from the original hypotheses. The remaining quotient exclusion,
individual full-support equalities and suitable-vector assembly stay with
qt-e-suitable-component-supports. Original14.6.18 remains hsolv, for final
discharge by qt-e-14625-source.

Source: Aschbacher--Smith B.1.5(4), F.9.18(6--7),14.6.22,
printed pp.69,326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


/-- Detecting the original component forces faithfulness on any action
when its Sylow orbit generates the outside group with T. This applies
in particular to noncentral quotients of the original module. -/
theorem source_faithful_of_component_detected
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) X)
    (hdetect : ¬ actorImage H K ≤ σ.ker) : Function.Injective σ := by
  have hres : pResidual 2 (H ⧸ pCore 2 H) ≤
      componentOrbit (actorImage H K) (quotientSylow H T hH.1.2) := by
    rw [quotient_componentOrbit H K T hKH hH.1.2,
      ←source_component_orbit_eq_residual hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK hgen, GenerationOne.residual, actorImage_internal,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  have hrad : solvableRadical (H ⧸ pCore 2 H) = ⊥ := by
    have hr := source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv H hH
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq hr)
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  exact faithful_of_detects_component_orbit σ (actorImage H K)
    (quotientSylow H T hH.1.2)
    (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
    hrad hres hdetect

/-- The non-FF marked component orbit excludes FF on every invariant
section containing its seed; its ambient action is proved faithful. -/
theorem source_l3_invariant_section_not_ff
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3))
    (hsmall : quadraticRatio (invariantSubspace a.representation (actorImage H K)
      (orbitSpan a.representation
        (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
      (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2)
    (W : Subrepresentation a.representation) (hIW : I ≤ W.toSubmodule) :
    Function.Injective W.toRepresentation ∧
      ¬ IsFFModule (imageRepresentation W.toRepresentation) := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  let : IsQuasisimple (actorImage H K) := hD.2
  let j : actorImage H K ≃* BinaryLinearThree.Group := b.groupEquiv
  have hz : center (actorImage H K) = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center BinaryLinearThree.Group at hh
    rw [show center BinaryLinearThree.Group = ⊥ from Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  let P := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  have hP : IsPGroup 2 P := (quotientSylow H T hH.1.2).isPGroup'.of_injective
    (inclusion (show P ≤ (quotientSylow H T hH.1.2 : Subgroup (H ⧸ pCore 2 H)) from inf_le_left))
    (inclusion_injective _)
  have hres : pResidual 2 (H ⧸ pCore 2 H) ≤
      componentOrbit (actorImage H K) (quotientSylow H T hH.1.2) := by
    rw [quotient_componentOrbit H K T hKH hH.1.2,
      ←source_component_orbit_eq_residual hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK hgen, GenerationOne.residual, actorImage_internal,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  have hf : Function.Injective W.toRepresentation :=
    source_faithful_of_component_detected hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hgen W.toRepresentation (by
        intro hk
        apply hI.isIrrPlus.not_le_fixedSpace a.representation
        intro v hv k
        have he := LinearMap.congr_fun (hk k.property) (⟨v,hIW hv⟩ : W)
        exact congrArg Subtype.val he)
  refine ⟨hf,not_ff_image_of_faithful W.toRepresentation hf ?_⟩
  apply not_ff_of_sylow_best_centralizes_orbit W.toRepresentation
    (quotientSylow H T hH.1.2) (actorImage H K) (pCore_quotient_pCore_eq_bot 2) hres
  intro A hAT hA
  exact hA.centralizes_of_nonFF_orbit_subrepresentation a.representation W hz hP hI hIW
    (le_inf hAT (ChapterB.source_lemma_B_1_5_4 W.toRepresentation hf hA hD))
    (source_l3_seed_orbit_not_ff hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK a hI b hsmall)

/-- On the full H-orbit of the marked seed, the two FF alternatives involving
the orbit itself are impossible. The only remaining obstruction to exhausting
the full residual support is a strong offender on its literal quotient. -/
theorem source_l3_full_orbit_exhaustion_or_strong_quotient
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    [hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3))
    (hsmall : quadraticRatio (invariantSubspace a.representation (actorImage H K)
      (orbitSpan a.representation
        (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
      (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    Function.Injective (seedOrbit a.representation I).toRepresentation ∧
    ¬ IsFFModule (imageRepresentation (seedOrbit a.representation I).toRepresentation) ∧
    (orbitSpan a.representation ⊤ I = subspaceCommutator a.representation ⊤
        (actorImage H (conjugateSpanBy K (T : Subgroup G))) ∨
      (Function.Injective (seedOrbit a.representation I).quotientRepresentation ∧
        IsStrongFFModule (imageRepresentation (seedOrbit a.representation I).quotientRepresentation))) := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  let W := seedOrbit a.representation I
  have hIW : I ≤ W.toSubmodule := le_orbitSpan a.representation ⊤ I
  obtain ⟨hf,hn⟩ := source_l3_invariant_section_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hgen a hI b hsmall W hIW
  have hr := source_component_orbit_eq_residual
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hgen
  have ho := quotient_componentOrbit H K T hKH hH.1.2
  have hnorm := source_quotient_componentOrbit_normal
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let R := actorImage H (residual H)
  have hR : R.Normal := by rw [show R = _ from congrArg (actorImage H) hr,←ho]; exact hnorm
  let := hR
  have hKR : actorImage H K ≤ R := by
    rw [show R = _ from congrArg (actorImage H) hr]
    exact map_mono (subgroupOf_mono H (le_conjugateSpanBy K (T : Subgroup G)))
  have hW : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤
      subspaceStabilizer a.representation W.toSubmodule := orbitSpan_invariant a.representation ⊤ I
  have hc : subspaceCommutator a.representation W.toSubmodule R = W.toSubmodule := by
    apply le_antisymm (subspaceCommutator_le_of_invariant a.representation (le_top.trans hW))
    apply orbitSpan_le a.representation
    · rw [←hI.isIrrPlus.choose_spec.1]
      apply Submodule.span_mono
      rintro v ⟨k,hk,x,hx,rfl⟩
      exact ⟨k,hKR hk,x,hIW hx,rfl⟩
    · exact subspaceCommutator_invariant_normalizer a.representation hW (by rw [normalizer_eq_top])
  obtain ⟨B,hB,hBA,hq,hbound,_⟩ := source_rankTwo_placed_quadratic_actor
    hG T hempty hM hunique hmany hcard e hab H hH hU a
  have hratio : actionRatio a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
    rw [actionRatio,ENNReal.div_le_iff (by exact_mod_cast (ne_of_gt hBA.rank_pos)) (by simp)]
    exact_mod_cast hbound
  have hgenq : conjugateSpanBy (actorImage H K) (actorImage H T) = R := by
    rw [show R = _ from congrArg (actorImage H) hr]
    rw [componentOrbit,←conjugateSpanBy_eq_iSup_conj] at ho
    exact ho
  have halt := source_section_alternatives a W K T hH.1.2 B hB
    (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
    hgenq ⟨hBA,hq,hratio⟩ (orbitSpan_ne_bot a.representation hI.isIrrPlus) hc
  refine ⟨hf,hn,?_⟩
  by_cases he : W.toSubmodule = subspaceCommutator a.representation ⊤ R
  · exact Or.inl (he.trans (congrArg (subspaceCommutator a.representation ⊤) (congrArg (actorImage H) hr)))
  have hdetect : ¬ actorImage H K ≤ W.quotientRepresentation.ker := by
    intro hk
    have hker : R ≤ W.quotientRepresentation.ker := by
      rw [←hgenq]
      exact conjugateSpanBy_le hk (by rw [normalizer_eq_top]; exact le_top)
    apply RepresentationReduction.SourceRestrictions.quotient_action_nontrivial
      a.representation W R hc he
    intro r hr v
    exact LinearMap.congr_fun (hker hr) v
  have hfQ := source_faithful_of_component_detected hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hgen W.quotientRepresentation hdetect
  rcases halt with heq | ⟨hff,_⟩ | ⟨A,hA,hs⟩ | hs
  · exact (he heq).elim
  · exact (hn hff).elim
  · exact (hn ⟨A,hA,hs.le⟩).elim
  · exact Or.inr ⟨hfQ,hs⟩

/-- The unchanged terminal exchanged-component hypotheses supply the seed,
its marking and the small quadratic action. Thus the full original orbit
has faithful non-FF action and only the strong-quotient exhaustion alternative. -/
theorem terminal_nonnormal_full_orbit_exhaustion_or_strong_quotient
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
      Function.Injective (seedOrbit a.representation I).toRepresentation ∧
      ¬ IsFFModule (imageRepresentation (seedOrbit a.representation I).toRepresentation) ∧
      (orbitSpan a.representation ⊤ I = subspaceCommutator a.representation ⊤
          (actorImage Mc (conjugateSpanBy K (T : Subgroup G))) ∨
        (Function.Injective (seedOrbit a.representation I).quotientRepresentation ∧
          IsStrongFFModule (imageRepresentation (seedOrbit a.representation I).quotientRepresentation))) := by
  obtain ⟨hU,a,I,hI,⟨b⟩,_,hsmall,_⟩ := terminal_nonnormal_full_component_action
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  exact ⟨hU,a,I,hI,⟨b⟩,source_l3_full_orbit_exhaustion_or_strong_quotient
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK
    (terminal_nonnormal_generated hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn)
    a hI b hsmall⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
