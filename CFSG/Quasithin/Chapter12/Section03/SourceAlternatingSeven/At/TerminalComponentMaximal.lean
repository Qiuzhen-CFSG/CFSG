module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentMaximal
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentPreparation

/-!
# TerminalComponentMaximal at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentMaximal`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

private theorem natural_faithful_at : Function.Injective
    (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) := by
  intro g h he
  apply Subtype.ext
  apply BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).surjective v
  rw [← BinaryPermutation.coreEquivNatural_equivariant,
    ← BinaryPermutation.coreEquivNatural_equivariant]
  exact congrArg (BinaryPermutation.coreEquivNatural (Fin 5) (by decide))
    (LinearMap.congr_fun he w)

private theorem double_natural_faithful_at : Function.Injective
    (Representation.prod (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5))) := by
  intro g h he
  apply natural_faithful_at
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v,0))

omit [Finite G] in

private theorem section_elementary_at {A B : Subgroup G} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) B W}
    (s : Representation.BinaryConjugationSection B A ⊥ ρ) :
    IsElementaryAbelian 2 A := by
  have hi : Function.Injective s.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [s.kernel_eq, bot_subgroupOf]
  have hsquare := s.square_eq_one_of_trivial_kernel rfl
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsquare x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

omit [Finite G] in

private theorem section_not_centralized_at {A B : Subgroup G} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    (μ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (hμ : Function.Injective μ)
    (f : B →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (s : Representation.BinaryConjugationSection B A ⊥ (μ.comp f)) :
    ¬ B ≤ centralizer (A : Set G) := by
  intro hc
  obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  obtain ⟨b,rfl⟩ := hf a
  apply ha
  apply hμ
  apply LinearMap.ext
  intro w
  obtain ⟨v,hv⟩ := s.onto (Multiplicative.ofAdd w)
  have he := s.equivariant b v
  have hfix : (⟨(b:G) * (v:G) * (b:G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized b.property) v).mp v.property⟩ : A) = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hc b.property v v.property).symm
  rw [hfix, hv] at he
  change w = μ (f b) w at he
  simpa [map_one] using he.symm

theorem maximal_residual_thompson_at
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) :
    ⁅P.K, elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.K := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  have hq := IsQuasisimple.of_mulEquiv q.symm
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.hypothesis.simpleQTKE T hmax.1
  have horbit : componentOrbit P.K (T : Subgroup G) = P.K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      P.sylow_normalizes_residual) (le_componentOrbit _ _)
  have hm : IsMaximalTwoLocal (normalizer (P.K : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  apply Chapter3.Section02.source_component_thompson_generation
    S.hypothesis.simpleQTKE T P.K hmax.1 hmax.2 hq P.sylow_normalizes_residual
    (Chapter3.hasMaximalOutside_of_many T P.many_maximal_overgroups_at _ hm
      P.sylow_normalizes_residual)
  exact (centralizer_le (Set.singleton_subset_iff.mpr P.central)).trans
    (P.pointCentralizer_normalizes_of_maximal hmax.1)

theorem maximal_thompson_moves_moved_module_at
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (⁅P.Z,P.K⁆ : Subgroup G) := by
  intro hj
  apply P.residual_moves_moved_module q hsum
  conv_lhs => rw [← P.maximal_residual_thompson_at q hmax]
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · rw [commutator_eq_bot_iff_le_centralizer.mpr hj, commutator_bot_left]
  · exact commutator_eq_bot_iff_le_centralizer.mpr
      ((le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right P.Z P.K)).trans
        (le_centralizer_iff.mp hj))

theorem maximal_moved_isFF_at
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q) :
    let := P.maximal_moved_elementary q hsum
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation P.H ⁅P.Z,P.K⁆ P.moved_module_normalized) := by
  let := P.maximal_moved_elementary q hsum
  exact Chapter3.internalActionImage_isFFModule_of_thompson_not_le T P.H ⁅P.Z,P.K⁆
    P.minimal.1.1.2 (P.moved_module_le_sylow q hsum) P.moved_module_normalized
    (P.maximal_thompson_moves_moved_module_at q hmax hsum)

private theorem notFF_of_section_normalizer_at
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (μ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (s : Representation.BinaryConjugationSection P.K ⁅P.Z,P.K⁆ ⊥
      (μ.comp (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.K)))))
    [IsElementaryAbelian 2 (⁅P.Z,P.K⁆ : Subgroup G)]
    (hnon : ¬ Representation.BinaryOffender.IsFFModule
      (Representation.BinaryOffender.normalizerRepresentation μ)) :
    ¬ Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation P.H ⁅P.Z,P.K⁆ P.moved_module_normalized) := by
  let A := ⁅P.Z,P.K⁆
  let f := ChapterD.UniqueFactor.actionHom P.H A P.moved_module_normalized
  let π := f.rangeRestrict
  let i := (inclusion (map_subtype_le (pResidual 2 P.H)))
  have hn : (P.K.subgroupOf P.H).Normal := normal_subgroupOf_of_le_normalizer
    (P.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P.H (pResidual 2 P.H)))
  have hnrange : (π.comp i).range.Normal := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact Subgroup.Normal.map hn π (MonoidHom.rangeRestrict_surjective f)
  have hci : Function.Injective s.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [s.kernel_eq, bot_subgroupOf]
  let E : Additive A ≃ₗ[ZMod 2] W :=
    LinearEquiv.ofBijective (s.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hci,s.onto⟩
  let ρ := ChapterD.UniqueFactor.imageRepresentation P.H A P.moved_module_normalized
  let b : Representation.Equiv (ρ.comp (π.comp i))
      (μ.comp (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.K)))) := {
    __ := E
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      change Multiplicative.toAdd (s.coordinates
        ⟨(k : G) * (v.toMul : G) * (k : G)⁻¹, _⟩) =
        μ (q (QuotientGroup.mk' (pCore 2 P.K) k))
          (Multiplicative.toAdd (s.coordinates v.toMul))
      exact s.equivariant k v.toMul }
  exact @Representation.BinaryOffender.not_isFFModule_of_marked_normal_range
    _ _ _ _ _ _ _ _ _ _ _ _ ρ
    (ChapterD.UniqueFactor.imageRepresentation_injective _ _ _) (π.comp i) hnrange μ
    (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.K)))
    (q.surjective.comp (QuotientGroup.mk'_surjective _)) b hnon

theorem maximal_action_of_double_normalizer_nonFF_at
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule
      (Representation.BinaryOffender.normalizerRepresentation
        (Representation.prod (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
          (BinaryPermutation.alternatingCoreRepresentation (Fin 5))))) :
    P.ResidualActionConclusions q := by
  refine ⟨P.maximal_residual_thompson_at q hmax, ?_⟩
  have hff := P.maximal_moved_isFF_at q hmax hsum
  let := P.maximal_moved_elementary q hsum
  unfold AtMostTwoNatural at hsum
  rcases hsum with hnat | hs
  · exact hnat
  · exact (P.notFF_of_section_normalizer_at _ q (Classical.choice hs) hnon hff).elim

theorem maximal_action_at
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q) :
    P.ResidualActionConclusions q :=
  P.maximal_action_of_double_normalizer_nonFF_at q hmax hsum
    BinaryPermutation.FiveDoubleNonFF.double_normalizer_not_isFFModule

theorem componentAnalysis_of_residual_and_proper_at (R : P.ResidualAnalysis)
    (properStep : ∀ F : P.Overcomponents, P.K < F.Y →
      (∃ W : Subgroup G, Nonempty (Setup T F.Y W)) →
      F.E = P.K ∧ P.ResidualActionConclusions R.quotient) :
    Nonempty P.ComponentAnalysis :=
  P.componentAnalysis_of_source_branches R properStep (P.maximal_action_at R.quotient)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

