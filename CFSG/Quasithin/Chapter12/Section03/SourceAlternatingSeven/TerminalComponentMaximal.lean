module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentBranches
public import CFSG.Quasithin.Chapter3.Section02.SourceComponentThompson
public import CFSG.Quasithin.Chapter3.Section01.OffenderBranch
public import Theory.Representation.BinaryOffender.NormalizerNonFF
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutation.FiveDoubleNonFF
public import Theory.ElementaryAbelian.Injective

/-!
# The maximal-component branch of 12.3.12

Suppose the actual residual K is a faithful maximal local component and
12.2.7 identifies its quotient with A₅ and its entire moved subgroup [Z,K]
with one or two natural modules. The original escaping H supplies the
multiple-overgroup guard for Thompson generation. Consequently J(T) moves
[Z,K], so the faithful H-action on that elementary abelian subgroup is FF.
The full linear normalizer of the doubled module is non-FF; transporting
the marked K-action into it eliminates the doubled alternative.

The final application supplies this maximal branch to ComponentAnalysis
assembly. Residual recognition and the proper-overcomponent branch remain
with the terminal-component source proof.
Source: Aschbacher--Smith, 12.3.12, printed p.811, using 12.2.7(3), 3.2.8
and B.5.1.
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

private theorem natural_faithful : Function.Injective
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

private theorem double_natural_faithful : Function.Injective
    (Representation.prod (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5))) := by
  intro g h he
  apply natural_faithful
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v,0))

omit [Finite G] in
private theorem section_elementary {A B : Subgroup G} {W : Type*}
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
private theorem section_not_centralized {A B : Subgroup G} {W : Type*}
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

theorem maximal_moved_elementary
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hsum : P.AtMostTwoNatural q) : IsElementaryAbelian 2 (⁅P.Z,P.K⁆ : Subgroup G) := by
  unfold AtMostTwoNatural at hsum
  rcases hsum with hs | hs
  · exact section_elementary (Classical.choice hs)
  · exact section_elementary (Classical.choice hs)

theorem residual_moves_moved_module
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hsum : P.AtMostTwoNatural q) :
    ¬ P.K ≤ centralizer (⁅P.Z,P.K⁆ : Subgroup G) := by
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.K))
  have hf : Function.Surjective f := q.surjective.comp (QuotientGroup.mk'_surjective _)
  unfold AtMostTwoNatural at hsum
  rcases hsum with hs | hs
  · exact section_not_centralized _ natural_faithful f hf (Classical.choice hs)
  · exact section_not_centralized _ double_natural_faithful f hf (Classical.choice hs)

theorem moved_module_normalized : P.H ≤ normalizer (⁅P.Z,P.K⁆ : Subgroup G) := by
  rw [← P.residual_sup_sylow]
  refine sup_le (normalizer_commutator_ge_right _ _) ?_
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_omegaCenterIn _ ((T : Subgroup G).le_normalizer ht)),
    mem_normalizer_iff_map_conj_eq.mp (P.sylow_normalizes_residual ht)]

theorem moved_module_le_sylow
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hsum : P.AtMostTwoNatural q) : ⁅P.Z,P.K⁆ ≤ (T : Subgroup G) := by
  have hWH : ⁅P.Z,P.K⁆ ≤ P.H := by
    unfold AtMostTwoNatural at hsum
    rcases hsum with hs | hs
    · exact (Classical.choice hs).section_le.trans (map_subtype_le _)
    · exact (Classical.choice hs).section_le.trans (map_subtype_le _)
  let := P.maximal_moved_elementary q hsum
  let : ((⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H).Normal :=
    normal_subgroupOf_of_le_normalizer P.moved_module_normalized
  let := IsElementaryAbelian.subgroupOf (p := 2) hWH
  have ht := (IsElementaryAbelian.isPGroup 2 ((⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H)).le_sylow_of_normal
    (T.subtype P.minimal.1.1.2)
  intro w hw
  exact ht (show (⟨w,hWH hw⟩ : P.H) ∈ (⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H from hw)

theorem maximal_residual_thompson
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
    (Chapter3.hasMaximalOutside_of_many T P.many_maximal_overgroups _ hm
      P.sylow_normalizes_residual)
  exact (centralizer_le (Set.singleton_subset_iff.mpr P.central)).trans
    (P.pointCentralizer_normalizes_of_maximal hmax.1)

theorem maximal_thompson_moves_moved_module
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (⁅P.Z,P.K⁆ : Subgroup G) := by
  intro hj
  apply P.residual_moves_moved_module q hsum
  conv_lhs => rw [← P.maximal_residual_thompson q hmax]
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · rw [commutator_eq_bot_iff_le_centralizer.mpr hj, commutator_bot_left]
  · exact commutator_eq_bot_iff_le_centralizer.mpr
      ((le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right P.Z P.K)).trans
        (le_centralizer_iff.mp hj))

theorem maximal_moved_isFF
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q) :
    let := P.maximal_moved_elementary q hsum
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation P.H ⁅P.Z,P.K⁆ P.moved_module_normalized) := by
  let := P.maximal_moved_elementary q hsum
  exact Chapter3.internalActionImage_isFFModule_of_thompson_not_le T P.H ⁅P.Z,P.K⁆
    P.minimal.1.1.2 (P.moved_module_le_sylow q hsum) P.moved_module_normalized
    (P.maximal_thompson_moves_moved_module q hmax hsum)

private theorem notFF_of_section_normalizer
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

/-- The only remaining model input is non-FF of the full normalizer of the
two-copy action. All source and literal-action transport premises are discharged. -/
theorem maximal_action_of_double_normalizer_nonFF
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule
      (Representation.BinaryOffender.normalizerRepresentation
        (Representation.prod (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
          (BinaryPermutation.alternatingCoreRepresentation (Fin 5))))) :
    P.ResidualActionConclusions q := by
  refine ⟨P.maximal_residual_thompson q hmax, ?_⟩
  have hff := P.maximal_moved_isFF q hmax hsum
  let := P.maximal_moved_elementary q hsum
  unfold AtMostTwoNatural at hsum
  rcases hsum with hnat | hs
  · exact hnat
  · exact (P.notFF_of_section_normalizer _ q (Classical.choice hs) hnon hff).elim

/-- The source maximal branch, with the doubled-module calculation discharged. -/
theorem maximal_action
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5))
    (hmax : FaithfulMaximalLocal T P.K) (hsum : P.AtMostTwoNatural q) :
    P.ResidualActionConclusions q :=
  P.maximal_action_of_double_normalizer_nonFF q hmax hsum
    BinaryPermutation.FiveDoubleNonFF.double_normalizer_not_isFFModule

/-- Apply the proved maximal branch to the original component-analysis
consumer. The terminal-component owner must still construct the 12.2.7
residual analysis and discharge the proper branch. -/
theorem componentAnalysis_of_residual_and_proper (R : P.ResidualAnalysis)
    (properStep : ∀ F : P.Overcomponents, P.K < F.Y →
      (∃ W : Subgroup G, Nonempty (Setup T F.Y W)) →
      F.E = P.K ∧ P.ResidualActionConclusions R.quotient) :
    Nonempty P.ComponentAnalysis :=
  P.componentAnalysis_of_source_branches R properStep (P.maximal_action R.quotient)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
