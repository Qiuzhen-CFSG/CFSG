module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Movement

/-!
# The positive-kernel binary-three half-Sylow normalizer

Let R = N_T(L) and Z = Ω₁Z(R). The proved binary-three omega movement
calculation and central-cover splitting show that L centralizes Z. Since
T normalizes R, the entire original orbit L₀ centralizes Z. The nontrivial
fixed kernel of [V,L] lies in Z, so Z is a nontrivial two-group normalized
by L₀T. The original uniqueness theorem for L₀T therefore gives
N_G(R) ≤ N_G(Z) ≤ M.

This proves the positive-kernel branch of 10.2.5 without point-centralizer
control or half-Sylow uniqueness. Reselecting via ModuleChoiceAt leaves only
the zero-kernel binary-three branch. The final application supplies the
normalizer to the literal containing-pair construction and half-join
uniqueness consumer. That zero-kernel branch, containing-pair exclusion and
final assembly remain with qt-d-10-nona5-half-sylow-unique. The independent
ModuleChoiceAt producer is qt-d-10-nona5-point-selection; its final discharge
remains with qt-d-10-nona5-point-control.

Source: Aschbacher--Smith, 10.2.5 and the independent omega calculation in
10.2.8, printed pp.747--750, using 1.2.7, printed p.506.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual central omega of N_T(L) controls its full ambient normalizer
when the selected binary-three moved cover has nontrivial fixed kernel. -/
theorem stabilizer_normalizer_of_binary_three_positive_kernel (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let Z := omegaCenterIn R
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hi : (R.subgroupOf (T : Subgroup G)).index = 2 := by
    have he : R.subgroupOf (T : Subgroup G) =
        (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp (normal_of_index_eq_two hi)
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    hTR.trans (normalizer_le_normalizer_omegaCenterIn R)
  have hLZ : L ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mp
    apply Selection.BinaryThree.interval_omega_centralizes_component D hmodel hne hfull hn
      (Selection.BinaryThree.core_omega_component_movement_le_of_orbit_movement_le D
        (Selection.BinaryThree.core_omega_orbit_movement_le D hmodel hne hfull hJ ht htn hcross))
      R (join_core_le_stabilizer D) inf_le_left
    exact le_inf inf_le_left (inf_le_right.trans L.le_normalizer)
  have hXZ : localOrbit T L ≤ centralizer (Z : Set G) :=
    iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) _ hLZ
      (hTZ.trans (normalizer_le_normalizer_centralizer _))
  have hKZ : sourceMovedFixed D ≤ Z := by
    have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    have hKR : sourceMovedFixed D ≤ R :=
      (inf_le_left.trans hWV).trans ((show D.fullModule ≤ (localJoin T L).pCoreIn 2 by
        rw [hfull]
        exact D.module_le_core).trans (join_core_le_stabilizer D))
    have hRC : R ≤ centralizer (sourceMovedFixed D : Set G) :=
      (Selection.BinaryThree.half_sylow_centralizes_moved_kernels D hmodel ht htn).trans
        (centralizer_le (show sourceMovedFixed D ≤ sourceMovedFixed D ⊔
          (sourceMovedFixed D).map (MulAut.conj t).toMonoidHom from le_sup_left))
    let := source_original_full_moved_elementary D
    intro z hz
    exact (mem_omegaCenterIn_iff R z).mpr ⟨hKR hz,
      le_centralizer_iff.mp hRC hz,elemPow_eq_one_of_isElementaryAbelian z hz.1⟩
  have hZne : Z ≠ ⊥ := fun h => hne (bot_unique (hKZ.trans_eq h))
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact (normalizer_le_normalizer_omegaCenterIn R).trans
    (normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
      (IsElementaryAbelian.isPGroup 2 Z) hZne
      (sup_le (hXZ.trans (Subgroup.centralizer_le_normalizer _)) hTZ))


/-- Module choice now leaves only the zero-kernel binary-three normalizer.
The source exchanger and its crossed centralization remain available there. -/
theorem stabilizerNormalizerAt_of_moduleChoice_and_zero_kernel
    (hchoice : Selection.ModuleChoiceAt T)
    (hzero : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
      ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      Selection.BinaryThreeNatural D → sourceMovedFixed D = ⊥ →
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
      ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
      normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal) :
    StabilizerNormalizerAt T := by
  intro hmany L D hn hna
  obtain ⟨E,hE,t,ht,htn,hcross,hcases⟩ :=
    hchoice hmany L D.maximal D.faithful D.quasisimple hn hna
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (E.fullModule : Set G)
  · exact stabilizer_normalizer_of_thompson_centralizes E hJ
  obtain ⟨heq,hm⟩ := hcases.resolve_left hJ
  rcases hm with hr | h3
  · exact stabilizer_normalizer_of_rankOneNatural E hn hr
  by_cases hz : sourceMovedFixed E = ⊥
  · exact hzero L E hmany hE heq hn hna h3 hz hJ t ht htn hcross
  · exact stabilizer_normalizer_of_binary_three_positive_kernel E h3 hz heq hJ ht htn hcross

/-- Apply the proved positive-kernel normalizer to the actual containing pair.
Only the separate containing-pair contradiction is retained by this consumer. -/
theorem halfSylowUnique_of_binary_three_positive_kernel_and_pairExclusion
    (hpair : ContainingPairExclusionAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : Selection.BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    HalfSylowUnique D := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  intro H hH hhalf
  by_contra hneq
  obtain ⟨s,K₁,K₂,C⟩ := exists_containingPair D
    (stabilizer_normalizer_of_binary_three_positive_kernel D hmodel hne hfull hJ ht htn hcross) hn hH hneq hhalf
  exact hpair hmany L D hn hna H s K₁ K₂ C

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
