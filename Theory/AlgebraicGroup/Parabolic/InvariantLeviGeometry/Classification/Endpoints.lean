module

public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.RootTransport
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry

/-!
# Endpoints of the actual standard parabolic family

The simple-root span is the entire root system, via the integral root
expansion in the supplied datum. The empty span has no roots. Marked rank-one
matrix identities put all selected normalizer lifts in the torus/root-generated
group; actual B–N–B coverage then proves that this group is the ambient group.
These facts establish the two endpoints and the positive-root complement for
proper standard parabolics, without an extra ambient-generation hypothesis.

Source: GLS3, Theorem 1.13.2(a,c), and the use of proper parabolics in 2.6.5.
Classification and rigidity are separate from these endpoint results.
-/

@[expose] public noncomputable section

namespace Theory.AlgebraicGroup.InvariantLeviGeometry.Classification

open scoped BigOperators
open BorelIntersectionGeometry.RankOneGeometry

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)

/-- The literal closed root-generated parabolic attached to any root subset. -/
def rootParabolic (J : Set S.D.Root) : ClosedSubgroup K :=
  parabolic S.D S.standardParabolic.1.2.1 S.standardParabolic.1.1.1
    S.positiveRoots (RootSubsystemSpan S.D J)

/-- Its literal closed Levi candidate. -/
def rootLevi (J : Set S.D.Root) : ClosedSubgroup K :=
  levi S.D S.standardParabolic.1.2.1 S.standardParabolic.1.1.1
    (RootSubsystemSpan S.D J)

/-- Bruhat coverage at the specified Borel and torus. -/
def BruhatCoverage : Prop :=
  ∀ g : Variety.Point K, ∃ b n c : Variety.Point K,
    b ∈ S.B.toSubgroup ∧ n ∈ S.T.normalizer.toSubgroup ∧
      c ∈ S.B.toSubgroup ∧ g = b * n * c

omit [IsAlgClosed k] in
/-- The root-subsystem construction is monotone in its generating roots. -/
theorem subsystem_mono {J J' : Set S.D.Root} (h : J ⊆ J') :
    RootSubsystemSpan S.D J ⊆ RootSubsystemSpan S.D J' :=
  fun _ ha => Subgroup.closure_mono (Set.image_mono h) ha

/-- Monotonicity for the actual closed standard parabolics. -/
theorem rootParabolic_mono {J J' : Set S.D.Root} (h : J ⊆ J') :
    rootParabolic S J ≤ rootParabolic S J' := by
  change S.T.toSubgroup ⊔ standardParabolicRootFactor S.D S.positiveRoots
      (RootSubsystemSpan S.D J) ≤
    S.T.toSubgroup ⊔ standardParabolicRootFactor S.D S.positiveRoots
      (RootSubsystemSpan S.D J')
  apply sup_le_sup_left
  apply RootSubgroupGenerated_mono
  exact Set.union_subset_union
    (Set.union_subset_union_right _ (subsystem_mono S h))
    (Set.image_mono (subsystem_mono S h))

/-- Every member of the family contains the supplied positive Borel. -/
theorem rootParabolic_isParabolic
    (hB : IsBorelOfPositiveSystem S.D S.positiveRoots S.B)
    (J : Set S.D.Root) :
    IsParabolicSubgroup (rootParabolic S J) ∧ S.B ≤ rootParabolic S J :=
  parabolic_of_positiveBorel S.D S.standardParabolic.1.2.1
    S.standardParabolic.1.1.1 _ _ hB

omit [IsAlgClosed k] in
/-- Nonzero integral root vectors exclude roots from the empty subsystem. -/
theorem subsystem_empty : RootSubsystemSpan S.D ∅ = ∅ := by
  ext a
  simp only [RootSubsystemSpan, Set.image_empty, Subgroup.closure_empty,
    Set.mem_ofPred_eq, Subgroup.mem_bot, Set.mem_empty_iff_false, iff_false]
  intro ha
  have hz : S.integralPairing.root (S.rootEquiv a) = 0 := by
    apply Multiplicative.ofAdd.injective
    apply S.weightEquiv.injective
    rw [S.actualRootDatum.2.1 a]
    simpa using ha
  exact S.integralPairing.ne_zero _ hz

omit [IsAlgClosed k] in
/-- Integral expansion in the supplied simple roots includes every actual root. -/
theorem subsystem_simple : RootSubsystemSpan S.D S.D.simple = Set.univ := by
  classical
  let := Fintype.ofFinite S.ι
  apply Set.eq_univ_of_forall
  intro a
  change S.D.rootWeight a ∈ Subgroup.closure (S.D.rootWeight '' S.D.simple)
  rw [← S.actualRootDatum.2.1 a, (S.integralSimpleRootExpansion (S.rootEquiv a)).1]
  have hsum : ∀ (t : Finset S.ι),
      (∀ j ∈ t, j ∈ S.integralBase.support) →
      S.weightEquiv (Multiplicative.ofAdd
        (∑ j ∈ t, S.coeff (S.rootEquiv a) j • S.integralPairing.root j)) ∈
          Subgroup.closure (S.D.rootWeight '' S.D.simple) := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
      rw [Finset.sum_insert hj, ofAdd_add, map_mul]
      apply Subgroup.mul_mem
      · rw [ofAdd_zsmul, map_zpow]
        apply Subgroup.zpow_mem
        have hs : S.rootEquiv.symm j ∈ S.D.simple :=
          (S.actualRootDatum.1.2.2.2 _).mpr (by simpa using ht j (by simp))
        have hw : S.weightEquiv (Multiplicative.ofAdd (S.integralPairing.root j)) =
            S.D.rootWeight (S.rootEquiv.symm j) := by
          simpa using S.actualRootDatum.2.1 (S.rootEquiv.symm j)
        rw [hw]
        exact Subgroup.subset_closure ⟨_, hs, rfl⟩
      · exact ih (fun i hi => ht i (Finset.mem_insert_of_mem hi))
  exact hsum _ (fun _ hj => hj)

/-- The empty member is exactly the positive Borel. -/
theorem rootParabolic_empty
    (hB : IsBorelOfPositiveSystem S.D S.positiveRoots S.B) :
    rootParabolic S ∅ = S.B := by
  apply SetLike.coe_injective
  change ((rootParabolic S ∅).toSubgroup : Set (Variety.Point K)) =
    (S.B.toSubgroup : Set (Variety.Point K))
  congr 1
  simp only [rootParabolic, parabolic_toSubgroup, subsystem_empty,
    Set.image_empty, Set.union_empty, standardParabolicRootFactor]
  rw [hB.torus_unipotent_generate, hB.root_generated]

omit [IsAlgClosed k] in
private theorem reflection_mem_rootGenerated
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {a : D.Root} (M : SL2RootMarking D a) :
    M.hom BruhatGeneration.SL2.reflection ∈
      T.toSubgroup ⊔ RootSubgroupGenerated D Set.univ := by
  let H := T.toSubgroup ⊔ RootSubgroupGenerated D Set.univ
  have hu (t : k) : M.hom (BruhatGeneration.SL2.upper t) ∈ H := by
    apply (show RootSubgroupGenerated D Set.univ ≤ H from le_sup_right)
    apply rootSubgroup_le_RootSubgroupGenerated D (Set.mem_univ a)
    change M.hom (BruhatGeneration.SL2.upper t) ∈ (D.rootSubgroup a : Set (Variety.Point K))
    rw [← M.upper_range]
    exact ⟨t, rfl⟩
  have hl (t : k) : M.hom (BruhatGeneration.SL2.lower t) ∈ H := by
    apply (show RootSubgroupGenerated D Set.univ ≤ H from le_sup_right)
    apply rootSubgroup_le_RootSubgroupGenerated D (Set.mem_univ (D.neg a))
    change M.hom (BruhatGeneration.SL2.lower t) ∈ (D.rootSubgroup (D.neg a) : Set (Variety.Point K))
    rw [← M.lower_range]
    exact ⟨t, rfl⟩
  have heq := congrArg M.hom (BruhatGeneration.SL2.reflection_upper (k := k) one_ne_zero)
  simp only [map_mul, inv_one] at heq
  have hm : M.hom BruhatGeneration.SL2.reflection *
      M.hom (BruhatGeneration.SL2.upper 1) ∈ H := by
    rw [heq]
    exact H.mul_mem (H.mul_mem (hu _) ((show T.toSubgroup ≤ H from le_sup_left) (M.diagonal_mem _ _))) (hl _)
  have h := H.mul_mem hm (H.inv_mem (hu 1))
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using h

omit [IsAlgClosed k] in
/-- Actual Bruhat coverage and the marked rank-one reflections imply ambient
root generation. The normalizer action and markings use the supplied datum. -/
theorem torus_roots_generate
    (hB : IsBorelOfPositiveSystem S.D S.positiveRoots S.B)
    (M : SimpleRootMarkings S.D S.positiveRoots)
    (W : NormalizerRootAction S.D S.positiveRoots)
    (hcover : BruhatCoverage S) :
    S.T.toSubgroup ⊔ RootSubgroupGenerated S.D Set.univ = ⊤ := by
  let H := S.T.toSubgroup ⊔ RootSubgroupGenerated S.D Set.univ
  have hBH : S.B.toSubgroup ≤ H := by
    rw [hB.torus_unipotent_generate, hB.root_generated]
    exact sup_le_sup_left (RootSubgroupGenerated_mono S.D (Set.subset_univ _)) _
  have hNH : S.T.normalizer.toSubgroup ≤ H := by
    rw [← normalizer_generated M W S.standardParabolic.1.2.1]
    apply (Subgroup.closure_le _).mpr
    rintro x (hx | ⟨i, rfl⟩)
    · exact (show S.T.toSubgroup ≤ H from le_sup_left) hx
    · exact reflection_mem_rootGenerated (M.marking i)
  apply top_unique
  intro x _
  obtain ⟨b, n, c, hb, hn, hc, rfl⟩ := hcover x
  exact H.mul_mem (H.mul_mem (hBH hb) (hNH hn)) (hBH hc)

/-- The full standard parabolic is the whole ambient group, with generation
discharged from the allowed earlier Bruhat and rank-one inputs. -/
theorem rootParabolic_simple
    (hB : IsBorelOfPositiveSystem S.D S.positiveRoots S.B)
    (M : SimpleRootMarkings S.D S.positiveRoots)
    (W : NormalizerRootAction S.D S.positiveRoots)
    (hcover : BruhatCoverage S) :
    rootParabolic S S.D.simple = ClosedSubgroup.top := by
  apply SetLike.coe_injective
  change ((rootParabolic S S.D.simple).toSubgroup : Set (Variety.Point K)) =
    (⊤ : Subgroup (Variety.Point K))
  congr 1
  simp only [rootParabolic, parabolic_toSubgroup, subsystem_simple,
    Set.union_univ, Set.univ_union, standardParabolicRootFactor]
  exact torus_roots_generate S hB M W hcover

/-- A proper literal standard parabolic leaves a positive root outside its
Levi subsystem. This application uses the full endpoint, not an extra ambient
generation premise. -/
theorem positiveOutside_nonempty_of_rootParabolic_proper
    (hB : IsBorelOfPositiveSystem S.D S.positiveRoots S.B)
    (M : SimpleRootMarkings S.D S.positiveRoots)
    (W : NormalizerRootAction S.D S.positiveRoots)
    (hcover : BruhatCoverage S)
    (hproper : rootParabolic S S.J ≠ ClosedSubgroup.top) :
    (S.positiveRoots \ S.sigmaJ).Nonempty := by
  apply positiveOutside_nonempty_of_simple_ssubset S
  refine ⟨S.standardParabolic.2.1, ?_⟩
  intro h
  have hJ : S.J = S.D.simple := Set.Subset.antisymm S.standardParabolic.2.1 h
  apply hproper
  rw [hJ]
  exact rootParabolic_simple S hB M W hcover

end Theory.AlgebraicGroup.InvariantLeviGeometry.Classification

end
