module

public import Theory.AlgebraicGroup.BNPair.Representatives
public import Theory.AlgebraicGroup.RootData.Standard
public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup
public import Theory.AlgebraicGroup.RootSystems.Weyl

/-!
Rank-one witnesses for the nontriviality clause in the standard algebraic-group
`BN`-pair.  The elementary core uses the square relation `n^2 ∈ B`: equality
of the singleton double coset with `B` would then make conjugation by `n`
preserve `B`, contradicting a root subgroup sent from a positive root to its
opposite.  The representative-set theorem transports this witness through
the quotient class without assuming a `TitsSystem`.  The standard-root-datum
wrapper supplies the positive root subgroup from the Borel generation equality
and leaves the rank-one opposite-root action and square relation explicit;
these are the genuine geometric inputs supplied by a normalizer/root-group
package.  Quotient normality is explicit at the representative-set boundary,
where it is needed to form the quotient.  This is the nontriviality argument
in GLS3 Theorem 1.11.3
(`refs/KGroup/GLS3/Chapter1.tex:483-485`).
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise
open TitsSystem

universe u₁

variable {X : Type*} [Group X]

private lemma not_mem_normalizer_of_root_conj
    (B : Subgroup X) (n : X)
    (R Rneg : Subgroup X)
    (hR : R ≤ B)
    (hRneg : ¬ Rneg ≤ B)
    (hconj : ∀ y, y ∈ Rneg → ∃ x, x ∈ R ∧ n * x * n⁻¹ = y) :
    n ∉ Subgroup.normalizer (B : Set X) := by
  intro hn
  apply hRneg
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hconj y hy
  have hnx : n * x * n⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp hn x).mp (hR hx)
  simpa [hxy] using hnx

/-- A rank-one square relation and a failure to normalize `B` force a
nontrivial singleton double coset. -/
public lemma singleton_doubleCoset_ne_of_sq_mem_of_not_mem_normalizer
    (B : Subgroup X) (n : X)
    (hnsq : n * n ∈ B)
    (hnorm : n ∉ Subgroup.normalizer (B : Set X)) :
    ({n} : Set X) * (B : Set X) * ({n} : Set X) ≠ (B : Set X) := by
  intro hEq
  apply hnorm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hnxn : n * x * n ∈ B := by
      change n * x * n ∈ (B : Set X)
      rw [← hEq]
      simp only [Set.mem_mul]
      refine ⟨n * x, ?_, n, Set.mem_singleton _, rfl⟩
      exact Set.mem_mul.mpr ⟨n, Set.mem_singleton _, x, hx, rfl⟩
    have hsqinv : (n * n)⁻¹ ∈ B := B.inv_mem hnsq
    have hninv : n⁻¹ = n * (n * n)⁻¹ := by
      simp
    rw [hninv]
    simpa [mul_assoc] using B.mul_mem hnxn hsqinv
  · intro hx
    have hnxn : n * x * n ∈ B := by
      rw [show n * x * n = (n * x * n⁻¹) * (n * n) by simp [mul_assoc]]
      simpa [mul_assoc] using B.mul_mem hx hnsq
    have hn2xn2 : n * (n * x * n) * n ∈ B := by
      change n * (n * x * n) * n ∈ (B : Set X)
      rw [← hEq]
      simp only [Set.mem_mul]
      refine ⟨n * (n * x * n), ?_, n, Set.mem_singleton _, rfl⟩
      exact Set.mem_mul.mpr ⟨n, Set.mem_singleton _, n * x * n, hnxn, rfl⟩
    have hsqinv : (n * n)⁻¹ ∈ B := B.inv_mem hnsq
    have hmem : x ∈ B := by
      rw [show x = (n * n)⁻¹ * (n * (n * x * n) * n) * (n * n)⁻¹ by
        simp [mul_assoc]]
      exact B.mul_mem (B.mul_mem hsqinv hn2xn2) hsqinv
    exact hmem

/-- The singleton rank-one witness transported to the all-representatives
quotient notation used by `TitsSystem`. -/
public lemma representativeSet_doubleCoset_ne_of_sq_mem_of_not_mem_normalizer
    (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (s : N ⧸ (B ⊓ N).subgroupOf N) (n : N)
    (hns : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n = s)
    (hnsq : (n : X) * (n : X) ∈ B)
    (hnorm : (n : X) ∉ Subgroup.normalizer (B : Set X)) :
    representativeSet B N s * (B : Set X) * representativeSet B N s ≠
      (B : Set X) := by
  rw [mul_assoc, B_mul_representativeSet B N s n hns, ← mul_assoc,
    representativeSet_mul_B B N s n hns]
  exact singleton_doubleCoset_ne_of_sq_mem_of_not_mem_normalizer B (n : X)
    hnsq hnorm

/-- A positive-root subgroup sent onto the opposite root subgroup gives the
rank-one representative witness in quotient representative-set form. -/
public lemma representativeSet_doubleCoset_ne_of_sq_mem_of_root_conj
    (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (s : N ⧸ (B ⊓ N).subgroupOf N) (n : N)
    (hns : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n = s)
    (hnsq : (n : X) * (n : X) ∈ B)
    (R Rneg : Subgroup X)
    (hR : R ≤ B)
    (hRneg : ¬ Rneg ≤ B)
    (hconj : ∀ y, y ∈ Rneg → ∃ x, x ∈ R ∧ (n : X) * x * (n : X)⁻¹ = y) :
    representativeSet B N s * (B : Set X) * representativeSet B N s ≠
      (B : Set X) := by
  apply representativeSet_doubleCoset_ne_of_sq_mem_of_not_mem_normalizer
    B N s n hns hnsq
  exact not_mem_normalizer_of_root_conj B (n : X) R Rneg hR hRneg hconj

/-- Standard Borel/root-datum form of the rank-one witness.  The explicit
`hneg` and `hconj` hypotheses are the rank-one geometric input: the opposite
root subgroup is not contained in the standard Borel, and the chosen
normalizer representative maps the positive root subgroup onto it. -/
public theorem standard_simple_reflection_doubleCoset_ne_B_of_root_conj
    {k : Type u₁} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsReductiveAlgebraicGroup K)
    (T B : ClosedSubgroup K)
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    (_hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hBroot : B.toSubgroup =
      RootSubgroupGenerated D positiveRoots ⊔ T.toSubgroup)
    {ι X Y : Type u₁} [Finite ι]
    [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (_hInf : B.toSubgroup ⊓
      Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) = T.toSubgroup)
    [hNormal : ((B.toSubgroup ⊓
      Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))).subgroupOf
        (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))).Normal]
    (i : base.support)
    (s : Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) ⧸
      (B.toSubgroup ⊓ Subgroup.normalizer
        (T.toSubgroup : Set (Variety.Point K))).subgroupOf
          (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))))
    (n : Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))
    (hns : QuotientGroup.mk'
      ((B.toSubgroup ⊓ Subgroup.normalizer
        (T.toSubgroup : Set (Variety.Point K))).subgroupOf
          (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))) n = s)
    (_weylEquiv :
      (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) ⧸
        (B.toSubgroup ⊓ Subgroup.normalizer
          (T.toSubgroup : Set (Variety.Point K))).subgroupOf
            (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))) ≃*
        P.weylGroup)
    (_hrep : _weylEquiv s = base.simpleReflection i)
    (hnsq : (n : Variety.Point K) * (n : Variety.Point K) ∈ B.toSubgroup)
    (hneg : ¬ (D.rootSubgroup (D.neg (e.symm i))).toSubgroup ≤ B.toSubgroup)
    (hconj : ∀ y, y ∈ (D.rootSubgroup (D.neg (e.symm i))).toSubgroup →
      ∃ x, x ∈ (D.rootSubgroup (e.symm i)).toSubgroup ∧
        (n : Variety.Point K) * x * (n : Variety.Point K)⁻¹ = y) :
    representativeSet B.toSubgroup
        (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))) s *
        (B.toSubgroup : Set (Variety.Point K)) *
        representativeSet B.toSubgroup
          (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))) s ≠
      (B.toSubgroup : Set (Variety.Point K)) := by
  have hαpos : e.symm i ∈ positiveRoots := by
    apply (hActual.2.2 _).mpr
    simpa only [Equiv.apply_symm_apply] using base.isPos_of_mem_support i.property
  let N := Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))
  have hR : (D.rootSubgroup (e.symm i)).toSubgroup ≤ B.toSubgroup := by
    rw [hBroot]
    exact (rootSubgroup_le_RootSubgroupGenerated D hαpos).trans le_sup_left
  exact representativeSet_doubleCoset_ne_of_sq_mem_of_root_conj
    B.toSubgroup N s n hns hnsq
    (D.rootSubgroup (e.symm i)).toSubgroup
    (D.rootSubgroup (D.neg (e.symm i))).toSubgroup hR hneg hconj

end Theory.AlgebraicGroup
