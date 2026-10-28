module

public import Theory.AlgebraicGroup.RootData.RankTwoChevalleyParameterWord

universe u

/-!
Singular rank-two positive-chain isolation for Chevalley systems.

GLS3 Theorem 1.12.7(d) generates every positive root subgroup from the whole
fundamental base.  In singular characteristic this cannot be reduced to the
immediate pair in a positive-root chain.  For example, in type `C2` and
characteristic two, the `(1,1)` coefficient for the pair
`(e1 + e2, e1 - e2)` is either `2` or `-2`, so those two root groups commute
and do not generate the endpoint `2e1`.

The characteristic-free contract below therefore records the output of the
full rank-two collection as a word in fundamental roots or positive roots of
strictly smaller height.  This is exactly the support available to the
fundamental-root height induction: fundamental factors are generators and the
remaining factors have already been generated.  The containment theorems turn
that parameter certificate into either containment in the subgroup generated
by the allowed support or containment in any subgroup already containing its
root groups.  The constructor proved here extracts a base-independent
certificate from the actual Chevalley and root-system-realization hypotheses,
so the positive-chain base may differ from that presentation base.  Its finite
rank-two calculation handles all six reduced tables;
in characteristics two and three it uses preceding roots, complete correction
term collection, and coroot-torus rescaling over the algebraically closed base
field.

The stronger immediate-pair certificate remains separate.  It explicitly
requires nonvanishing of the valid `(1,1)` Chevalley coefficient, excluding the
singular `C2` obstruction (and its analogous exceptional-coefficient cases),
before concluding generation from the two immediate root groups.  No result in
this module uses the placeholder-bearing numbered theorem.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Roots that may occur in a characteristic-free positive-chain isolation
word: a fundamental root or a positive root strictly earlier in the base-height
induction.  The exposed body is the intended construction interface for the
finite rank-two collection certificate. -/
@[expose] public def RankTwoPositiveChainSupport
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (e : D.Root ≃ ι) (base : P.Base)
    (gamma : D.Root) : Set D.Root :=
  {rho | e rho ∈ base.support ∨
    (base.IsPos (e rho) ∧ base.height (e rho) < base.height (e gamma))}

/-- The root-theoretic part of one positive-chain extension across a
fundamental root. -/
public structure RankTwoPositiveChainStep
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (alpha delta gamma : D.Root) : Prop where
  delta_mem_base : e delta ∈ base.support
  alpha_positive : base.IsPos (e alpha)
  gamma_positive : base.IsPos (e gamma)
  gamma_eq_alpha_add_delta :
    P.root (e gamma) = P.root (e alpha) + P.root (e delta)

/-- A characteristic-free positive-chain extension.  Its parameter certificate
may use the entire fundamental base and positive roots already available at a
strictly smaller height; it does not claim that the immediate pair generates
the endpoint in singular characteristic. -/
public structure RankTwoPositiveChainExtension
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (alpha delta gamma : D.Root) : Prop extends
    RankTwoPositiveChainStep D P e base alpha delta gamma where
  parameter_isolation : ∀ t : k, ∃ word : List (D.Root × k),
    (∀ q ∈ word, q.1 ∈ RankTwoPositiveChainSupport D P e base gamma) ∧
      C.x gamma t = FilteredCollection.wordProduct C.x word

/-- An immediate-pair isolation certificate for a nonsingular chain step.
The coefficient premise is localized to the valid `(1,1,gamma)` term and is
stated for every expected coefficient so that it applies to the coefficient
selected by an `IsChevalleySystem` commutator formula. -/
public structure RankTwoImmediatePairExtension
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (alpha delta gamma : D.Root) : Prop extends
    RankTwoPositiveChainStep D P e base alpha delta gamma where
  one_one_valid : IsValidChevalleyCommutatorTerm D P e alpha delta
    {i := 1, j := 1, root := gamma}
  one_one_coefficient_ne_zero : ∀ c : k,
    HasExpectedChevalleyCoefficient D P e alpha delta
      {i := 1, j := 1, root := gamma} c → c ≠ 0
  commutator_isolation : ∀ t : k, ∃ a b : k, ∃ word : List (D.Root × k),
    (∀ q ∈ word, q.1 = alpha ∨ q.1 = delta) ∧
      (C.x alpha a)⁻¹ * (C.x delta b)⁻¹ * C.x alpha a * C.x delta b =
        C.x gamma t * FilteredCollection.wordProduct C.x word

/-- Realize a positive-chain extension from the actual Chevalley and root-data
hypotheses.  The finite rank-two parameter-word theorem supplies the complete
collection certificate, including the singular characteristic branches. -/
public theorem RankTwoPositiveChainStep.toExtension_of_certificate
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) [IsAlgClosed k]
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    (_hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hStep : RankTwoPositiveChainStep D P e base alpha delta gamma) :
    RankTwoPositiveChainExtension D C P e base alpha delta gamma := by
  refine { hStep with parameter_isolation := ?_ }
  intro t
  simpa only [RankTwoPositiveChainSupport, Set.mem_ofPred_eq] using
    rankTwoPositiveChain_parameter_word_of_certificate D C P e base hC hRoot
      hStep.delta_mem_base hStep.alpha_positive hStep.gamma_positive
      hStep.gamma_eq_alpha_add_delta t

public theorem RankTwoPositiveChainStep.toExtension
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) [IsAlgClosed k]
    (hC : IsChevalleySystem D C P e base)
    (hActual : IsRootSystemRealization D P e base)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hStep : RankTwoPositiveChainStep D P e base alpha delta gamma) :
    RankTwoPositiveChainExtension D C P e base alpha delta gamma := by
  exact RankTwoPositiveChainStep.toExtension_of_certificate D C P e base
    (RankTwoChevalleyParameterCertificate.of_system D C P e base hC)
    (RankTwoRootPairingCertificate.of_realization D P e base hActual) hAdd hStep

/-- The root-addition operation agrees with the positive-chain endpoint. -/
public theorem RankTwoPositiveChainExtension.add_eq
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hExt : RankTwoPositiveChainExtension D C P e base alpha delta gamma) :
    D.add alpha delta = some gamma :=
  hAdd.add_of_root_eq_add hExt.gamma_eq_alpha_add_delta

/-- A positive-chain parameter certificate puts the endpoint root subgroup in
the subgroup generated by its fundamental-or-earlier support. -/
public theorem rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainExtension_of_certificate
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {alpha delta gamma : D.Root}
    (hExt : RankTwoPositiveChainExtension D C P e base alpha delta gamma) :
    (D.rootSubgroup gamma).toSubgroup ≤
      RootSubgroupGenerated D (RankTwoPositiveChainSupport D P e base gamma) := by
  intro x hx
  have hxClosed : x ∈ (D.rootSubgroup gamma : Set (Variety.Point K)) := hx
  have hx' : x ∈ Set.range (C.x gamma) := by
    rw [← hC.rootCurve_range gamma] at hxClosed
    exact hxClosed
  obtain ⟨t, rfl⟩ := hx'
  obtain ⟨word, hword, hfactor⟩ := hExt.parameter_isolation t
  rw [hfactor]
  apply Subgroup.list_prod_mem
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  apply (rootSubgroup_le_RootSubgroupGenerated D (hword q hq))
  have hxq : C.x q.1 q.2 ∈
      (D.rootSubgroup q.1 : Set (Variety.Point K)) := by
    rw [← hC.rootCurve_range q.1]
    exact Set.mem_range_self _
  exact hxq

public theorem rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainExtension
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base)
    {alpha delta gamma : D.Root}
    (hExt : RankTwoPositiveChainExtension D C P e base alpha delta gamma) :
    (D.rootSubgroup gamma).toSubgroup ≤
      RootSubgroupGenerated D (RankTwoPositiveChainSupport D P e base gamma) := by
  exact rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainExtension_of_certificate
    D C P e base (RankTwoChevalleyParameterCertificate.of_system D C P e base hC) hExt

/-- Induction form of positive-chain isolation: if a subgroup already contains
every root subgroup in the allowed support, it also contains the endpoint root
subgroup. -/
public theorem rootSubgroup_le_of_rankTwoPositiveChainExtension_of_certificate
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {alpha delta gamma : D.Root}
    (hExt : RankTwoPositiveChainExtension D C P e base alpha delta gamma)
    (H : Subgroup (Variety.Point K))
    (hSupport : ∀ rho, rho ∈ RankTwoPositiveChainSupport D P e base gamma →
      (D.rootSubgroup rho).toSubgroup ≤ H) :
    (D.rootSubgroup gamma).toSubgroup ≤ H := by
  exact (rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainExtension_of_certificate
    D C P e base hC hExt).trans
      (RootSubgroupGenerated_le_of_rootSubgroup_le D _ H hSupport)

public theorem rootSubgroup_le_of_rankTwoPositiveChainExtension
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base)
    {alpha delta gamma : D.Root}
    (hExt : RankTwoPositiveChainExtension D C P e base alpha delta gamma)
    (H : Subgroup (Variety.Point K))
    (hSupport : ∀ rho, rho ∈ RankTwoPositiveChainSupport D P e base gamma →
      (D.rootSubgroup rho).toSubgroup ≤ H) :
    (D.rootSubgroup gamma).toSubgroup ≤ H := by
  exact rootSubgroup_le_of_rankTwoPositiveChainExtension_of_certificate
    D C P e base
    (RankTwoChevalleyParameterCertificate.of_system D C P e base hC) hExt H hSupport

/-- Direct characteristic-free isolation from a positive-chain step and the
actual Chevalley/root-realization hypotheses.  The endpoint is generated by
the fundamental roots and the positive roots already available at lower
height. -/
public theorem rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainStep
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) [IsAlgClosed k]
    (hC : IsChevalleySystem D C P e base)
    (hActual : IsRootSystemRealization D P e base)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hStep : RankTwoPositiveChainStep D P e base alpha delta gamma) :
    (D.rootSubgroup gamma).toSubgroup ≤
      RootSubgroupGenerated D (RankTwoPositiveChainSupport D P e base gamma) := by
  exact rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainExtension
    D C P e base hC
      (RankTwoPositiveChainStep.toExtension
        D C P e base hC hActual hAdd hStep)

/-- Direct induction form of characteristic-free rank-two isolation. -/
public theorem rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainStep_of_separateBase
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base) [IsAlgClosed k]
    (hC : IsChevalleySystem D C P e systemBase)
    (hActual : IsRootSystemRealization D P e systemBase)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hStep : RankTwoPositiveChainStep D P e positiveBase alpha delta gamma) :
    (D.rootSubgroup gamma).toSubgroup ≤
      RootSubgroupGenerated D (RankTwoPositiveChainSupport D P e positiveBase gamma) := by
  let hCert := RankTwoChevalleyParameterCertificate.of_system D C P e systemBase hC
  let hPair := RankTwoRootPairingCertificate.of_realization D P e systemBase hActual
  exact rootSubgroup_le_RootSubgroupGenerated_of_rankTwoPositiveChainExtension_of_certificate
    D C P e positiveBase hCert
    (RankTwoPositiveChainStep.toExtension_of_certificate D C P e positiveBase hCert hPair hAdd hStep)

public theorem rootSubgroup_le_of_rankTwoPositiveChainStep_of_separateBase
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base) [IsAlgClosed k]
    (hC : IsChevalleySystem D C P e systemBase)
    (hActual : IsRootSystemRealization D P e systemBase)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hStep : RankTwoPositiveChainStep D P e positiveBase alpha delta gamma)
    (H : Subgroup (Variety.Point K))
    (hSupport : ∀ rho, rho ∈ RankTwoPositiveChainSupport D P e positiveBase gamma →
      (D.rootSubgroup rho).toSubgroup ≤ H) :
    (D.rootSubgroup gamma).toSubgroup ≤ H := by
  let hCert := RankTwoChevalleyParameterCertificate.of_system D C P e systemBase hC
  let hPair := RankTwoRootPairingCertificate.of_realization D P e systemBase hActual
  exact rootSubgroup_le_of_rankTwoPositiveChainExtension_of_certificate
    D C P e positiveBase hCert
    (RankTwoPositiveChainStep.toExtension_of_certificate D C P e positiveBase hCert hPair hAdd hStep)
    H hSupport

public theorem rootSubgroup_le_of_rankTwoPositiveChainStep
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) [IsAlgClosed k]
    (hC : IsChevalleySystem D C P e base)
    (hActual : IsRootSystemRealization D P e base)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hStep : RankTwoPositiveChainStep D P e base alpha delta gamma)
    (H : Subgroup (Variety.Point K))
    (hSupport : ∀ rho, rho ∈ RankTwoPositiveChainSupport D P e base gamma →
      (D.rootSubgroup rho).toSubgroup ≤ H) :
    (D.rootSubgroup gamma).toSubgroup ≤ H := by
  exact rootSubgroup_le_of_rankTwoPositiveChainExtension
    D C P e base hC
      (RankTwoPositiveChainStep.toExtension
        D C P e base hC hActual hAdd hStep)
      H hSupport

/-- Under the explicit nonzero `(1,1)` coefficient certificate, the stronger
immediate-pair isolation gives containment in the subgroup generated by the two
roots of that pair. -/
public theorem rootSubgroup_le_RootSubgroupGenerated_pair_of_rankTwoImmediatePairExtension
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base)
    {alpha delta gamma : D.Root}
    (hExt : RankTwoImmediatePairExtension D C P e base alpha delta gamma) :
    (D.rootSubgroup gamma).toSubgroup ≤ RootSubgroupGenerated D {alpha, delta} := by
  intro x hx
  have hxClosed : x ∈ (D.rootSubgroup gamma : Set (Variety.Point K)) := hx
  have hx' : x ∈ Set.range (C.x gamma) := by
    rw [← (hC.1 gamma).2] at hxClosed
    exact hxClosed
  obtain ⟨t, rfl⟩ := hx'
  obtain ⟨a, b, word, hword, hfactor⟩ := hExt.commutator_isolation t
  have hAlpha : C.x alpha a ∈ RootSubgroupGenerated D {alpha, delta} := by
    apply (rootSubgroup_le_RootSubgroupGenerated D
      (by simp : alpha ∈ ({alpha, delta} : Set D.Root)))
    have : C.x alpha a ∈ (D.rootSubgroup alpha : Set (Variety.Point K)) := by
      rw [← (hC.1 alpha).2]
      exact Set.mem_range_self _
    exact this
  have hDelta : C.x delta b ∈ RootSubgroupGenerated D {alpha, delta} := by
    apply (rootSubgroup_le_RootSubgroupGenerated D
      (by simp : delta ∈ ({alpha, delta} : Set D.Root)))
    have : C.x delta b ∈ (D.rootSubgroup delta : Set (Variety.Point K)) := by
      rw [← (hC.1 delta).2]
      exact Set.mem_range_self _
    exact this
  have hcomm :
      (C.x alpha a)⁻¹ * (C.x delta b)⁻¹ * C.x alpha a * C.x delta b ∈
        RootSubgroupGenerated D {alpha, delta} := by
    exact (RootSubgroupGenerated D {alpha, delta}).mul_mem
      ((RootSubgroupGenerated D {alpha, delta}).mul_mem
        ((RootSubgroupGenerated D {alpha, delta}).mul_mem
          ((RootSubgroupGenerated D {alpha, delta}).inv_mem hAlpha)
          ((RootSubgroupGenerated D {alpha, delta}).inv_mem hDelta)) hAlpha) hDelta
  have hwordmem : FilteredCollection.wordProduct C.x word ∈
      RootSubgroupGenerated D {alpha, delta} := by
    apply Subgroup.list_prod_mem
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion]
    rcases hword q hq with hqa | hqd
    · rw [hqa]
      exact ⟨alpha, by simp, (hC.1 alpha).2 ▸ Set.mem_range_self _⟩
    · rw [hqd]
      exact ⟨delta, by simp, (hC.1 delta).2 ▸ Set.mem_range_self _⟩
  have hprod := (RootSubgroupGenerated D {alpha, delta}).mul_mem hcomm
      ((RootSubgroupGenerated D {alpha, delta}).inv_mem hwordmem)
  have hsolve :
      (C.x alpha a)⁻¹ * (C.x delta b)⁻¹ * C.x alpha a * C.x delta b *
          (FilteredCollection.wordProduct C.x word)⁻¹ = C.x gamma t := by
    rw [hfactor]
    group
  rw [← hsolve]
  exact hprod

end Theory.AlgebraicGroup
