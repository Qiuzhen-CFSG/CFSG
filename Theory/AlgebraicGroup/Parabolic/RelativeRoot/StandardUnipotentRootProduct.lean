module

public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.UnipotentCandidate
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Commutator
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.StandardParabolic
public import Theory.AlgebraicGroup.Unipotent.Radical

/-!
This module proves that the standard positive-root candidate outside a chosen
Levi subsystem is a unipotent algebraic group, as required in the construction
of the unipotent radical in GLS3, Theorem 1.13.3.  The hypotheses align the
chosen positive roots with the actual positive system and provide compatible
integral and rational based root data together with a Chevalley system.

The standard-Borel setup supplies the root-addition completeness needed by the
positive-root collection interfaces, so no separate completeness hypothesis is
carried by the theorem below.  The proof first shows that the finite family of
connected root subgroups has a closed, connected generated subgroup.
The integral actual-root realization identifies this subgroup with relative-root
series layer one.  Chevalley
commutator collection then bounds its lower central series by successive
relative-height layers; finiteness of the root system makes a sufficiently high
layer trivial, so the candidate is nilpotent and hence solvable.  Its unipotent
radical contains every generating one-parameter root subgroup, forcing equality
with the candidate.  No unipotence or radical property of the candidate is
assumed.
-/

universe u

open scoped commutatorElement Pointwise

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma rootWordProduct_mul_image_prodSet_eq
    {K : Variety k} [AlgebraicGroup K]
    (S T : Set (Variety.Point K)) :
    (AlgebraicGroup.mulMorphism K).toFun '' Variety.prodSet S T = S * T := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine Set.mem_mul.mpr ⟨(Variety.prodPointEquiv K K w).1,
      hw.1, (Variety.prodPointEquiv K K w).2, hw.2, ?_⟩
    rfl
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨(Variety.prodPointEquiv K K).symm (x, y), ?_, ?_⟩
    · exact ⟨hx, hy⟩
    · rfl

omit [IsAlgClosed k] in
private lemma rootWordProduct_isIrreducible
    {K : Variety k} [AlgebraicGroup K]
    {ι : Type*} (H : ι → ClosedSubgroup K)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point K))) :
    ∀ w, IsIrreducible (closedSubgroupWordProduct H w) := by
  intro w
  induction w with
  | nil => exact isIrreducible_singleton
  | cons i w ih =>
      rw [closedSubgroupWordProduct, ← rootWordProduct_mul_image_prodSet_eq]
      exact IsIrreducible.image
        (prodSet_irreducible_of_irreducible
          ((H i).isIrreducible_of_isConnected (hconn i)) ih)
        (AlgebraicGroup.mulMorphism K).toFun
        (AlgebraicGroup.mulMorphism K).continuous.continuousOn

omit [IsAlgClosed k] in
private lemma rootWordProduct_isConnected
    {K : Variety k} [AlgebraicGroup K]
    {ι : Type*} (H : ι → ClosedSubgroup K)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point K)))
    (w : List ι) :
    _root_.IsConnected (closedSubgroupWordProduct H w) :=
  (rootWordProduct_isIrreducible H hconn w).isConnected

omit [IsAlgClosed k] in
private lemma exists_relativeRootHeight_bound
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    {ι : Type*} [Fintype ι]
    (e : D.Root ≃ ι) (base : Finset ι) (coeff : ι → ι → ℤ)
    (J : Set D.Root) :
    ∃ n : ℕ, 0 < n ∧
      ∀ α, RelativeRootHeight coeff base (e '' J) (e α) < (n : ℤ) := by
  let n : ℕ :=
    (Finset.univ.sup fun α : D.Root =>
      Int.natAbs (RelativeRootHeight coeff base (e '' J) (e α))) + 1
  refine ⟨n, by simp [n], ?_⟩
  intro α
  have hle : Int.natAbs (RelativeRootHeight coeff base (e '' J) (e α)) ≤ n - 1 := by
    have hle' :
        Int.natAbs (RelativeRootHeight coeff base (e '' J) (e α)) ≤
          Finset.univ.sup (fun β : D.Root =>
            Int.natAbs (RelativeRootHeight coeff base (e '' J) (e β))) :=
      Finset.le_sup (f := fun β : D.Root =>
        Int.natAbs (RelativeRootHeight coeff base (e '' J) (e β)))
        (Finset.mem_univ α)
    simpa [n] using hle'
  have habs : RelativeRootHeight coeff base (e '' J) (e α) ≤
      Int.natAbs (RelativeRootHeight coeff base (e '' J) (e α)) :=
    Int.le_natAbs
  omega

omit [IsAlgClosed k] in
private lemma relativeRootSeries_one_isNilpotent
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root] (C : ChevalleyData K D)
    {ι X Y : Type*} [Fintype ι]
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    (P : RootPairing ι ℚ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) :
    Group.IsNilpotent (RelativeRootSeries D e base.support coeff J 1) := by
  obtain ⟨n, hn, hbound⟩ :=
    exists_relativeRootHeight_bound D e base.support coeff J
  have hterminal : RelativeRootSeries D e base.support coeff J n = ⊥ :=
    relativeRootSeries_eq_bot_of_height_lt D e base.support coeff J n hbound
  have hcentral : ∀ i : ℕ,
      (RelativeRootSeries D e base.support coeff J 1).lowerCentralSeries i ≤
        RelativeRootSeries D e base.support coeff J (i + 1) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        exact (Subgroup.commutator_mono ih le_rfl).trans
          (relativeRootSeries_commutator_series_le D C P e base coeff hCoeff hC
            J (i + 1) (by omega))
  rw [Subgroup.isNilpotent_iff_lowerCentralSeries]
  refine ⟨n - 1, le_bot_iff.mp ?_⟩
  have hle := hcentral (n - 1)
  have hnIndex : n - 1 + 1 = n := by omega
  rw [hnIndex] at hle
  exact hle.trans_eq hterminal

/-- The standard positive-root candidate outside a simple-root subsystem is a
unipotent algebraic group. -/
public theorem unipotentCandidate_isUnipotentAlgebraicGroup
    {K : Variety k} [AlgebraicGroup K]
    (T B : ClosedSubgroup K) (D : RootGroupData K T) [Fintype D.Root]
    {ι X Y XQ YQ : Type*} [Fintype ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    [AddCommGroup XQ] [Module ℚ XQ] [AddCommGroup YQ] [Module ℚ YQ]
    (Q : RootPairing ι ℚ XQ YQ) [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced]
    (rootBase : Q.Base) (rootBase_support : rootBase.support = base.support)
    (C : ChevalleyData K D) (coeff : ι → ι → ℤ)
    (positiveRoots : Set D.Root)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv D.positive)
    (hCoeff : HasSimpleRootExpansion P base coeff)
    (hRootCoeff : HasSimpleRootExpansion Q rootBase coeff)
    (hC : IsChevalleySystem D C Q e rootBase)
    (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (positiveRoots_actual : positiveRoots = D.positive)
    (J : Set D.Root) (hJ : J ⊆ D.simple) :
    IsUnipotentAlgebraicGroup
      (unipotentCandidate T D positiveRoots J).carrierVariety := by
  classical
  let roots : Set D.Root := positiveRoots \ RootSubsystemSpan D J
  let H : Subgroup (Variety.Point K) := RootSubgroupGenerated D roots
  let rootFamily : roots → ClosedSubgroup K := fun α => D.rootSubgroup α.1
  have hrootFamilyConnected :
      ∀ α, _root_.IsConnected (rootFamily α : Set (Variety.Point K)) := by
    intro α
    have hcarrier : Variety.IsConnected (D.rootSubgroup α.1).carrierVariety :=
      (hSetup.2.1.2.2.1 α.1).1.2.isConnected
    let _ : ConnectedSpace
        (Variety.Point (D.rootSubgroup α.1).carrierVariety) :=
      connectedSpace_iff_univ.mpr hcarrier
    change _root_.IsConnected
      ((D.rootSubgroup α.1).toSubgroup : Set (Variety.Point K))
    rw [← (D.rootSubgroup α.1).range_inclusion]
    exact isConnected_range (D.rootSubgroup α.1).inclusion.toVariety.continuous
  have hHfamily : H = Subgroup.closure
      (⋃ α, (rootFamily α : Set (Variety.Point K))) := by
    simp only [H, roots, RootSubgroupGenerated, rootFamily]
    congr 1
    ext x
    simp only [Set.mem_iUnion, Set.mem_sdiff]
    constructor
    · rintro ⟨α, hα, hx⟩
      exact ⟨⟨α, hα⟩, hx⟩
    · rintro ⟨α, hx⟩
      exact ⟨α.1, α.2, hx⟩
  have hHzariski : IsZariskiClosed K (H : Set (Variety.Point K)) := by
    rw [hHfamily]
    exact closure_iUnion_connected_closedSubgroup_isZariskiClosed
      rootFamily hrootFamilyConnected
  obtain ⟨w, hw⟩ :=
    exists_closedSubgroupWordProduct_eq_closure_iUnion
      rootFamily hrootFamilyConnected
  have hHconnected : _root_.IsConnected (H : Set (Variety.Point K)) := by
    rw [hHfamily, ← hw]
    exact rootWordProduct_isConnected rootFamily hrootFamilyConnected w
  let U := unipotentCandidate T D positiveRoots J
  have hUH : U.toSubgroup = H := by
    dsimp only [U]
    rw [unipotentCandidate_spec]
    apply SetLike.ext
    intro x
    change x ∈ closure
        (standardUnipotentRootFactor D positiveRoots (RootSubsystemSpan D J) :
          Set (Variety.Point K)) ↔ x ∈ H
    have hHclosed : IsClosed (H : Set (Variety.Point K)) :=
      Variety.isClosed_iff_isZariskiClosed.mpr hHzariski
    rw [show standardUnipotentRootFactor D positiveRoots
      (RootSubsystemSpan D J) = H by rfl, hHclosed.closure_eq]
    rfl
  have hParabolicSetup : IsStandardParabolicSetup T B D positiveRoots J
      (RootSubsystemSpan D J) := ⟨hSetup, hJ, rfl⟩
  have hActualPositive :
      IsActualBasedRootDatum D P base e weightEquiv positiveRoots := by
    rw [positiveRoots_actual]
    exact hActual
  have hSeriesOne : RelativeRootSeries D e base.support coeff J 1 = H := by
    exact (relativeRootSeries_one_eq_standardUnipotentRadical
      T B D P base e weightEquiv positiveRoots J (RootSubsystemSpan D J)
      U coeff hActualPositive hCoeff hParabolicSetup (hUH.trans rfl)).trans hUH
  have hHnilpotent : Group.IsNilpotent H := by
    rw [← hSeriesOne]
    rw [← rootBase_support]
    exact relativeRootSeries_one_isNilpotent D C Q e rootBase coeff hRootCoeff hC J
  have hUnilpotent : Group.IsNilpotent U.toSubgroup := by
    rw [hUH]
    exact hHnilpotent
  let _ : Group.IsNilpotent U.toSubgroup := hUnilpotent
  have hUsolvable : Group.IsSolvable (Variety.Point U.carrierVariety) := by
    apply Group.isSolvable_of_isSolvable_injective
      (f := (Equiv.mulEquiv U.pointEquiv).toMonoidHom)
    exact (Equiv.mulEquiv U.pointEquiv).injective
  have hUconnected : _root_.IsConnected (U : Set (Variety.Point K)) := by
    change _root_.IsConnected (U.toSubgroup : Set (Variety.Point K))
    rw [hUH]
    exact hHconnected
  obtain ⟨R, hR, _hRconnected⟩ :=
    exists_unipotentRadical_of_connected_solvable U hUconnected hUsolvable
  have hUR : U ≤ R := by
    have hHR : H ≤ R.toSubgroup := by
      apply RootSubgroupGenerated_le_of_rootSubgroup_le D roots R.toSubgroup
      intro α hα
      apply hR.contains_unipotent_closedSubgroup hUconnected hUsolvable
      · intro x hx
        change x ∈ U.toSubgroup
        rw [hUH]
        exact rootSubgroup_le_RootSubgroupGenerated D hα hx
      · exact (hSetup.2.1.2.2.1 α).1.2.isUnipotentAlgebraicGroup
    intro x hx
    apply hHR
    rw [← hUH]
    exact hx
  have hRU : R ≤ U := hR.1
  have hEq : U = R := SetLike.coe_injective (Set.Subset.antisymm hUR hRU)
  have hUunipotent : IsUnipotentAlgebraicGroup U.carrierVariety := by
    rw [hEq]
    exact hR.2.1
  simpa only [U] using hUunipotent

end Theory.AlgebraicGroup
