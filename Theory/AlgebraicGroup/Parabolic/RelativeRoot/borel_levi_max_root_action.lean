module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_module_source_action_bridge
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_unique_max_root
public import Theory.AlgebraicGroup.RootData.ChevalleyCommutator

/-!
# Maximal-root action of the induced Levi Borel

For a `RelativeRootRepresentationSource`, this module proves that a root of
maximal absolute height in a fixed relative-root fiber spans a line invariant
under the preimage of the aligned Borel in the Levi.  It also identifies the
action of the torus preimage on that line.

The proof follows the maximal-height step in GLS3, Theorem 1.14.7, without
using that numbered theorem.  Positive source roots have nonnegative relative
height.  Positive-height root factors centralize the chosen layer modulo the
next layer.  For a positive Levi root of relative height zero, the concrete
Chevalley commutator formula produces roots `i * delta + j * gamma`: terms
with `j > 1` lie in the next layer, while a term with `j = 1` would remain in
the fiber with strictly larger absolute height, contradicting maximality.
The exact Borel generation alignment then extends these generator calculations
to every Borel point.

The source torus calculation uses the repository's root-weight convention
`t⁻¹ * x * t = chi(t) x`.  Since the fiber representation is the maintained
left-conjugation action `t * x * t⁻¹`, its honest weight is the inverse of the
pulled-back root character.  The final theorem records precisely that
orientation on the induced Levi Borel and torus.
-/

set_option linter.style.haveILetI false

universe u

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private lemma sourcePointCharacter_inv_apply
    {T : Variety k} [AlgebraicGroup T]
    (chi : TorusCharacter T) (s : Variety.Point T) :
    (chi⁻¹).pointCharacter s = (chi.pointCharacter s)⁻¹ := by
  change ((dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 : k)) =
    ((dPointEquiv 1 (chi.onPoints s) 0 : k))⁻¹
  have hmul := congrFun
    (dPointEquiv_mul 1 (chi.onPoints s)⁻¹ (chi.onPoints s)) 0
  rw [_root_.inv_mul_cancel, dPointEquiv_one] at hmul
  simp only [Pi.one_apply, Pi.mul_apply] at hmul
  have hu : dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 =
      (dPointEquiv 1 (chi.onPoints s) 0)⁻¹ := by
    calc
      dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 =
          dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 *
            dPointEquiv 1 (chi.onPoints s) 0 *
              (dPointEquiv 1 (chi.onPoints s) 0)⁻¹ := by simp
      _ = 1 * (dPointEquiv 1 (chi.onPoints s) 0)⁻¹ := by rw [← hmul]
      _ = (dPointEquiv 1 (chi.onPoints s) 0)⁻¹ := one_mul _
  simpa using congrArg Units.val hu

omit [IsAlgClosed k] in
private lemma sourcePositiveRoot_baseIsPos
    (S : RelativeRootRepresentationSource K) {delta : S.D.Root}
    (hdelta : delta ∈ S.positiveRoots) : S.base.IsPos delta := by
  have hheight := S.rootSystemRealization.2.2.2.2 delta
  simp only [Equiv.refl_apply] at hheight
  rw [RootPairing.Base.isPos_iff, ← hheight]
  rw [S.positiveRoots_actual,
    S.isRealization.2.2.2.2.2.2.2.2.2.2.1] at hdelta
  exact hdelta

omit [IsAlgClosed k] in
private lemma sourcePositiveRoot_coeff_nonneg
    (S : RelativeRootRepresentationSource K) {delta : S.D.Root}
    (hdelta : delta ∈ S.positiveRoots) :
    ∀ j ∈ S.base.support, 0 ≤ S.coeff delta j := by
  classical
  letI := Fintype.ofFinite S.D.Root
  obtain ⟨f, _hfSupport, hfSign, hfRoot⟩ :=
    S.base.exists_root_eq_sum_int delta
  have hcoeff (j : S.D.Root) (hj : j ∈ S.base.support) :
      S.coeff delta j = f j := by
    have hsource := (S.simpleRootExpansion delta).1
    rw [S.base.support.sum_subtype (p := (· ∈ S.base.support)) (by simp)
      (F := inferInstance)] at hsource hfRoot
    have heq :
        ∑ j : S.base.support, (S.coeff delta j : ℚ) • S.pairing.root j =
          ∑ j : S.base.support, (f j : ℚ) • S.pairing.root j :=
      hsource.symm.trans (by
        simpa only [Int.cast_smul_eq_zsmul] using hfRoot)
    have hq := Fintype.linearIndependent_iffₛ.mp S.base.linearIndepOn_root
      (fun j : S.base.support => (S.coeff delta j : ℚ))
      (fun j : S.base.support => (f j : ℚ)) heq ⟨j, hj⟩
    exact_mod_cast hq
  have hfpos : 0 < f := by
    rcases hfSign with hfpos | hfneg
    · exact hfpos
    · exfalso
      have hheightNeg : S.base.height delta < 0 := by
        rw [S.base.height_eq_sum hfRoot]
        exact Finset.sum_neg' (fun j _ => (Pi.lt_def.mp hfneg).1 j) <| by
          obtain ⟨j, hjneg⟩ := (Pi.lt_def.mp hfneg).2
          have hjneg' : f j < 0 := by simpa only [Pi.zero_apply] using hjneg
          have hjne : f j ≠ 0 := by omega
          exact ⟨j, _hfSupport hjne, hjneg'⟩
      exact (not_lt_of_ge (sourcePositiveRoot_baseIsPos S hdelta).le) hheightNeg
  intro j hj
  rw [hcoeff j hj]
  exact (Pi.lt_def.mp hfpos).1 j

omit [IsAlgClosed k] in
private lemma sourcePositiveRoot_relativeHeight_nonneg
    (S : RelativeRootRepresentationSource K) {delta : S.D.Root}
    (hdelta : delta ∈ S.positiveRoots) :
    0 ≤ RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J delta := by
  classical
  letI := Fintype.ofFinite S.D.Root
  rw [← S.base_support_eq_simple_toFinset]
  exact Finset.sum_nonneg fun j hj => by
    by_cases hjJ : j ∈ S.J
    · simp [hjJ]
    · simpa [hjJ] using
        sourcePositiveRoot_coeff_nonneg S hdelta j hj

private lemma sourcePositiveRoot_mem_rootSubsystemSpan_of_relativeHeight_eq_zero
    (S : RelativeRootRepresentationSource K) {delta : S.D.Root}
    (hdelta : delta ∈ S.positiveRoots)
    (hheight : RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset
      S.J delta = 0) :
    delta ∈ RootSubsystemSpan S.D S.J := by
  classical
  letI := Fintype.ofFinite S.D.Root
  apply (S.root_mem_span_iff_mem_rootSubsystemSpan delta).mp
  rw [(S.simpleRootExpansion delta).1]
  apply Submodule.sum_mem
  intro j hj
  by_cases hjJ : j ∈ S.J
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, hjJ, rfl⟩)
  · have hcoeffNonneg : ∀ x ∈ S.base.support, 0 ≤ S.coeff delta x :=
      sourcePositiveRoot_coeff_nonneg S hdelta
    have htermLe : S.coeff delta j ≤
        RelativeRootHeight S.coeff S.base.support S.J delta := by
      rw [RelativeRootHeight]
      have hjTerm :
          S.coeff delta j = if j ∉ S.J then S.coeff delta j else 0 := by
        simp [hjJ]
      rw [hjTerm]
      apply Finset.single_le_sum
          (s := S.base.support)
          (f := fun x => if x ∉ S.J then S.coeff delta x else 0)
      · intro x hx
        by_cases hxJ : x ∈ S.J
        · simp [hxJ]
        · simpa [hxJ] using hcoeffNonneg x hx
      · exact hj
    have hheightBase :
        RelativeRootHeight S.coeff S.base.support S.J delta = 0 := by
      simpa [S.base_support_eq_simple_toFinset] using hheight
    have hcoeffZero : S.coeff delta j = 0 := by
      have hnonneg := hcoeffNonneg j hj
      omega
    rw [hcoeffZero]
    simp

omit [IsAlgClosed k] in
private lemma sourcePositiveRootFactor_le_sourceRelativeRootLayer_normalizer
    (S : RelativeRootRepresentationSource K) (i : ℕ) :
    RootSubgroupGenerated S.D S.positiveRoots ≤
      Subgroup.normalizer
        (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
          S.coeff S.J i : Set (Variety.Point K)) := by
  classical
  letI := Fintype.ofFinite S.D.Root
  rw [RootSubgroupGenerated_le_iff]
  intro delta hdelta
  have hnonneg := sourcePositiveRoot_relativeHeight_nonneg S hdelta
  cases i with
  | zero =>
      have hrootLe : (S.D.rootSubgroup delta).toSubgroup ≤
          sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
            S.coeff S.J 0 := by
        rw [sourceRelativeRootLayer, RelativeRootSeries]
        exact rootSubgroup_le_RootSubgroupGenerated S.D (by simpa using hnonneg)
      exact hrootLe.trans
        (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
          S.coeff S.J 0).le_normalizer
  | succ n =>
      by_cases hzero : RelativeRootHeight S.coeff
          S.D.simple.toFinite.toFinset S.J delta = 0
      · have hbaseZero : RelativeRootHeight S.coeff S.base.support S.J delta = 0 := by
          simpa [S.base_support_eq_simple_toFinset] using hzero
        simpa [sourceRelativeRootLayer, S.base_support_eq_simple_toFinset] using
          (rootSubgroup_le_normalizer_relativeRootSeries_of_height_zero
            S.D S.C S.pairing (Equiv.refl S.D.Root) S.base S.coeff
            S.simpleRootExpansion S.chevalleySystem S.J (n + 1)
            (by omega) delta (by simpa using hbaseZero))
      · have hpositive : (1 : ℤ) ≤ RelativeRootHeight S.coeff
            S.D.simple.toFinite.toFinset S.J delta := by
          omega
        have hrootLe : (S.D.rootSubgroup delta).toSubgroup ≤
            sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
              S.coeff S.J 1 := by
          rw [sourceRelativeRootLayer, RelativeRootSeries]
          exact rootSubgroup_le_RootSubgroupGenerated S.D (by simpa using hpositive)
        apply hrootLe.trans
        rw [Subgroup.le_normalizer_iff_commutator_le_left]
        have hcomm := relativeRootSeries_commutator_series_le
          S.D S.C S.pairing (Equiv.refl S.D.Root) S.base S.coeff
            S.simpleRootExpansion S.chevalleySystem S.J (n + 1) (by omega)
        have hnextLe := relativeRootSeries_antitone S.D
          (Equiv.refl S.D.Root) S.base.support S.coeff S.J
            (show n + 1 ≤ n + 1 + 1 by omega)
        simpa [sourceRelativeRootLayer, S.base_support_eq_simple_toFinset] using
          hcomm.trans hnextLe

omit [IsAlgClosed k] in
private lemma sourceBorel_le_sourceRelativeRootLayer_normalizer
    (S : RelativeRootRepresentationSource K) (i : ℕ) :
    S.B.toSubgroup ≤
      Subgroup.normalizer
        (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
          S.coeff S.J i : Set (Variety.Point K)) := by
  rw [S.borel_alignment]
  exact sup_le
    (sourcePositiveRootFactor_le_sourceRelativeRootLayer_normalizer S i)
    (S.torus_le_sourceRelativeRootLayer_normalizer i)

@[reducible]
private noncomputable def sourceSubgroupConjugationAction
    (L H : Subgroup (Variety.Point K))
    (hL : L ≤ Subgroup.normalizer (H : Set (Variety.Point K))) :
    MulDistribMulAction L H := by
  let inclusion : L →* Subgroup.normalizer (H : Set (Variety.Point K)) :=
    { toFun := fun l => ⟨l.1, hL l.2⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  exact MulDistribMulAction.compHom H inclusion

/-- Conjugation by the aligned source Borel on the source relative-root layer
quotient.  Its implementation remains hidden; clients use the maximal-root
action theorem below. -/
@[reducible]
public noncomputable def sourceBorelQuotientConjugationAction
    (S : RelativeRootRepresentationSource K) :
    MulDistribMulAction S.B.toSubgroup (relativeRootLayerQuotient S) := by
  let H : Subgroup (Variety.Point K) :=
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J S.height
  let Hnext : Subgroup (Variety.Point K) :=
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J (S.height + 1)
  let hBH : S.B.toSubgroup ≤ Subgroup.normalizer (H : Set (Variety.Point K)) :=
    sourceBorel_le_sourceRelativeRootLayer_normalizer S S.height
  let hBnext : S.B.toSubgroup ≤
      Subgroup.normalizer (Hnext : Set (Variety.Point K)) :=
    sourceBorel_le_sourceRelativeRootLayer_normalizer S (S.height + 1)
  letI : MulDistribMulAction S.B.toSubgroup H :=
    sourceSubgroupConjugationAction S.B.toSubgroup H hBH
  let N : Subgroup H := Hnext.subgroupOf H
  let hInv : IsInvariant S.B.toSubgroup H N := by
    constructor
    intro b x
    change x.1 ∈ Hnext ↔
      ((sourceSubgroupConjugationAction S.B.toSubgroup H hBH).smul b x :
        Variety.Point K) ∈ Hnext
    change x.1 ∈ Hnext ↔ b.1 * x.1 * b.1⁻¹ ∈ Hnext
    have hnorm := hBnext b.2
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact hnorm x.1
  let : IsInvariant S.B.toSubgroup H N := hInv
  let : N.Normal := by
    dsimp only [N, H, Hnext]
    exact sourceRelativeRootLayer_next_normal S
  change MulDistribMulAction S.B.toSubgroup (H ⧸ N)
  exact quotientMulDistribMulAction N hInv

omit [IsAlgClosed k] in
private lemma sourceBorelQuotientConjugationAction_mk
    (S : RelativeRootRepresentationSource K)
    (b : S.B.toSubgroup)
    (x : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J S.height) :
    (sourceBorelQuotientConjugationAction S).smul b
        (show relativeRootLayerQuotient S from QuotientGroup.mk'
          (sourceAbstractNextLayer S) x) =
      QuotientGroup.mk' (sourceAbstractNextLayer S)
        ⟨b.1 * x.1 * b.1⁻¹, by
          have hnorm := sourceBorel_le_sourceRelativeRootLayer_normalizer
            S S.height b.2
          rw [Subgroup.mem_normalizer_iff] at hnorm
          exact (hnorm x.1).mp x.2⟩ := by
  let H : Subgroup (Variety.Point K) :=
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J S.height
  let Hnext : Subgroup (Variety.Point K) :=
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J (S.height + 1)
  let hBH : S.B.toSubgroup ≤ Subgroup.normalizer (H : Set (Variety.Point K)) :=
    sourceBorel_le_sourceRelativeRootLayer_normalizer S S.height
  let hBnext : S.B.toSubgroup ≤
      Subgroup.normalizer (Hnext : Set (Variety.Point K)) :=
    sourceBorel_le_sourceRelativeRootLayer_normalizer S (S.height + 1)
  letI : MulDistribMulAction S.B.toSubgroup H :=
    sourceSubgroupConjugationAction S.B.toSubgroup H hBH
  let N : Subgroup H := Hnext.subgroupOf H
  let hInv : IsInvariant S.B.toSubgroup H N := by
    constructor
    intro a y
    change y.1 ∈ Hnext ↔
      ((sourceSubgroupConjugationAction S.B.toSubgroup H hBH).smul a y :
        Variety.Point K) ∈ Hnext
    change y.1 ∈ Hnext ↔ a.1 * y.1 * a.1⁻¹ ∈ Hnext
    have hnorm := hBnext a.2
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact hnorm y.1
  let : IsInvariant S.B.toSubgroup H N := hInv
  let : N.Normal := by
    dsimp only [N, H, Hnext]
    exact sourceRelativeRootLayer_next_normal S
  change (quotientMulDistribMulAction N hInv).smul b (QuotientGroup.mk' N x) = _
  rfl

omit [IsAlgClosed k] in
private lemma sourceHeight_of_validChevalleyCommutatorTerm
    (S : RelativeRootRepresentationSource K) {alpha beta : S.D.Root}
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hq : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) alpha beta q) :
    S.base.height q.root =
      (q.i : ℤ) * S.base.height alpha +
        (q.j : ℤ) * S.base.height beta := by
  classical
  obtain ⟨f, -, -, hf⟩ := S.base.exists_root_eq_sum_int alpha
  obtain ⟨g, -, -, hg⟩ := S.base.exists_root_eq_sum_int beta
  have hf : S.pairing.root alpha =
      ∑ l ∈ S.base.support, f l • S.pairing.root l := hf
  have hg : S.pairing.root beta =
      ∑ l ∈ S.base.support, g l • S.pairing.root l := hg

  have hqexp : S.pairing.root q.root =
      ∑ l ∈ S.base.support,
        ((q.i : ℤ) * f l + (q.j : ℤ) * g l) • S.pairing.root l := by
    have hq' : S.pairing.root q.root =
        (q.i : ℤ) • S.pairing.root alpha +
          (q.j : ℤ) • S.pairing.root beta := by
      simpa only [Equiv.refl_apply, Nat.cast_smul_eq_nsmul ℚ,
        ← natCast_zsmul] using hq.2.2
    rw [hq', hf, hg]
    simp_rw [Finset.smul_sum, smul_smul, add_zsmul,
      Finset.sum_add_distrib]
  rw [S.base.height_eq_sum hqexp, S.base.height_eq_sum hf,
    S.base.height_eq_sum hg]
  simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

omit [IsAlgClosed k] in
private lemma sourcePositiveRoot_exactRoot_linearIndependent
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ S.positiveRoots)
    (gamma : RelativeRootSourceExactIndex S) (hne : delta ≠ gamma.1) :
    AreLinearlyIndependentRoots S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 := by
  letI := Fintype.ofFinite S.D.Root
  letI := S.pairing.indexNeg
  have hdeltaPos := sourcePositiveRoot_baseIsPos S hdelta
  have hgammaPos : S.base.IsPos gamma.1 := by
    apply base_isPos_of_relativeRootHeight_pos S.pairing S.base S.J S.coeff
      S.simpleRootExpansion
    rw [S.base_support_eq_simple_toFinset, gamma.2]
    exact_mod_cast S.height_pos
  have hnotopp : S.pairing.root delta ≠ -S.pairing.root gamma.1 := by
    intro hopp
    have hidx : delta = -gamma.1 :=
      S.pairing.root.injective <| by simpa using hopp
    rw [hidx, RootPairing.Base.isPos_iff,
      S.base.height_reflectionPerm_self] at hdeltaPos
    rw [RootPairing.Base.isPos_iff] at hgammaPos
    omega
  have hlin : LinearIndependent ℚ
      ![S.pairing.root delta, S.pairing.root gamma.1] :=
    RootPairing.IsReduced.linearIndependent (P := S.pairing) hne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

private lemma sourceValidTerm_mem_fiber_of_positive_zeroHeight
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ S.positiveRoots)
    (hdeltaHeight : RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J delta = 0)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 q)
    (hqj : q.j = 1) :
    q.root ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root := by
  letI := Fintype.ofFinite S.D.Root
  have hdeltaSpan :=
    sourcePositiveRoot_mem_rootSubsystemSpan_of_relativeHeight_eq_zero
      S hdelta hdeltaHeight
  have hspanDelta :=
    (S.root_mem_span_iff_mem_rootSubsystemSpan delta).mpr hdeltaSpan
  have hspan : S.pairing.root q.root - S.pairing.root gamma.1 ∈
      Submodule.span ℚ (S.pairing.root '' S.J) := by
    have hroot := hvalid.2.2
    simp only [Equiv.refl_apply, hqj, Nat.cast_one, one_smul] at hroot
    rw [hroot]
    simpa [add_sub_cancel_right] using
      (Submodule.smul_mem (Submodule.span ℚ (S.pairing.root '' S.J))
        (q.i : ℚ) hspanDelta)
  have hJ : S.J ⊆ S.base.support := by
    intro j hj
    exact (S.rootSystemRealization.2.2.2.1 j).mp (S.J_simple hj)
  have hprojection := projection_eq_of_root_sub_mem_span S.pairing S.base S.J
    hJ S.coeff S.simpleRootExpansion hspan
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [S.base_support_eq_simple_toFinset] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hqheight : RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root = S.height := by
    rw [hheight, hdeltaHeight, gamma.2.2, hqj]
    simp
  refine ⟨⟨Set.mem_univ _, ?_⟩, hqheight⟩
  have hsimple : (S.base.support : Set S.D.Root) = S.D.simple := by
    ext root
    exact (S.rootSystemRealization.2.2.2.1 root).symm
  rw [← hsimple]
  exact hprojection.trans (by
    rw [hsimple]
    exact gamma.2.1.2)

private lemma sourcePositiveValidTerm_mem_nextLayer
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ S.positiveRoots)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1)
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 q) (a : k) :
    S.C.x q.root a ∈ sourceRelativeRootLayer S.D
      S.D.simple.toFinite.toFinset S.coeff S.J (S.height + 1) := by
  letI := Fintype.ofFinite S.D.Root
  have hdeltaHeight := sourcePositiveRoot_relativeHeight_nonneg S hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [S.base_support_eq_simple_toFinset] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hbound : (S.height + 1 : ℕ) ≤ RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root := by
    rw [hheight, gamma.2.2]
    by_cases hdeltaZero : RelativeRootHeight S.coeff
        S.D.simple.toFinite.toFinset S.J delta = 0
    · by_cases hqj : q.j = 1
      · have hqFiber := sourceValidTerm_mem_fiber_of_positive_zeroHeight
          S hdelta hdeltaZero gamma q hvalid hqj
        have hmaxD := hgammaMax q.root hqFiber
        have hmaxBase : S.base.height q.root ≤ S.base.height gamma.1 := by
          have hqHeight := S.rootSystemRealization.2.2.2.2 q.root
          have hgammaHeight := S.rootSystemRealization.2.2.2.2 gamma.1
          simp only [Equiv.refl_apply] at hqHeight hgammaHeight
          rw [hqHeight, hgammaHeight] at hmaxD
          exact hmaxD
        have habsolute := sourceHeight_of_validChevalleyCommutatorTerm S q hvalid
        rw [habsolute, hqj] at hmaxBase
        have hdeltaPos := sourcePositiveRoot_baseIsPos S hdelta
        rw [RootPairing.Base.isPos_iff] at hdeltaPos
        have hqi : (0 : ℤ) < q.i := by exact_mod_cast hvalid.1
        exfalso
        norm_num at hmaxBase
        nlinarith
      · have hqjLower : (2 : ℤ) ≤ q.j := by
          have : 0 < q.j := hvalid.2.1
          omega
        have hheightPos : (0 : ℤ) < S.height := by
          exact_mod_cast S.height_pos
        norm_num
        nlinarith
    · have hdeltaPositive : (1 : ℤ) ≤ RelativeRootHeight S.coeff
          S.D.simple.toFinite.toFinset S.J delta := by omega
      have hqi : (1 : ℤ) ≤ q.i := by exact_mod_cast hvalid.1
      have hqj : (1 : ℤ) ≤ q.j := by exact_mod_cast hvalid.2.1
      have hheightPos : (0 : ℤ) < S.height := by exact_mod_cast S.height_pos
      norm_num
      nlinarith
  rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨q.root, by simpa using hbound, ?_⟩
  rw [← (S.chevalleySystem.1 q.root).2]
  exact ⟨a, rfl⟩

omit [IsAlgClosed k] in
private lemma sourceChevalleyRoot_mem_borel
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ S.positiveRoots) (s : k) :
    S.C.x delta s ∈ S.B := by
  change S.C.x delta s ∈ S.B.toSubgroup
  rw [S.borel_alignment]
  have hx : S.C.x delta s ∈ (S.D.rootSubgroup delta).toSubgroup := by
    rw [← S.chevalleyParametrization_value delta s]
    exact ((S.D.rootSubgroup delta).pointEquiv
      ((S.chevalleyParametrization delta).value s)).2
  exact (le_sup_left : RootSubgroupGenerated S.D S.positiveRoots ≤ _)
    ((rootSubgroup_le_RootSubgroupGenerated S.D hdelta) hx)

omit [IsAlgClosed k] in
private lemma sourceTorus_mem_borel
    (S : RelativeRootRepresentationSource K)
    (s : Variety.Point S.T.carrierVariety) :
    S.T.includePoint s ∈ S.B := by
  change S.T.includePoint s ∈ S.B.toSubgroup
  rw [S.borel_alignment]
  exact (le_sup_right : S.T.toSubgroup ≤ _) (S.T.pointEquiv s).2

private lemma sourcePositiveRoot_commutator_le_nextLayer
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ S.positiveRoots)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1)
    (hne : delta ≠ gamma.1) :
    ⁅(S.D.rootSubgroup delta).toSubgroup,
        (S.D.rootSubgroup gamma.1).toSubgroup⁆ ≤
      sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J (S.height + 1) := by
  letI := Fintype.ofFinite S.D.Root
  apply (rootSubgroup_commutator_le_chevalleyCommutatorRoots
    S.D S.C S.pairing (Equiv.refl S.D.Root) S.base S.chevalleySystem
      (sourcePositiveRoot_exactRoot_linearIndependent S hdelta
        ⟨gamma.1, gamma.2.2⟩ hne)).trans
  rw [RootSubgroupGenerated_le_iff]
  intro eta heta
  rw [mem_chevalleyCommutatorRoots_iff] at heta
  rcases heta with ⟨i, j, hi, hj, hroot⟩
  let q : ChevalleyCommutatorTerm S.D.Root := ⟨i, j, eta⟩
  have hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 q := ⟨hi, hj, hroot⟩
  intro x hx
  have hetaRoot : (S.D.rootSubgroup eta : Set (Variety.Point K)) =
      Set.range (S.C.x eta) := by
    simpa using (S.chevalleySystem.1 eta).2.symm
  have hx' : x ∈ (S.D.rootSubgroup eta : Set (Variety.Point K)) := hx
  rw [hetaRoot] at hx'
  rcases hx' with ⟨a, rfl⟩
  exact sourcePositiveValidTerm_mem_nextLayer
    S hdelta gamma hgammaMax q hvalid a

private lemma sourcePositiveRoot_action_maximalGenerator
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ S.positiveRoots)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1)
    (s t : k) :
    (sourceBorelQuotientConjugationAction S).smul
        (⟨S.C.x delta s, sourceChevalleyRoot_mem_borel S hdelta s⟩ :
          S.B.toSubgroup)
        (show relativeRootLayerQuotient S from
          QuotientGroup.mk' (sourceAbstractNextLayer S)
            (relativeRootLayerElement S gamma.1 gamma.2 t)) =
      QuotientGroup.mk' (sourceAbstractNextLayer S)
        (relativeRootLayerElement S gamma.1 gamma.2 t) := by
  let b : S.B.toSubgroup :=
    ⟨S.C.x delta s, sourceChevalleyRoot_mem_borel S hdelta s⟩
  let y := relativeRootLayerElement S gamma.1 gamma.2 t
  rw [show (⟨S.C.x delta s, sourceChevalleyRoot_mem_borel S hdelta s⟩ :
      S.B.toSubgroup) = b by rfl]
  rw [show relativeRootLayerElement S gamma.1 gamma.2 t = y by rfl]
  rw [sourceBorelQuotientConjugationAction_mk]
  have htarget : S.C.x delta s * S.C.x gamma.1 t * (S.C.x delta s)⁻¹ *
      (S.C.x gamma.1 t)⁻¹ ∈
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J (S.height + 1) := by
    by_cases hsame : delta = gamma.1
    · subst delta
      rw [S.chevalleySystem.2.2.2.1 gamma.1 s t, add_comm s t,
        ← S.chevalleySystem.2.2.2.1 gamma.1 t s]
      simp
    · have hx : S.C.x delta s ∈ S.D.rootSubgroup delta := by
        rw [← S.chevalleyParametrization_value delta s]
        exact ((S.D.rootSubgroup delta).pointEquiv
          ((S.chevalleyParametrization delta).value s)).2
      have hy : S.C.x gamma.1 t ∈ S.D.rootSubgroup gamma.1 := by
        rw [← S.chevalleyParametrization_value gamma.1 t]
        exact ((S.D.rootSubgroup gamma.1).pointEquiv
          ((S.chevalleyParametrization gamma.1).value t)).2
      have hle := sourcePositiveRoot_commutator_le_nextLayer
        S hdelta gamma hgammaMax hsame
      rw [Subgroup.commutator_le] at hle
      have hcomm := hle (S.C.x delta s) hx
        (S.C.x gamma.1 t) hy
      simpa [commutatorElement_def] using hcomm
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (((⟨b.1 * y.1 * b.1⁻¹, by
      have hnorm := sourceBorel_le_sourceRelativeRootLayer_normalizer
        S S.height b.2
      rw [Subgroup.mem_normalizer_iff] at hnorm
      exact (hnorm y.1).mp y.2⟩ /
        y : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
          S.coeff S.J S.height) : Variety.Point K) ∈
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J (S.height + 1))
  simpa [b, y, div_eq_mul_inv, relativeRootLayerElement_coe] using htarget

private lemma sourceTorus_action_generator
    (S : RelativeRootRepresentationSource K)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (s : Variety.Point S.T.carrierVariety) (t : k) :
    (sourceBorelQuotientConjugationAction S).smul
        (⟨S.T.includePoint s, sourceTorus_mem_borel S s⟩ :
          S.B.toSubgroup)
        (show relativeRootLayerQuotient S from
          QuotientGroup.mk' (sourceAbstractNextLayer S)
            (relativeRootLayerElement S gamma.1 gamma.2 t)) =
      QuotientGroup.mk' (sourceAbstractNextLayer S)
        (relativeRootLayerElement S gamma.1 gamma.2
          (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * t)) := by
  have hconj : S.T.includePoint s * S.C.x gamma.1 t *
      (S.T.includePoint s)⁻¹ =
    S.C.x gamma.1
      (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * t) := by
    have hweight := S.isRealization.2.2.1 gamma.1
    have h := hweight.2 (S.chevalleyParametrization gamma.1) t s⁻¹
    rw [S.chevalleyParametrization_value,
      S.chevalleyParametrization_value] at h
    change (S.T.inclusion.onPoints s⁻¹)⁻¹ * S.C.x gamma.1 t *
        S.T.inclusion.onPoints s⁻¹ = _ at h
    rw [map_inv, map_inv] at h
    have hinclude : S.T.includePoint s = S.T.inclusion.onPoints s := rfl
    rw [hinclude]
    simpa only [inv_inv] using h
  rw [sourceBorelQuotientConjugationAction_mk]
  apply congrArg (QuotientGroup.mk' (sourceAbstractNextLayer S))
  apply Subtype.ext
  simpa only [relativeRootLayerElement_coe] using hconj

private noncomputable def sourceMaximalRootScalarSubgroup
    (S : RelativeRootRepresentationSource K)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) :
    Subgroup S.B.toSubgroup := by
  let A := sourceBorelQuotientConjugationAction S
  let MA : MulAction S.B.toSubgroup (relativeRootLayerQuotient S) :=
    @MulDistribMulAction.toMulAction _ _ _ _ A
  let SGA : SemigroupAction S.B.toSubgroup (relativeRootLayerQuotient S) :=
    @MulAction.toSemigroupAction _ _ _ MA
  let SA : SMul S.B.toSubgroup (relativeRootLayerQuotient S) :=
    @SemigroupAction.toSMul _ _ _ SGA
  let act := @SMul.smul S.B.toSubgroup (relativeRootLayerQuotient S) SA
  let qgen (t : k) : relativeRootLayerQuotient S :=
    QuotientGroup.mk' (sourceAbstractNextLayer S)
      (relativeRootLayerElement S gamma.1 gamma.2 t)
  refine
    { carrier := {b | ∃ c : kˣ, ∀ t : k,
        act b (qgen t) = qgen ((c : k) * t)}
      one_mem' := ⟨1, fun t => by
        simp only [Units.val_one, one_mul]
        dsimp only [act, SA, SGA, MA, A]
        change (sourceBorelQuotientConjugationAction S).smul 1 (qgen t) = qgen t
        dsimp only [qgen]
        rw [sourceBorelQuotientConjugationAction_mk]
        apply congrArg (QuotientGroup.mk' (sourceAbstractNextLayer S))
        apply Subtype.ext
        simp⟩
      mul_mem' := by
        rintro b d ⟨c, hc⟩ ⟨e, he⟩
        refine ⟨c * e, ?_⟩
        intro t
        calc
          act (b * d) (qgen t) = act b (act d (qgen t)) :=
            (@mul_smul S.B.toSubgroup (relativeRootLayerQuotient S)
              _ SGA b d (qgen t))
          _ = act b (qgen ((e : k) * t)) :=
            congrArg (fun q => act b q) (he t)
          _ = qgen ((c : k) * ((e : k) * t)) := hc _
          _ = qgen (((c * e : kˣ) : k) * t) := by
            apply congrArg qgen
            simp [mul_assoc]
      inv_mem' := by
        rintro b ⟨c, hc⟩
        refine ⟨c⁻¹, ?_⟩
        intro t
        have h : act b (qgen ((c⁻¹ : kˣ) * t)) = qgen t := by
          rw [hc]
          apply congrArg qgen
          simp
        calc
          act b⁻¹ (qgen t) =
              act b⁻¹ (act b (qgen ((c⁻¹ : kˣ) * t))) :=
            congrArg (fun q => act b⁻¹ q) h.symm
          _ = act (b⁻¹ * b) (qgen ((c⁻¹ : kˣ) * t)) :=
            (@mul_smul S.B.toSubgroup (relativeRootLayerQuotient S)
              _ SGA b⁻¹ b _).symm
          _ = act 1 (qgen ((c⁻¹ : kˣ) * t)) := by
            rw [_root_.inv_mul_cancel]
          _ = qgen ((c⁻¹ : kˣ) * t) :=
            @MulAction.one_smul S.B.toSubgroup (relativeRootLayerQuotient S)
              _ MA _ }

private lemma sourceBorel_le_maximalRootScalarSubgroup_map
    (S : RelativeRootRepresentationSource K)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1) :
    S.B.toSubgroup ≤ Subgroup.map S.B.toSubgroup.subtype
      (sourceMaximalRootScalarSubgroup S gamma) := by
  intro x hxB
  have hxSup : x ∈
      RootSubgroupGenerated S.D S.positiveRoots ⊔ S.T.toSubgroup := by
    rw [← S.borel_alignment]
    exact hxB
  have hRoot : RootSubgroupGenerated S.D S.positiveRoots ≤
      Subgroup.map S.B.toSubgroup.subtype
        (sourceMaximalRootScalarSubgroup S gamma) := by
    rw [RootSubgroupGenerated_le_iff]
    intro delta hdelta x hx
    have hx' : x ∈ (S.D.rootSubgroup delta : Set (Variety.Point K)) := hx
    have hroot : (S.D.rootSubgroup delta : Set (Variety.Point K)) =
        Set.range (S.C.x delta) := by
      simpa using (S.chevalleySystem.1 delta).2.symm
    rw [hroot] at hx'
    rcases hx' with ⟨s, rfl⟩
    let b : S.B.toSubgroup :=
      ⟨S.C.x delta s, sourceChevalleyRoot_mem_borel S hdelta s⟩
    have hb : b ∈ sourceMaximalRootScalarSubgroup S gamma := by
      refine ⟨1, ?_⟩
      intro t
      simpa only [b, Units.val_one, one_mul] using
        sourcePositiveRoot_action_maximalGenerator
          S hdelta gamma hgammaMax s t
    exact ⟨b, hb, rfl⟩
  have hTorus : S.T.toSubgroup ≤
      Subgroup.map S.B.toSubgroup.subtype
        (sourceMaximalRootScalarSubgroup S gamma) := by
    intro x hx
    let s : Variety.Point S.T.carrierVariety :=
      S.T.pointEquiv.symm ⟨x, hx⟩
    have hs : S.T.includePoint s = x := by
      change (S.T.pointEquiv s).1 = x
      rw [S.T.pointEquiv.apply_symm_apply]
    let b : S.B.toSubgroup :=
      ⟨S.T.includePoint s, sourceTorus_mem_borel S s⟩
    have hb : b ∈ sourceMaximalRootScalarSubgroup S gamma := by
      let c : kˣ := Units.mk0
        ((S.D.rootWeight gamma.1).pointCharacter s)⁻¹
        (inv_ne_zero (Units.ne_zero
          (dPointEquiv 1 ((S.D.rootWeight gamma.1).onPoints s) 0)))
      refine ⟨c, ?_⟩
      intro t
      rw [show (c : k) =
        ((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ by rfl]
      exact sourceTorus_action_generator S gamma s t
    exact ⟨b, hb, hs⟩
  have hSup : RootSubgroupGenerated S.D S.positiveRoots ⊔ S.T.toSubgroup ≤
      Subgroup.map S.B.toSubgroup.subtype
        (sourceMaximalRootScalarSubgroup S gamma) :=
    sup_le hRoot hTorus
  exact hSup hxSup

/-- Every point of the aligned source Borel acts by a nonzero scalar on the
maximal-height root generator in the adjacent relative-root quotient. -/
public theorem sourceBorel_action_maximalRootGenerator
    (S : RelativeRootRepresentationSource K)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1)
    (b : S.B.toSubgroup) :
    ∃ c : kˣ, ∀ t : k,
      (sourceBorelQuotientConjugationAction S).smul b
          (show relativeRootLayerQuotient S from
            QuotientGroup.mk' (sourceAbstractNextLayer S)
              (relativeRootLayerElement S gamma.1 gamma.2 t)) =
        QuotientGroup.mk' (sourceAbstractNextLayer S)
          (relativeRootLayerElement S gamma.1 gamma.2 ((c : k) * t)) := by
  have hbMap := sourceBorel_le_maximalRootScalarSubgroup_map
    S gamma hgammaMax b.2
  rcases hbMap with ⟨b', hb', hvalue⟩
  have hbb : b' = b := Subtype.ext hvalue
  subst b'
  exact hb'

private lemma sourceFiberConjugationHom_eq_borelAction_generator
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (hl : S.L.includePoint l ∈ S.B)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (t : k) :
    (S.sourceFiberConjugationHom l
        (relativeRootFiberQuotientGenerator S (gamma, t)) :
          relativeRootLayerQuotient S) =
      (sourceBorelQuotientConjugationAction S).smul
        (⟨S.L.includePoint l, hl⟩ : S.B.toSubgroup)
        (show relativeRootLayerQuotient S from
          QuotientGroup.mk' (sourceAbstractNextLayer S)
            (relativeRootLayerElement S gamma.1 gamma.2 t)) := by
  rcases S.sourceFiberConjugationHom_generator_value l (gamma, t) with
    ⟨y, hy, hqy⟩
  rw [hqy, sourceBorelQuotientConjugationAction_mk]
  apply congrArg (QuotientGroup.mk' (sourceAbstractNextLayer S))
  apply Subtype.ext
  simpa only [relativeRootLayerElement_coe] using hy

/-- A maximal-height root vector spans an invariant line under all Levi points
whose ambient images lie in the aligned source Borel. -/
public theorem RelativeRootFiberModule.inducedBorel_action_maximalRootVector
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1)
    (l : Variety.Point S.L.carrierVariety)
    (hl : S.L.includePoint l ∈ S.B) (t : k) :
    ∃ c : kˣ,
      (M.representation.action l).1 (M.rootVector (gamma, t)) =
        (c : k) • M.rootVector (gamma, t) := by
  let b : S.B.toSubgroup := ⟨S.L.includePoint l, hl⟩
  obtain ⟨c, hc⟩ := sourceBorel_action_maximalRootGenerator
    S gamma hgammaMax b
  refine ⟨c, ?_⟩
  have hsource : S.sourceFiberConjugationHom l
      (relativeRootFiberQuotientGenerator S (gamma, t)) =
        relativeRootFiberQuotientGenerator S (gamma, (c : k) * t) := by
    apply Subtype.ext
    calc
      (S.sourceFiberConjugationHom l
          (relativeRootFiberQuotientGenerator S (gamma, t)) :
            relativeRootLayerQuotient S) =
          (sourceBorelQuotientConjugationAction S).smul b
            (show relativeRootLayerQuotient S from
              QuotientGroup.mk' (sourceAbstractNextLayer S)
                (relativeRootLayerElement S gamma.1 gamma.2 t)) :=
        sourceFiberConjugationHom_eq_borelAction_generator S l hl gamma t
      _ = QuotientGroup.mk' (sourceAbstractNextLayer S)
            (relativeRootLayerElement S gamma.1 gamma.2 ((c : k) * t)) := hc t
      _ = (relativeRootFiberQuotientGenerator S (gamma, (c : k) * t) :
            relativeRootLayerQuotient S) :=
        (relativeRootFiberQuotientGenerator_coe S
          (gamma, (c : k) * t)).symm
  calc
    (M.representation.action l).1 (M.rootVector (gamma, t)) =
        Multiplicative.toAdd
          (M.pointEquiv (S.sourceFiberConjugationHom l
            (relativeRootFiberQuotientGenerator S (gamma, t)))) :=
      M.representation_action_rootVector l (gamma, t)
    _ = M.rootVector (gamma, (c : k) * t) := by
      rw [hsource]
      exact (M.rootVector_value (gamma, (c : k) * t)).symm
    _ = (c : k) • M.rootVector (gamma, t) := M.rootVector_smul gamma c t

/-- Under left conjugation, a source-torus point acts on a fiber root vector
by the inverse of the source root character. -/
public theorem RelativeRootFiberModule.sourceTorus_action_rootVector
    (S : RelativeRootRepresentationSource K)
    (M : RelativeRootFiberModule S)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (s : Variety.Point S.T.carrierVariety) (t : k) :
    (M.representation.action (sourceTorusLeviPoint S s)).1
        (M.rootVector (gamma, t)) =
      ((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ •
        M.rootVector (gamma, t) := by
  let l := sourceTorusLeviPoint S s
  have hl : S.L.includePoint l ∈ S.B := by
    rw [sourceTorusLeviPoint_include]
    exact sourceTorus_mem_borel S s
  let b : S.B.toSubgroup := ⟨S.L.includePoint l, hl⟩
  let c : k := ((S.D.rootWeight gamma.1).pointCharacter s)⁻¹
  have hsource : S.sourceFiberConjugationHom l
      (relativeRootFiberQuotientGenerator S (gamma, t)) =
        relativeRootFiberQuotientGenerator S (gamma, c * t) := by
    apply Subtype.ext
    calc
      (S.sourceFiberConjugationHom l
          (relativeRootFiberQuotientGenerator S (gamma, t)) :
            relativeRootLayerQuotient S) =
          (sourceBorelQuotientConjugationAction S).smul b
            (show relativeRootLayerQuotient S from
              QuotientGroup.mk' (sourceAbstractNextLayer S)
                (relativeRootLayerElement S gamma.1 gamma.2 t)) :=
        sourceFiberConjugationHom_eq_borelAction_generator S l hl gamma t
      _ = QuotientGroup.mk' (sourceAbstractNextLayer S)
            (relativeRootLayerElement S gamma.1 gamma.2 (c * t)) := by
        exact sourceTorus_action_generator S gamma s t
      _ = (relativeRootFiberQuotientGenerator S (gamma, c * t) :
            relativeRootLayerQuotient S) :=
        (relativeRootFiberQuotientGenerator_coe S (gamma, c * t)).symm
  calc
    (M.representation.action (sourceTorusLeviPoint S s)).1
        (M.rootVector (gamma, t)) =
      Multiplicative.toAdd
        (M.pointEquiv (S.sourceFiberConjugationHom l
          (relativeRootFiberQuotientGenerator S (gamma, t)))) :=
      M.representation_action_rootVector l (gamma, t)
    _ = M.rootVector (gamma, c * t) := by
      rw [hsource]
      exact (M.rootVector_value (gamma, c * t)).symm
    _ = c • M.rootVector (gamma, t) := M.rootVector_smul gamma c t

/-- A nonzero maximal-height root vector is a high-weight vector for the
induced Levi Borel.  Its weight is the inverse pulled-back root character,
as forced by the left-conjugation orientation. -/
public theorem RelativeRootFiberModule.maximalRoot_hasHighWeight_inducedBorel
    (S : RelativeRootRepresentationSource K)
    (M : RelativeRootFiberModule S)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1)
    (z : k) (hz : z ≠ 0) :
    letI : AlgebraicGroup S.L.carrierVariety := S.L.carrierAlgebraicGroup
    let BLevi := S.L.inclusion.closedSubgroupPreimage S.B
    let TLevi := S.L.inclusion.closedSubgroupPreimage S.T
    letI : AlgebraicGroup BLevi.carrierVariety := BLevi.carrierAlgebraicGroup
    letI : AlgebraicGroup TLevi.carrierVariety := TLevi.carrierAlgebraicGroup
    HasHighWeight M.representation BLevi TLevi (M.rootVector (gamma, z))
      ((TorusCharacter.pullback (S.L.inclusion.preimageRestriction S.T)
        (S.D.rootWeight gamma.1))⁻¹) := by
  dsimp only
  letI : AlgebraicGroup S.L.carrierVariety := S.L.carrierAlgebraicGroup
  let BLevi := S.L.inclusion.closedSubgroupPreimage S.B
  let TLevi := S.L.inclusion.closedSubgroupPreimage S.T
  letI : AlgebraicGroup BLevi.carrierVariety := BLevi.carrierAlgebraicGroup
  letI : AlgebraicGroup TLevi.carrierVariety := TLevi.carrierAlgebraicGroup
  constructor
  · refine ⟨M.rootVector_ne_zero gamma hz, ?_⟩
    intro l hl
    change S.L.includePoint l ∈ S.B at hl
    obtain ⟨c, hc⟩ :=
      M.inducedBorel_action_maximalRootVector gamma hgammaMax l hl z
    exact ⟨(c : k), hc⟩
  · refine ⟨M.rootVector_ne_zero gamma hz, ?_⟩
    intro t
    let s : Variety.Point S.T.carrierVariety :=
      (S.L.inclusion.preimageRestriction S.T).onPoints t
    have hTLeviInclude (x : Variety.Point TLevi.carrierVariety) :
        TLevi.includePoint x = TLevi.inclusion.onPoints x := by
      apply Variety.Point.ext
      funext i
      rfl
    have hLInclude (x : Variety.Point S.L.carrierVariety) :
        S.L.includePoint x = S.L.inclusion.onPoints x := by
      apply Variety.Point.ext
      funext i
      rfl
    have hpoint : TLevi.includePoint t = sourceTorusLeviPoint S s := by
      apply S.L.inclusion_injective
      calc
        S.L.inclusion.onPoints (TLevi.includePoint t) =
            S.L.inclusion.onPoints (TLevi.inclusion.onPoints t) := by
          rw [hTLeviInclude]
        _ = S.T.inclusion.onPoints s := by
          simpa only [TLevi, s] using
            (S.L.inclusion.preimageRestriction_inclusion_apply S.T t).symm
        _ = S.L.inclusion.onPoints (sourceTorusLeviPoint S s) := by
          rw [← hLInclude]
          exact (sourceTorusLeviPoint_include S s).symm
    rw [hpoint, M.sourceTorus_action_rootVector S]
    apply congrArg (fun c : k => c • M.rootVector (gamma, z))
    rw [sourcePointCharacter_inv_apply]
    dsimp only [s]
    congr 1
end Theory.AlgebraicGroup
