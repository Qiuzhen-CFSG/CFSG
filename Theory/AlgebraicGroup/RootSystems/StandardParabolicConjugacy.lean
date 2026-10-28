module

public import Theory.AlgebraicGroup.RootSystems.StandardParabolicLattice
public import Theory.AlgebraicGroup.RootSystems.GraphDegree
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.DoubleCoset

/-!
Finite standard-parabolic double cosets in a Weyl group have minimum-length
representatives.  The proof is the usual Coxeter descent argument:
right (respectively left) multiplication by a simple reflection decreases
length exactly when the corresponding root is sent negative.  A minimum in a
double coset therefore sends the two indicated simple systems to positive
roots.  The root-theoretic part of the Kilmoyer argument then says that a
positive simple root whose reflection lies in the opposite standard
parabolic must itself be one of its simple roots.  Consequently a
distinguished representative conjugating two standard parabolics transports
their simple-root subsets (and hence their Dynkin type) exactly.

This module uses only the finite reduced crystallographic root-system and
word-length APIs.  It deliberately makes no assertion that a pure Weyl
normalizer of a standard parabolic equals that parabolic: diagram symmetries
can enlarge the normalizer.
-/

open Set
open Submodule
open scoped Pointwise

namespace Theory.AlgebraicGroup

variable {ι M N : Type*} [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]

section Length

omit [P.IsRootSystem] in
private lemma wordLength_inv (b : P.Base) (g : P.weylGroup) :
    b.wordLength g⁻¹ = b.wordLength g := by
  apply Nat.le_antisymm
  · rcases b.wordLength_spec g with ⟨l, hlen, hprod⟩
    have hprodInv : b.wordProd l.reverse = g⁻¹ := by
      rw [b.wordProd_reverse, hprod]
    have hle := b.wordLength_le g⁻¹ l.reverse hprodInv
    simpa [List.length_reverse, hlen] using hle
  · rcases b.wordLength_spec g⁻¹ with ⟨l, hlen, hprod⟩
    have hprodInv : b.wordProd l.reverse = g := by
      rw [b.wordProd_reverse, hprod, inv_inv]
    have hle := b.wordLength_le g l.reverse hprodInv
    simpa [List.length_reverse, hlen] using hle

omit [P.IsRootSystem] in
private lemma left_step_of_not_pos (b : P.Base) (w : P.weylGroup)
    (j : b.support) (hneg : ¬ b.IsPos (P.weylGroupToPerm w⁻¹ j)) :
    b.wordLength (b.simpleReflection j * w) + 1 = b.wordLength w := by
  have hdec := b.wordLength_mul_simpleReflection_of_not_isPos w⁻¹ j hneg
  rw [show w⁻¹ * b.simpleReflection j = (b.simpleReflection j * w)⁻¹ by simp] at hdec
  rw [wordLength_inv (b := b) (b.simpleReflection j * w),
    wordLength_inv (b := b) w] at hdec
  exact hdec

end Length

section DoubleCosets

/-- A minimum-length element in the `(J,K)` double coset of `w`. -/
public noncomputable def IsMinimalDoubleCoset
    (b : P.Base) (J K : Set b.support) (w : P.weylGroup) : Prop :=
  ∀ x ∈ DoubleCoset.doubleCoset w
      (b.parabolicSubgroup J : Set P.weylGroup)
      (b.parabolicSubgroup K : Set P.weylGroup),
    b.wordLength w ≤ b.wordLength x

/-- Distinguished elements: both the left `J` and right `K` simple roots stay
positive. -/
public noncomputable def IsDistinguishedDoubleCoset
    (b : P.Base) (J K : Set b.support) (w : P.weylGroup) : Prop :=
  (∀ j ∈ J, b.IsPos (P.weylGroupToPerm w⁻¹ j)) ∧
  (∀ k ∈ K, b.IsPos (P.weylGroupToPerm w k))

omit [P.IsRootSystem] in
public theorem isMinimalDoubleCoset_isDistinguished
    (b : P.Base) (J K : Set b.support) (w : P.weylGroup)
    (hmin : IsMinimalDoubleCoset b J K w) :
    IsDistinguishedDoubleCoset b J K w := by
  constructor
  · intro j hj
    by_contra hneg
    have hmem : b.simpleReflection j * w ∈
        DoubleCoset.doubleCoset w
          (b.parabolicSubgroup J : Set P.weylGroup)
          (b.parabolicSubgroup K : Set P.weylGroup) := by
      apply DoubleCoset.mem_doubleCoset.mpr
      exact ⟨b.simpleReflection j,
        Subgroup.subset_closure ⟨j, hj, rfl⟩,
        1, (b.parabolicSubgroup K).one_mem, by simp⟩
    have hle := hmin _ hmem
    have hdec := left_step_of_not_pos b w j hneg
    omega
  · intro k hk
    by_contra hneg
    have hmem : w * b.simpleReflection k ∈
        DoubleCoset.doubleCoset w
          (b.parabolicSubgroup J : Set P.weylGroup)
          (b.parabolicSubgroup K : Set P.weylGroup) := by
      apply DoubleCoset.mem_doubleCoset.mpr
      exact ⟨1, (b.parabolicSubgroup J).one_mem,
        b.simpleReflection k, Subgroup.subset_closure ⟨k, hk, rfl⟩, by simp⟩
    have hle := hmin _ hmem
    have hdec := b.wordLength_mul_simpleReflection_of_not_isPos w k hneg
    omega

public theorem exists_minimalDoubleCoset
    (b : P.Base) (J K : Set b.support) (w : P.weylGroup) :
    ∃ v ∈ DoubleCoset.doubleCoset w
        (b.parabolicSubgroup J : Set P.weylGroup)
        (b.parabolicSubgroup K : Set P.weylGroup),
      IsMinimalDoubleCoset b J K v ∧
      IsDistinguishedDoubleCoset b J K v := by
  classical
  let S : Set P.weylGroup := DoubleCoset.doubleCoset w
    (b.parabolicSubgroup J : Set P.weylGroup)
    (b.parabolicSubgroup K : Set P.weylGroup)
  have hS : S.Nonempty := by
    exact ⟨w, DoubleCoset.mem_doubleCoset_self
      (b.parabolicSubgroup J) (b.parabolicSubgroup K) w⟩
  let _ : Finite P.weylGroup := weylGroup_finite P
  have hSf : S.Finite := Set.finite_univ.subset (Set.subset_univ _)
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S b.wordLength hSf hS
  have hcoset := DoubleCoset.doubleCoset_eq_of_mem
    (H := b.parabolicSubgroup J) (K := b.parabolicSubgroup K) hv
  have hvm : IsMinimalDoubleCoset b J K v := by
    rw [IsMinimalDoubleCoset, hcoset]
    simpa [S] using hmin
  exact ⟨v, hv, hvm, isMinimalDoubleCoset_isDistinguished b J K v hvm⟩

end DoubleCosets

section RootRigidity

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private lemma span_of_neg_action
    (b : P.Base) (J : Set b.support) (x : P.weylGroup)
    (hx : x ∈ b.parabolicSubgroup J) {i : ι} (hi : b.IsPos i)
    (hneg : ¬ b.IsPos (P.weylGroupToPerm x i)) :
    P.root i ∈ Submodule.span ℝ
      (P.root '' ((fun j : b.support => (j : ι)) '' J)) := by
  by_contra hspan
  rcases (b.mem_parabolicSubgroup_iff_exists_word J x).1 hx with
    ⟨l, hlJ, hlprod⟩
  have hpos := b.wordProd_root_isPos_of_external J l hlJ i hi hspan
  rw [hlprod] at hpos
  exact hneg hpos

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private lemma pos_add_span_left
    (b : P.Base) (J : Set b.support)
    {i j k : ι} (hi : b.IsPos i) (hj : b.IsPos j)
    (hijk : P.root k = P.root i + P.root j)
    (hspan : P.root k ∈ Submodule.span ℝ
      (P.root '' ((fun t : b.support => (t : ι)) '' J))) :
    P.root i ∈ Submodule.span ℝ
      (P.root '' ((fun t : b.support => (t : ι)) '' J)) := by
  apply (b.mem_span_root_image_iff_repr_support_subset J (P.root i)).2
  intro t ht
  by_contra htJ
  have hcoord := (b.mem_span_root_image_iff_repr_support_subset J (P.root k)).1 hspan
  have hkzero : b.toWeightBasis.repr (P.root k) t = 0 := by
    apply not_ne_iff.mp
    intro hne
    exact htJ (hcoord (Finsupp.mem_support_iff.mpr hne))
  have hsum := congrArg (fun x => b.toWeightBasis.repr x t) hijk
  rw [map_add, Finsupp.add_apply] at hsum
  have hsum' : 0 = b.toWeightBasis.repr (P.root i) t +
      b.toWeightBasis.repr (P.root j) t := by
    linarith [hsum, hkzero]
  have hnoni := b.isPos_repr_nonneg i hi t
  have hnonj := b.isPos_repr_nonneg j hj t
  have hi0 : b.toWeightBasis.repr (P.root i) t = 0 := by linarith [hsum']
  exact (Finsupp.mem_support_iff.mp ht) hi0

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private lemma pos_span_inv_pos
    (b : P.Base) (J : Set b.support) (w : P.weylGroup)
    (hleft : ∀ j ∈ J, b.IsPos (P.weylGroupToPerm w⁻¹ j))
    {i : ι} (hi : b.IsPos i)
    (hspan : P.root i ∈ Submodule.span ℝ
      (P.root '' ((fun j : b.support => (j : ι)) '' J))) :
    b.IsPos (P.weylGroupToPerm w⁻¹ i) := by
  apply (b.isPos_iff_root_mem_closure _).2
  let S : AddSubmonoid M := AddSubmonoid.closure
      (P.root '' ((fun j : b.support => (j : ι)) '' J))
  have hcl : P.root i ∈ S := b.closure_mem_span_root_image_of_mem_span J
    (P.root i) ((b.isPos_iff_root_mem_closure i).mp hi) hspan
  have hmap : ∀ x : M, x ∈ S →
      w⁻¹ • x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι)) := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
        rcases hx with ⟨j, hjJ, hroot⟩
        rcases hjJ with ⟨jJ, hjJ, hval⟩
        subst j
        rw [← hroot]
        change w⁻¹ • P.root (jJ : ι) ∈ _
        have hact := P.weylGroup_apply_root (w⁻¹) (jJ : ι)
        rw [hact]
        exact (b.isPos_iff_root_mem_closure _).mp (hleft jJ hjJ)
    | zero => simp
    | add x y hx hy ihx ihy =>
        simpa [smul_add] using AddSubmonoid.add_mem _ ihx ihy
  have hm := hmap (P.root i) hcl
  rw [P.weylGroup_apply_root] at hm
  exact hm

omit [P.IsReduced] in
private lemma positive_span_simple_of_preimage_simple
    (b : P.Base) (J : Set b.support) (w : P.weylGroup)
    (hleft : ∀ j ∈ J, b.IsPos (P.weylGroupToPerm w⁻¹ j))
    {k : b.support} (hrpos : b.IsPos (P.weylGroupToPerm w k))
    (hrspan : P.root (P.weylGroupToPerm w k) ∈ b.parabolicRootSpan J) :
    ∃ j ∈ J,
      P.root (P.weylGroupToPerm w k) = P.root (j : ι) := by
  let r : ι := P.weylGroupToPerm w k
  change P.root r ∈ Submodule.span ℝ
    (P.root '' ((fun j : b.support => (j : ι)) '' J)) at hrspan
  have hpre : b.IsPos (P.weylGroupToPerm w⁻¹ r) := by
    apply pos_span_inv_pos b J w hleft hrpos
    simpa [r] using hrspan
  have hkroot : P.root (P.weylGroupToPerm w⁻¹ r) = P.root (k : ι) := by
    calc
      P.root (P.weylGroupToPerm w⁻¹ r) = w⁻¹ • P.root r :=
        (P.weylGroup_apply_root w⁻¹ r).symm
      _ = w⁻¹ • (w • P.root (k : ι)) := by
        congr 1
        exact (P.weylGroup_apply_root w (k : ι)).symm.trans (by simp)
      _ = P.root (k : ι) := by simp
  have hkindecomp : b.toPositiveSubsystem.IsIndecomposable (k : ι) :=
    (base_mem_support_iff_isIndecomposablePositive b (k : ι)).1 k.property
  by_contra hnot
  have hsimple : ¬ r ∈ b.support := by
    intro hrs
    have hrcoord := (b.mem_span_root_image_iff_repr_support_subset J (P.root r)).1 hrspan
    have hrself : (⟨r, hrs⟩ : b.support) ∈
        (b.toWeightBasis.repr (P.root r)).support := by
      rw [show P.root r = P.root (⟨r, hrs⟩ : b.support) by rfl,
        b.toWeightBasis_repr_root]
      simp
    exact hnot ⟨⟨r, hrs⟩, hrcoord hrself, rfl⟩
  have hnotind : ¬ b.toPositiveSubsystem.IsIndecomposable r := by
    intro hind
    exact hsimple ((base_mem_support_iff_isIndecomposablePositive b r).2 hind)
  have hdecomp : ∃ a c, b.IsPos a ∧ b.IsPos c ∧
      P.root r = P.root a + P.root c := by
    apply Classical.byContradiction
    intro hno
    apply hnotind
    rw [RootPairing.PositiveSubsystem.isIndecomposable_iff]
    exact ⟨by simpa only [RootPairing.Base.mem_toPositiveSubsystem] using hrpos,
      by simpa only [RootPairing.Base.mem_toPositiveSubsystem] using hno⟩
  rcases hdecomp with ⟨a, c, ha, hc, hac⟩
  have ha_span := pos_add_span_left b J ha hc hac hrspan
  have hc_span := pos_add_span_left b J hc ha (by simpa [r, add_comm] using hac) hrspan
  have ha' := pos_span_inv_pos b J w hleft ha ha_span
  have hc' := pos_span_inv_pos b J w hleft hc hc_span
  rw [RootPairing.PositiveSubsystem.isIndecomposable_iff] at hkindecomp
  apply hkindecomp.2
  refine ⟨P.weylGroupToPerm w⁻¹ a, P.weylGroupToPerm w⁻¹ c,
    by simpa only [RootPairing.Base.mem_toPositiveSubsystem] using ha',
    by simpa only [RootPairing.Base.mem_toPositiveSubsystem] using hc', ?_⟩
  calc
    P.root (k : ι) = P.root (P.weylGroupToPerm w⁻¹ r) := hkroot.symm
    _ = w⁻¹ • P.root r := (P.weylGroup_apply_root w⁻¹ r).symm
    _ = w⁻¹ • (P.root a + P.root c) := by rw [hac]
    _ = P.root (P.weylGroupToPerm w⁻¹ a) +
        P.root (P.weylGroupToPerm w⁻¹ c) := by
      rw [smul_add, P.weylGroup_apply_root, P.weylGroup_apply_root]

omit [P.IsReduced] in
private lemma simple_image_of_parabolic_mem
    (b : P.Base) (J : Set b.support) (w : P.weylGroup)
    (hleft : ∀ j ∈ J, b.IsPos (P.weylGroupToPerm w⁻¹ j))
    {k : b.support} (hrpos : b.IsPos (P.weylGroupToPerm w k))
    (hx : w * b.simpleReflection k * w⁻¹ ∈ b.parabolicSubgroup J) :
    ∃ j ∈ J, P.root (P.weylGroupToPerm w k) = P.root (j : ι) := by
  let := P.indexNeg
  have hneg : ¬ b.IsPos (P.weylGroupToPerm
      (w * b.simpleReflection k * w⁻¹) (P.weylGroupToPerm w k)) := by
    have hroot : P.root (P.weylGroupToPerm
        (w * b.simpleReflection k * w⁻¹) (P.weylGroupToPerm w k)) =
          - P.root (P.weylGroupToPerm w k) := by
      calc
        P.root (P.weylGroupToPerm (w * b.simpleReflection k * w⁻¹)
            (P.weylGroupToPerm w k)) =
            (w * b.simpleReflection k * w⁻¹) •
              P.root (P.weylGroupToPerm w k) :=
          (P.weylGroup_apply_root _ _).symm
        _ = (w * b.simpleReflection k * w⁻¹) •
              (w • P.root (k : ι)) := by
          exact congrArg (fun x : M =>
            (w * b.simpleReflection k * w⁻¹) • x)
            (P.weylGroup_apply_root w (k : ι)).symm
        _ = w • (b.simpleReflection k •
            (w⁻¹ • (w • P.root (k : ι)))) := by
          rw [mul_smul, mul_smul]
        _ = w • (b.simpleReflection k • P.root (k : ι)) := by
          rw [inv_smul_smul]
        _ = w • (-P.root (k : ι)) := by
          congr 1
          change P.reflection (k : ι) (P.root (k : ι)) = _
          rw [P.reflection_apply_self]
        _ = -(w • P.root (k : ι)) := by rw [smul_neg]
        _ = -P.root (P.weylGroupToPerm w k) := by
          rw [P.weylGroup_apply_root]
    have hidx : P.weylGroupToPerm
        (w * b.simpleReflection k * w⁻¹) (P.weylGroupToPerm w k) =
          -(P.weylGroupToPerm w k) := by
      apply P.root.injective
      calc
        P.root (P.weylGroupToPerm
            (w * b.simpleReflection k * w⁻¹) (P.weylGroupToPerm w k)) =
            -P.root (P.weylGroupToPerm w k) := hroot
        _ = P.root (-(P.weylGroupToPerm w k)) := by
          symm
          change P.root (P.reflectionPerm (P.weylGroupToPerm w k)
            (P.weylGroupToPerm w k)) = _
          rw [P.root_reflectionPerm, P.reflection_apply_self]
    change ¬ b.IsPos (P.weylGroupToPerm
      (w * b.simpleReflection k * w⁻¹) (P.weylGroupToPerm w k))
    rw [hidx, RootPairing.Base.IsPos.neg_iff_not b]
    exact not_not_intro hrpos
  exact positive_span_simple_of_preimage_simple b J w hleft hrpos
    (span_of_neg_action b J (w * b.simpleReflection k * w⁻¹) hx
      hrpos hneg)

omit [P.IsReduced] in
public theorem distinguished_simple_root_image
    (b : P.Base) (J K : Set b.support) (w : P.weylGroup)
    (hD : IsDistinguishedDoubleCoset b J K w)
    (hconj : (b.parabolicSubgroup K).conjBy w = b.parabolicSubgroup J) :
    ∀ k ∈ K, ∃ j ∈ J,
      P.root (P.weylGroupToPerm w k) = P.root (j : ι) := by
  intro k hk
  apply simple_image_of_parabolic_mem b J w hD.1 (hD.2 k hk)
  have hm : b.simpleReflection k ∈ b.parabolicSubgroup K :=
    Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hmap : w * b.simpleReflection k * w⁻¹ ∈
      (b.parabolicSubgroup K).conjBy w := by
    exact Subgroup.mem_map.mpr ⟨b.simpleReflection k, hm, by
      simp [MulAut.conj_apply, mul_assoc]⟩
  rw [hconj] at hmap
  exact hmap

omit [P.IsReduced] in
public theorem distinguished_standardParabolic_simple_root_rigidity
    (b : P.Base) (J K : Set b.support) (w : P.weylGroup)
    (hD : IsDistinguishedDoubleCoset b J K w)
    (hconj : (b.parabolicSubgroup K).conjBy w = b.parabolicSubgroup J) :
    (∀ k ∈ K, ∃ j ∈ J,
      P.root (P.weylGroupToPerm w k) = P.root (j : ι)) ∧
    (∀ j ∈ J, ∃ k ∈ K,
      P.root (P.weylGroupToPerm w⁻¹ j) = P.root (k : ι)) := by
  refine ⟨distinguished_simple_root_image b J K w hD hconj, ?_⟩
  have hDinv : IsDistinguishedDoubleCoset b K J w⁻¹ :=
    ⟨hD.2, hD.1⟩
  have hconjinv : (b.parabolicSubgroup J).conjBy w⁻¹ =
      b.parabolicSubgroup K := by
    rw [← hconj, Subgroup.conjBy_inv]
  exact distinguished_simple_root_image b K J w⁻¹ hDinv hconjinv

omit [P.IsReduced] in
public theorem distinguished_standardParabolic_support_image_eq
    (b : P.Base) (J K : Set b.support) (w : P.weylGroup)
    (hD : IsDistinguishedDoubleCoset b J K w)
    (hconj : (b.parabolicSubgroup K).conjBy w = b.parabolicSubgroup J) :
    P.weylGroupToPerm w '' ((fun k : b.support => (k : ι)) '' K) =
      ((fun j : b.support => (j : ι)) '' J) := by
  ext i
  constructor
  · rintro ⟨k, ⟨kK, hkK, hkval⟩, hival⟩
    rcases (distinguished_simple_root_image b J K w hD hconj kK hkK) with
      ⟨j, hj, hroot⟩
    have hidx : P.weylGroupToPerm w (kK : ι) = (j : ι) :=
      P.root.injective hroot
    refine ⟨j, hj, ?_⟩
    exact hival ▸ (hkval ▸ hidx.symm)
  · rintro ⟨j, hj, hival⟩
    rcases (distinguished_standardParabolic_simple_root_rigidity b J K w hD hconj).2
      j hj with ⟨k, hk, hroot⟩
    have hidx : P.weylGroupToPerm w⁻¹ (j : ι) = (k : ι) :=
      P.root.injective hroot
    refine ⟨P.weylGroupToPerm w⁻¹ (j : ι), ⟨k, hk, hidx.symm⟩, ?_⟩
    rw [← hival]
    simp

omit [P.IsReduced] in
public theorem distinguished_standardParabolic_normalizer_support_eq
    (b : P.Base) (J : Set b.support) (w : P.weylGroup)
    (hD : IsDistinguishedDoubleCoset b J J w)
    (hconj : (b.parabolicSubgroup J).conjBy w = b.parabolicSubgroup J) :
    P.weylGroupToPerm w '' ((fun j : b.support => (j : ι)) '' J) =
      ((fun j : b.support => (j : ι)) '' J) :=
  distinguished_standardParabolic_support_image_eq b J J w hD hconj

end RootRigidity

end Theory.AlgebraicGroup
