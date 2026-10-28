module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.PointStabilizer
public import Theory.Mathieu.M24.ChapterHStabilizers.PairInvolutions
public import Theory.Mathieu.M22.Properties.OuterCentralizers.DesignAction
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.PairResidual.Displacement
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.Quasithin.EvenCharacteristic

/-!
# Outer M22 involutions with eight fixed design points

A design automorphism of M22 corresponds to an M24 permutation preserving the
marked pair. If the automorphism is outer, the permutation swaps the pair; its
M22 centralizer is therefore the stabilizer of either marked point in the M24
centralizer. Eight fixed design points force the M24 involution into class 2A.
The moved-point stabilizer of a 2A centralizer has self-centralizing two-core,
which excludes ordinary components of the M22 centralizer.

This is the fixed-octad case used in Aschbacher–Smith 16.1.5(5), printed
p.1171 of `refs/quasithin.pdf`.
-/

public section


open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M24ChapterHStabilizers
open MathieuCode
open scoped Pointwise

namespace Sporadic.Mathieu.M22OuterCentralizers

private theorem pair_coordinate_action (g : MathieuCode.m22PairStabilizer) (s : m22DesignAut)
    (he : m22PairStabilizerEquivAut g = m22DesignAutToAut s) (i : Fin 22) :
    g.val • m22Coordinates i = m22Coordinates (s.val i) := by
  have hn : g.val • m22Coordinates i ∉ MathieuCode.m22Pair := by
    intro h
    have hp := (MulAction.mem_stabilizer_finset.mp g.property (m22Coordinates i)).mp h
    exact (by decide +kernel : ∀ i : Fin 22, m22Coordinates i ∉ MathieuCode.m22Pair) i hp
  obtain h0 | h9 | ⟨j, hj⟩ := pairResidual_coordinates_cover (g.val • m22Coordinates i)
  · exact (hn (by simp [h0, MathieuCode.m22Pair])).elim
  · exact (hn (by simp [h9, MathieuCode.m22Pair])).elim
  rw [← hj]
  congr 1
  by_contra hji
  have hpre : s.val⁻¹ j ≠ i := by
    intro h
    exact hji (by simpa using congrArg s.val h)
  obtain ⟨l, hli, hlpre⟩ := Fin.exists_ne_and_ne_of_two_lt i (s.val⁻¹ j) (by decide)
  obtain ⟨k, hki, hkp⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    hpre.symm hli.symm
  have hc := m22PairStabilizerEquivAut_apply g k
  rw [he] at hc
  have hm := (eq_mul_inv_iff_mul_eq.mp hc)
  have hh := congrArg (fun x : M24 => x • m22Coordinates i) hm
  have hact (a : M22) (b : Fin 22) :
      m22Embedding a • m22Coordinates b = m22Coordinates (a • b) := m22Embedding_apply a b
  simp only [mul_smul, hact, hki, ← hj] at hh
  have hjfix : m22DesignAutToAut s k • j = j := m22Coordinates.injective hh
  change (m22DesignAutToAut s k).val j = j at hjfix
  rw [m22DesignAutToAut_apply_perm] at hjfix
  change s.val (k.val (s.val⁻¹ j)) = j at hjfix
  have hfix : k • (s.val⁻¹ j) = s.val⁻¹ j := by
    change k.val (s.val⁻¹ j) = s.val⁻¹ j
    apply s.val.injective
    simpa using hjfix
  exact hlpre (hkp.symm.trans hfix)

private theorem fixedPoints_eq_reduced (g : MathieuCode.m22PairStabilizer) (s : m22DesignAut)
    (he : m22PairStabilizerEquivAut g = m22DesignAutToAut s) :
    fixedPoints s = reducedFixedPoints g := by
  ext i
  rw [mem_fixedPoints, mem_reducedFixedPoints, pair_coordinate_action g s he,
    m22Coordinates.injective.eq_iff]

private noncomputable def pairCentralizerMap (x : MathieuCode.m22PairStabilizer)
    (s : m22DesignAut) (he : m22PairStabilizerEquivAut x = m22DesignAutToAut s) :
    centralizer s →* MulAction.stabilizer (Subgroup.centralizer ({x.val} : Set M24))
      (0 : Fin 24) where
  toFun g := ⟨⟨m22Embedding g.val, by
    apply mem_centralizer_singleton_iff.mpr
    have hg : m22DesignAutToAut s g.val = g.val :=
      (MulAut.mem_fixedSubgroup _ _).mp g.property
    have hc := m22PairStabilizerEquivAut_apply x g.val
    rw [he, hg] at hc
    exact eq_mul_inv_iff_mul_eq.mp hc⟩, m22Embedding_fixed_zero g.val⟩
  map_one' := Subtype.ext (Subtype.ext (map_one m22Embedding))
  map_mul' _ _ := Subtype.ext (Subtype.ext (map_mul m22Embedding _ _))

private theorem pairCentralizerMap_bijective (x : MathieuCode.m22PairStabilizer)
    (s : m22DesignAut) (he : m22PairStabilizerEquivAut x = m22DesignAutToAut s)
    (ho : x.val ∉ m22PointwisePairStabilizer) :
    Function.Bijective (pairCentralizerMap x s he) := by
  constructor
  · intro g h hgh
    exact Subtype.ext (m22Embedding_injective (congrArg (fun a => a.val.val) hgh))
  · intro g
    have hc : g.val.val * x.val = x.val * g.val.val :=
      mem_centralizer_singleton_iff.mp g.val.property
    have hswap := (outer_pair_iff_swaps x).mp ho
    have h9 : g.val.val • (9 : Fin 24) = 9 := by
      have h := congrArg (fun z : M24 => z • (0 : Fin 24)) hc
      simpa only [mul_smul, hswap.1, show g.val.val • (0 : Fin 24) = 0 from g.property] using h
    have hmem : g.val.val ∈ m22Embedding.range := by
      rw [m22Embedding_range]
      exact ⟨g.property, h9⟩
    obtain ⟨k, hk⟩ := hmem
    have hfix : k ∈ centralizer s := by
      rw [centralizer, MulAut.mem_fixedSubgroup]
      apply m22Embedding_injective
      rw [← he, m22PairStabilizerEquivAut_apply, hk, ← hc, mul_inv_cancel_right]
    exact ⟨⟨k, hfix⟩, Subtype.ext (Subtype.ext hk)⟩

end Sporadic.Mathieu.M22OuterCentralizers

namespace Sporadic.Mathieu.M22OuterCentralizers

theorem eight_fixed_twoCore (s : m22DesignAut) (hs : orderOf s = 2)
    (ho : s.val ∉ M22) (h8 : (fixedPoints s).card = 8) :
    Subgroup.centralizer (pCore 2 (centralizer s) : Set (centralizer s)) ≤
      pCore 2 (centralizer s) := by
  let x := m22PairStabilizerEquivAut.symm (m22DesignAutToAut s)
  have he : m22PairStabilizerEquivAut x = m22DesignAutToAut s :=
    m22PairStabilizerEquivAut.apply_symm_apply _
  have hx : orderOf x = 2 := (m22PairStabilizerEquivAut.symm.orderOf_eq _).trans
    ((orderOf_injective m22DesignAutToAut m22DesignAutToAut_injective s).trans hs)
  have houter : x.val ∉ m22PointwisePairStabilizer := by
    intro hm
    obtain ⟨g, hg⟩ := (pair_inner_iff x).mpr hm
    apply ho
    exact (induced_inner_iff s).mp ⟨g, he.symm.trans hg⟩
  have hcard : (M24ChapterHStabilizers.fixedPoints x.val).card = 8 := by
    rw [← reducedFixedPoints_image x houter,
      Finset.card_image_of_injective _ m22Coordinates.injective,
      ← fixedPoints_eq_reduced x s he]
    exact h8
  have hclass : IsConj M24InvolutionCentralizers.involution2A x.val := by
    rcases M24InvolutionCentralizers.involution_classes x.val
      ((Subgroup.orderOf_coe x).trans hx) with hA | hB
    · exact hA
    · rw [class2B_fixed_empty hB, Finset.card_empty] at hcard
      omega
  have hmove : x.val • (0 : Fin 24) ≠ 0 := by
    rw [(outer_pair_iff_swaps x).mp houter |>.1]
    decide
  let e := MulEquiv.ofBijective (pairCentralizerMap x s he)
    (pairCentralizerMap_bijective x s he houter)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
    (M24InvolutionCentralizers.pointed_twoCore_of_class2A x.val hclass 0 hmove)

theorem eight_fixed_no_component (s : m22DesignAut) (hs : orderOf s = 2)
    (ho : s.val ∉ M22) (h8 : (fixedPoints s).card = 8)
    (B : Subgroup (centralizer s)) : ¬ Theory.GroupTheory.IsComponent (centralizer s) B :=
  Theory.GroupTheory.not_isComponent_of_twoCore (eight_fixed_twoCore s hs ho h8) B

end Sporadic.Mathieu.M22OuterCentralizers
