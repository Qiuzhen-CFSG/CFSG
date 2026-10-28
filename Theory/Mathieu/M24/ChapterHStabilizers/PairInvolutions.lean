module

public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions
public import Theory.Mathieu.M24.ChapterHStabilizers.PairCertificates
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# The two outer involution classes of the native M22 extension

The setwise stabilizer of {0,9} in M24 is the proved automorphism group of
native M22. Its inner subgroup fixes the pair pointwise; every outer element
exchanges its two points. For an outer involution an ambient M24 conjugator
can therefore be corrected by a centralizer element so as to fix the pair
pointwise. The checked centralizer transport words give exactly two outer
classes. Their fixed sets distinguish them: an octad disjoint from {0,9}, or
the empty set. Restriction through the original 22-point coordinate embedding
retains exactly those fixed points.

The actual pair-to-automorphism equivalence transfers coverage, the order-two
assertion, outer status and class separation to `MulAut M22`. No action on a
code or cocode module is used or asserted.

Source: Aschbacher–Smith H.14.4(4), printed p.398 (PDF p.409).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Sporadic.Mathieu.M24InvolutionCentralizers
open scoped Pointwise
namespace Sporadic.Mathieu.M24ChapterHStabilizers
open MathieuCode PairCertificates FusionData

private theorem mem_pair_of_swaps {g : M24}
    (h0 : g • (0 : Fin 24) = 9) (h9 : g • (9 : Fin 24) = 0) :
    g ∈ MathieuCode.m22PairStabilizer := by
  apply MulAction.mem_stabilizer_finset'.mpr
  intro i hi
  have hi' : i = 0 ∨ i = 9 := by simpa [m22Pair] using hi
  rcases hi' with rfl | rfl
  · rw [h0]; simp [m22Pair]
  · rw [h9]; simp [m22Pair]

/-- Outside the native M22, the setwise pair stabilizer interchanges its two points. -/
theorem outer_pair_iff_swaps (g : MathieuCode.m22PairStabilizer) :
    g.val ∉ m22PointwisePairStabilizer ↔
      g.val • (0 : Fin 24) = 9 ∧ g.val • (9 : Fin 24) = 0 := by
  have h0 : g.val • (0 : Fin 24) = 0 ∨ g.val • (0 : Fin 24) = 9 := by
    have h := MulAction.mem_stabilizer_finset'.mp g.property (by simp [m22Pair] : 0 ∈ m22Pair)
    simpa [m22Pair] using h
  have h9 : g.val • (9 : Fin 24) = 0 ∨ g.val • (9 : Fin 24) = 9 := by
    have h := MulAction.mem_stabilizer_finset'.mp g.property (by simp [m22Pair] : 9 ∈ m22Pair)
    simpa [m22Pair] using h
  have hinj : Function.Injective (fun i : Fin 24 => g.val • i) := g.val.val.injective
  constructor
  · intro hn
    rcases h0 with h0 | h0
    · rcases h9 with h9 | h9
      · exact (show (9 : Fin 24) ≠ 0 by decide) (hinj (h9.trans h0.symm)) |>.elim
      · exact (hn ⟨h0, h9⟩).elim
    · refine ⟨h0, ?_⟩
      rcases h9 with h9 | h9
      · exact h9
      · exact (show (9 : Fin 24) ≠ 0 by decide) (hinj (h9.trans h0.symm)) |>.elim
  · rintro ⟨h0, _⟩ hp
    have he : g.val • (0 : Fin 24) = 0 := hp.1
    exact (show (9 : Fin 24) ≠ 0 by decide) (h0.symm.trans he)

/-- The actual pair equivalence detects precisely the inner automorphisms. -/
theorem pair_inner_iff (g : MathieuCode.m22PairStabilizer) :
    (∃ k : M22, m22PairStabilizerEquivAut g = MulAut.conj k) ↔
      g.val ∈ m22PointwisePairStabilizer := by
  constructor
  · rintro ⟨k, hk⟩
    have he : g = m22ToPairStabilizer k := m22PairStabilizerEquivAut.injective
      (hk.trans (m22PairStabilizerEquivAut_inner k).symm)
    rw [he]
    exact ⟨m22Embedding_fixed_zero k, m22Embedding_fixed_nine k⟩
  · intro hg
    rw [← m22Embedding_range] at hg
    obtain ⟨k, hk⟩ := hg
    have he : g = m22ToPairStabilizer k := Subtype.ext hk.symm
    exact ⟨k, he ▸ m22PairStabilizerEquivAut_inner k⟩

private theorem base_order (a : Bool) : orderOf (base a) = 2 := by
  cases a
  · exact involution2B_order
  · exact involution2A_order

private theorem marked_swaps (a : Bool) :
    (MulAut.conj (marking a) (base a)) • (0 : Fin 24) = 9 ∧
    (MulAut.conj (marking a) (base a)) • (9 : Fin 24) = 0 := by
  have h0 : (marking a) • baseMoved a = (0 : Fin 24) := (marking_apply a).1
  have h9 : (marking a) • ((base a) • baseMoved a) = (9 : Fin 24) := (marking_apply a).2
  have hs : base a * base a = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp (base_order a)).1
  constructor
  · rw [← h0, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul]
    exact h9
  · rw [← h9, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul,
      ← mul_smul (base a), hs, one_smul]
    exact h0

/-- Representatives of the two outer classes, on the native marked pair. -/
noncomputable def pairRepresentative (a : Bool) : MathieuCode.m22PairStabilizer :=
  ⟨MulAut.conj (marking a) (base a), by
    exact mem_pair_of_swaps (marked_swaps a).1 (marked_swaps a).2⟩

theorem pairRepresentative_order (a : Bool) : orderOf (pairRepresentative a) = 2 :=
  (Subgroup.orderOf_coe _).symm.trans ((MulEquiv.orderOf_eq _ _).trans (base_order a))

theorem pairRepresentative_outer (a : Bool) :
    (pairRepresentative a).val ∉ m22PointwisePairStabilizer :=
  (outer_pair_iff_swaps _).mpr (marked_swaps a)

/-- Correcting an ambient conjugator by a centralizing word makes it fix the
marked pair pointwise. Thus fusion takes place inside the actual pair group. -/
theorem pair_fusion_of_ambient (a : Bool) (x : MathieuCode.m22PairStabilizer)
    (ho : x.val ∉ m22PointwisePairStabilizer) (hc : IsConj (base a) x.val) :
    IsConj (pairRepresentative a) x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hx := (outer_pair_iff_swaps x).mp ho
  have hcomm : g * base a = x.val * g := (mul_inv_eq_iff_eq_mul).mp hg
  have hmove : (base a).val (g⁻¹ • (0 : Fin 24)) ≠ g⁻¹ • (0 : Fin 24) := by
    intro h
    have he := congrArg (fun k : M24 => k • (g⁻¹ • (0 : Fin 24))) hcomm
    change g • ((base a) • (g⁻¹ • (0 : Fin 24))) = x.val • (g • (g⁻¹ • (0 : Fin 24))) at he
    rw [show (base a) • (g⁻¹ • (0 : Fin 24)) = g⁻¹ • (0 : Fin 24) from h,
      smul_inv_smul, hx.1] at he
    exact (show (0 : Fin 24) ≠ 9 by decide) he
  obtain ⟨c, hc, hcp⟩ := exists_centralizer_transport a (g⁻¹ • (0 : Fin 24)) hmove
  let k : M24 := g * c * (marking a)⁻¹
  have hk0 : k • (0 : Fin 24) = 0 := by
    conv_lhs => rw [show (0 : Fin 24) = (marking a) • baseMoved a from (marking_apply a).1.symm]
    change (g * c * (marking a)⁻¹) • ((marking a) • baseMoved a) = _
    rw [mul_smul, inv_smul_smul, mul_smul,
      show c • baseMoved a = g⁻¹ • (0 : Fin 24) from hcp, smul_inv_smul]
  have hkconj : k * (pairRepresentative a).val * k⁻¹ = x.val := by
    change (g * c * (marking a)⁻¹) *
      ((marking a) * base a * (marking a)⁻¹) * (g * c * (marking a)⁻¹)⁻¹ = x.val
    calc
      _ = g * (c * base a * c⁻¹) * g⁻¹ := by group
      _ = g * base a * g⁻¹ := by rw [hc]; group
      _ = x.val := hg
  have hk9 : k • (9 : Fin 24) = 9 := by
    have he := congrArg (fun z : M24 => z • (0 : Fin 24))
      ((mul_inv_eq_iff_eq_mul).mp hkconj)
    change k • ((pairRepresentative a).val • (0 : Fin 24)) = x.val • (k • (0 : Fin 24)) at he
    rw [show (pairRepresentative a).val • (0 : Fin 24) = 9 from (marked_swaps a).1, hk0, hx.1] at he
    exact he
  have hk : k ∈ MathieuCode.m22PairStabilizer := m22PointwisePairStabilizer_le ⟨hk0, hk9⟩
  exact isConj_iff.mpr ⟨⟨k, hk⟩, Subtype.ext hkconj⟩

/-- Exhaustive conjugacy coverage in the actual outer coset of the pair group. -/
theorem outer_pair_involution_classes (x : MathieuCode.m22PairStabilizer)
    (hx : orderOf x = 2) (ho : x.val ∉ m22PointwisePairStabilizer) :
    IsConj (pairRepresentative true) x ∨ IsConj (pairRepresentative false) x := by
  rcases involution_classes x.val ((Subgroup.orderOf_coe x).trans hx) with h | h
  · exact Or.inl (pair_fusion_of_ambient true x ho h)
  · exact Or.inr (pair_fusion_of_ambient false x ho h)

/-- The octad fixed by an outer involution avoids both deleted coordinates. -/
theorem outer_pair_fixed_octad_or_empty (x : MathieuCode.m22PairStabilizer)
    (hx : orderOf x = 2) (ho : x.val ∉ m22PointwisePairStabilizer) :
    (fixedPoints x.val ∈ m24Blocks ∧ Disjoint (fixedPoints x.val) m22Pair) ∨
      fixedPoints x.val = ∅ := by
  rcases involution_classes x.val ((Subgroup.orderOf_coe x).trans hx) with h | h
  · refine Or.inl ⟨class2A_fixed_octad h, ?_⟩
    apply Finset.disjoint_left.mpr
    intro i hi hp
    have hfix := (mem_fixedPoints _ _).mp hi
    have hswap := (outer_pair_iff_swaps x).mp ho
    have hp' : i = 0 ∨ i = 9 := by simpa [m22Pair] using hp
    rcases hp' with rfl | rfl
    · exact (show (9 : Fin 24) ≠ 0 by decide) (hswap.1.symm.trans hfix)
    · exact (show (0 : Fin 24) ≠ 9 by decide) (hswap.2.symm.trans hfix)
  · exact Or.inr (class2B_fixed_empty h)

/-- The representative with fixed points fixes a literal octad avoiding the pair. -/
theorem pairRepresentative_fixed_octad :
    fixedPoints (pairRepresentative true).val ∈ m24Blocks :=
  class2A_fixed_octad (isConj_iff.mpr ⟨marking true, rfl⟩)

theorem pairRepresentative_fixed_empty :
    fixedPoints (pairRepresentative false).val = ∅ :=
  class2B_fixed_empty (isConj_iff.mpr ⟨marking false, rfl⟩)

private theorem pair_fixed_card_conj (x y : MathieuCode.m22PairStabilizer)
    (h : IsConj x y) : (fixedPoints x.val).card = (fixedPoints y.val).card := by
  exact fixedPoints_card_eq_of_isConj (MathieuCode.m22PairStabilizer.subtype.map_isConj h)

/-- The two outer classes remain distinct inside the pair group. -/
theorem outer_pair_classes_disjoint :
    ¬ IsConj (pairRepresentative true) (pairRepresentative false) := by
  intro h
  have he := pair_fixed_card_conj _ _ h
  rw [m24Blocks_card _ pairRepresentative_fixed_octad,
    pairRepresentative_fixed_empty, Finset.card_empty] at he
  omega

/-- The two outer representatives in the actual automorphism group of native M22. -/
noncomputable def outerAutRepresentative (a : Bool) : MulAut M22 :=
  m22PairStabilizerEquivAut (pairRepresentative a)

theorem outerAutRepresentative_order (a : Bool) : orderOf (outerAutRepresentative a) = 2 :=
  (m22PairStabilizerEquivAut.orderOf_eq _).trans (pairRepresentative_order a)

theorem outerAutRepresentative_outer (a : Bool) :
    ¬ ∃ g : M22, outerAutRepresentative a = MulAut.conj g := by
  intro h
  exact pairRepresentative_outer a ((pair_inner_iff _).mp h)

/-- The abstract automorphism group has exactly these two outer involution classes. -/
theorem outer_aut_involution_classes (r : MulAut M22) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : M22, r = MulAut.conj g) :
    IsConj (outerAutRepresentative true) r ∨ IsConj (outerAutRepresentative false) r := by
  let x := m22PairStabilizerEquivAut.symm r
  have hx : orderOf x = 2 := (m22PairStabilizerEquivAut.symm.orderOf_eq _).trans hr
  have houter : x.val ∉ m22PointwisePairStabilizer := by
    intro h
    obtain ⟨g, hg⟩ := (pair_inner_iff x).mpr h
    exact ho ⟨g, (m22PairStabilizerEquivAut.apply_symm_apply r).symm.trans hg⟩
  have transfer (a : Bool) (h : IsConj (pairRepresentative a) x) :
      IsConj (outerAutRepresentative a) r := by
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    refine isConj_iff.mpr ⟨m22PairStabilizerEquivAut g, ?_⟩
    have he := congrArg m22PairStabilizerEquivAut hg
    simpa only [map_mul, map_inv, x, outerAutRepresentative, m22PairStabilizerEquivAut.apply_symm_apply] using he
  exact (outer_pair_involution_classes x hx houter).imp (transfer true) (transfer false)

theorem outer_aut_classes_disjoint :
    ¬ IsConj (outerAutRepresentative true) (outerAutRepresentative false) := by
  intro h
  apply outer_pair_classes_disjoint
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨m22PairStabilizerEquivAut.symm g, ?_⟩
  apply m22PairStabilizerEquivAut.injective
  simpa only [map_mul, map_inv, outerAutRepresentative, m22PairStabilizerEquivAut.apply_symm_apply] using hg

/-- Fixed points on the original 22 coordinates, retained through their native
embedding into the Witt design. -/
noncomputable def reducedFixedPoints (x : MathieuCode.m22PairStabilizer) : Finset (Fin 22) :=
  Finset.univ.filter (fun i => x.val • m22Coordinates i = m22Coordinates i)

@[simp] theorem mem_reducedFixedPoints (x : MathieuCode.m22PairStabilizer) (i : Fin 22) :
    i ∈ reducedFixedPoints x ↔ x.val • m22Coordinates i = m22Coordinates i := by
  simp [reducedFixedPoints]

private theorem coordinates_range : ∀ a : Fin 24,
    (∃ i : Fin 22, m22Coordinates i = a) ↔ a ≠ 0 ∧ a ≠ 9 := by decide +kernel

/-- Removing the exchanged pair removes no fixed point of an outer element. -/
theorem reducedFixedPoints_image (x : MathieuCode.m22PairStabilizer)
    (ho : x.val ∉ m22PointwisePairStabilizer) :
    (reducedFixedPoints x).image m22Coordinates = fixedPoints x.val := by
  ext a
  constructor
  · rintro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (mem_fixedPoints _ _).mpr ((mem_reducedFixedPoints _ _).mp hi)
  · intro ha
    have hf := (mem_fixedPoints _ _).mp ha
    have hs := (outer_pair_iff_swaps x).mp ho
    have h0 : a ≠ 0 := by
      rintro rfl
      exact (show (9 : Fin 24) ≠ 0 by decide) (hs.1.symm.trans hf)
    have h9 : a ≠ 9 := by
      rintro rfl
      exact (show (0 : Fin 24) ≠ 9 by decide) (hs.2.symm.trans hf)
    obtain ⟨i, rfl⟩ := (coordinates_range a).mpr ⟨h0, h9⟩
    exact Finset.mem_image.mpr ⟨i, (mem_reducedFixedPoints _ _).mpr hf, rfl⟩

/-- Each outer involution either fixes eight original coordinates whose image
is a Witt octad, or is fixed-point-free on the original degree-22 design. -/
theorem outer_pair_reduced_fixed_geometry (x : MathieuCode.m22PairStabilizer)
    (hx : orderOf x = 2) (ho : x.val ∉ m22PointwisePairStabilizer) :
    ((reducedFixedPoints x).image m22Coordinates ∈ m24Blocks ∧
      Disjoint ((reducedFixedPoints x).image m22Coordinates) m22Pair ∧
      (reducedFixedPoints x).card = 8) ∨ reducedFixedPoints x = ∅ := by
  rcases outer_pair_fixed_octad_or_empty x hx ho with ⟨hB, hd⟩ | he
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · rwa [reducedFixedPoints_image x ho]
    · rwa [reducedFixedPoints_image x ho]
    · have hc := m24Blocks_card _ hB
      rw [← reducedFixedPoints_image x ho,
        Finset.card_image_of_injective _ m22Coordinates.injective] at hc
      exact hc
  · apply Or.inr
    exact Finset.image_eq_empty.mp ((reducedFixedPoints_image x ho).trans he)

end Sporadic.Mathieu.M24ChapterHStabilizers
