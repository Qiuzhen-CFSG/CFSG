module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Words

/-!
# Small-subgroup fixed dimensions in native octad kernels

Every nonidentity octad-kernel element fixes seven dimensions of the literal
Golay quotient, and every order-four subgroup fixes four. Conjugacy reduces
to the native seed octad, whose kernel is exhausted by binary translations.
Checked word counts give Golay dimensions eight and five. Every subgroup here
fixes a coordinate, so the proved lifting theorem subtracts the constant line.
For the four-group case, two distinct nonidentity elements and their product
exhaust the subgroup; no normality or further module hypothesis is required.

Source: Aschbacher--Smith, H.16.2(4), printed pp.402--403, and H.16.8,
printed p.405. This concerns subgroups of the octad kernel, and keeps the
separate E16 called D in H.16.2(7) distinct.
-/

public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode
namespace SmallKernelFixed

private theorem seed_sq (g : M24) (hg : g ∈ octadPointwiseKernel seedOctad) : g ^ 2 = 1 := by
  obtain ⟨a, ha, rfl⟩ := hg
  exact congrArg (fun k : (action seedOctad).ker => k.val.val) (kernel_sq ⟨a, ha⟩)

private theorem four_generators (A : Subgroup M24) (hA : A ≤ octadPointwiseKernel seedOctad)
    (hc : Nat.card A = 4) :
    ∃ g h : A, g ≠ 1 ∧ h ≠ 1 ∧ g ≠ h ∧
      ∀ a : A, a = 1 ∨ a = g ∨ a = h ∨ a = g * h := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hc' : (Finset.univ : Finset A).card = 4 := by
    simpa only [Nat.card_eq_fintype_card, Finset.card_univ] using hc
  obtain ⟨g, _, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({1} : Finset A).card < Finset.univ.card by simp [hc'])
  have hg1 : g ≠ 1 := by simpa only [Finset.mem_singleton] using hg
  obtain ⟨h, _, hh⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({1, g} : Finset A).card < Finset.univ.card by simp [hc', hg1.symm])
  have hh1 : h ≠ 1 := fun he => hh (by simp [he])
  have hgh : g ≠ h := fun he => hh (by simp [← he])
  have hgg : g * g = 1 := by
    apply Subtype.ext
    change g.val * g.val = 1
    simpa only [pow_two] using seed_sq g.val (hA g.property)
  have hprod1 : g * h ≠ 1 := by
    intro he
    have he' := congrArg (fun a : A => g * a) he
    rw [← mul_assoc, hgg, one_mul, mul_one] at he'
    exact hgh he'.symm
  have hprodg : g * h ≠ g := by
    intro he
    exact hh1 (mul_left_cancel (he.trans (mul_one g).symm))
  have hprodh : g * h ≠ h := by
    intro he
    exact hg1 (mul_right_cancel (he.trans (one_mul h).symm))
  have hfour : ({1, g, h, g * h} : Finset A).card = 4 := by
    exact Finset.card_eq_four.mpr ⟨1, g, h, g * h, hg1.symm, hh1.symm, hprod1.symm,
      hgh, hprodg.symm, hprodh.symm, rfl⟩
  have hu : ({1, g, h, g * h} : Finset A) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [hc', hfour]
  refine ⟨g, h, hg1, hh1, hgh, ?_⟩
  intro a
  have ha := Finset.mem_univ a
  rw [← hu] at ha
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ha

private theorem code_dim_of_seed (A : Subgroup M24) (hA : A ≤ octadPointwiseKernel seedOctad)
    (d : Nat) (hd : Module.finrank (ZMod 2) (fixedSpace golayRepresentation A) = d + 1) :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation A) = d := by
  have h := finrank_fixedSpace_golay A (24 : Fin 24) (fun g hg =>
    (mem_octadPointwiseKernel _ _).mp (hA hg) _ ((mem_seedOctad _).mpr (Or.inl rfl)))
  omega

private theorem seed_element_finrank (g : M24) (hg : g ∈ octadPointwiseKernel seedOctad)
    (hne : g ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation (Subgroup.zpowers g)) = 7 := by
  obtain ⟨n, rfl⟩ := translation_surjective g hg
  have hn : n ≠ 0 := fun h => hne (by rw [h, translation_zero])
  exact code_dim_of_seed _ (Subgroup.zpowers_le.mpr (translation_mem n)) 7
    (golay_translation_finrank n hn)

private theorem seed_four_finrank (A : Subgroup M24) (hA : A ≤ octadPointwiseKernel seedOctad)
    (hc : Nat.card A = 4) : Module.finrank (ZMod 2) (fixedSpace codeRepresentation A) = 4 := by
  obtain ⟨g, h, hg, hh, hgh, hcover⟩ := four_generators A hA hc
  have hfix : fixedSpace golayRepresentation A =
      fixedSpace golayRepresentation (Subgroup.zpowers g.val) ⊓
        fixedSpace golayRepresentation (Subgroup.zpowers h.val) := by
    ext v
    constructor
    · intro hv
      exact ⟨(mem_fixedSpace_zpowers_iff _ _ _).mpr (hv g),
        (mem_fixedSpace_zpowers_iff _ _ _).mpr (hv h)⟩
    · rintro ⟨hv, hw⟩ a
      have hgv := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
      have hhv := (mem_fixedSpace_zpowers_iff _ _ _).mp hw
      rcases hcover a with rfl | rfl | rfl | rfl
      · change golayRepresentation 1 v = v
        simp
      · exact hgv
      · exact hhv
      · change golayRepresentation (g.val * h.val) v = v
        rw [map_mul, Module.End.mul_apply, hhv, hgv]
  obtain ⟨n, hn⟩ := translation_surjective g.val (hA g.property)
  obtain ⟨m, hm⟩ := translation_surjective h.val (hA h.property)
  have hn0 : n ≠ 0 := by
    intro he
    exact hg (Subtype.ext (by rw [← hn, he, translation_zero]; rfl))
  have hm0 : m ≠ 0 := by
    intro he
    exact hh (Subtype.ext (by rw [← hm, he, translation_zero]; rfl))
  have hnm : n ≠ m := by
    intro he
    exact hgh (Subtype.ext (hn.symm.trans ((congrArg translation he).trans hm)))
  apply code_dim_of_seed A hA 4
  rw [hfix, ← hn, ← hm]
  exact golay_pair_finrank n m hn0 hm0 hnm

end SmallKernelFixed

/-- Every nonidentity element of a native octad kernel fixes seven dimensions
of the literal eleven-dimensional Golay quotient. -/
theorem octad_kernel_involution_fixed_finrank (O : Octad) (g : M24)
    (hg : g ∈ octadPointwiseKernel O) (hne : g ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation (Subgroup.zpowers g)) = 7 := by
  obtain ⟨a, ha⟩ := exists_smul_octad_eq O seedOctad
  have hb : (MulAut.conj a) g ∈ octadPointwiseKernel seedOctad := by
    rw [← octad_kernel_map O seedOctad a ha]
    exact Subgroup.mem_map_of_mem _ hg
  have hbn : (MulAut.conj a) g ≠ 1 := by
    intro he
    apply hne
    exact (MulAut.conj a).injective (he.trans (map_one (MulAut.conj a)).symm)
  have hd := SmallKernelFixed.seed_element_finrank _ hb hbn
  have he := (fixedSpaceConjEquiv codeRepresentation (Subgroup.zpowers g) a).finrank_eq
  rw [MonoidHom.map_zpowers] at he
  exact he.trans hd

/-- Every subgroup of order four in a native octad kernel fixes exactly four
code dimensions. In particular this applies to the common kernel in H.16.2(4). -/
theorem octad_kernel_four_fixed_finrank (O : Octad) (A : Subgroup M24)
    (hA : A ≤ octadPointwiseKernel O) (hc : Nat.card A = 4) :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation A) = 4 := by
  obtain ⟨a, ha⟩ := exists_smul_octad_eq O seedOctad
  let B := A.map (MulAut.conj a).toMonoidHom
  have hB : B ≤ octadPointwiseKernel seedOctad := by
    rw [← octad_kernel_map O seedOctad a ha]
    exact Subgroup.map_mono hA
  have hBc : Nat.card B = 4 := (Subgroup.card_map_of_injective (MulAut.conj a).injective).trans hc
  exact (fixedSpaceConjEquiv codeRepresentation A a).finrank_eq.trans
    (SmallKernelFixed.seed_four_finrank B hB hBc)

end MathieuCode
