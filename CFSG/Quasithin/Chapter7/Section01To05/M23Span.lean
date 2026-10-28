module

public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.FixedSpan
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed

/-!
# The native M₂₃ code span used by 7.5.4

The proved native E16 classification supplies a conjugate of the marked
common four-group. This common group lies in the actual octad kernel.
The checked native code calculations give dimension seven for each of two
nonidentity element fixed spaces and dimension four for their intersection.
Thus their span has dimension ten in the eleven-dimensional code. Existing
conjugation and subgroup transport extend this bound to every native E16.
No additional module or group-classification premise remains in this result.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.16.8 and its application in 7.5.4, printed pp.405,700.
-/

public section
open Subgroup Representation.BinaryOffender Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open CFSG.Quasithin.ChapterH.Section13To16

namespace CFSG.Quasithin.Chapter7

private theorem four_generators {X : Type*} [Group X] [Finite X] (A : Subgroup X) [IsElementaryAbelian 2 A]
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
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (g : X) g.property
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


/-- The native H.16.8 bound used in 7.5.4, with all model inputs discharged. -/
theorem m23Code_fixedSpan_bound (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    Module.finrank (ZMod 2)
      (MathieuCode.Code ⧸ fixedSpaceSpan MathieuCode.m23CodeRepresentation A) ≤ 1 := by
  let K := m23CommonKernel
  let _ : IsElementaryAbelian 2 K := standardM23_commonKernel_structure.1
  obtain ⟨a, b, ha, hb, _, hcover⟩ := four_generators K m23CommonKernel_card
  have hK : K.map MathieuCode.pointEmbedding ≤ MathieuCode.octadPointwiseKernel standardOctad := by
    rw [← MathieuCode.octad_core_map_eq_pointwise]
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hKC : Nat.card (K.map MathieuCode.pointEmbedding) = 4 := by
    rw [Subgroup.card_map_of_injective MathieuCode.pointEmbedding_injective]
    exact m23CommonKernel_card
  have hdim : Module.finrank (ZMod 2)
      (fixedSpace MathieuCode.m23CodeRepresentation K) = 4 := by
    rw [MathieuCode.m23CodeRepresentation, fixedSpace_comp_map]
    exact MathieuCode.octad_kernel_four_fixed_finrank standardOctad _ hK hKC
  have hdim1 (c : K) (hc : c ≠ 1) : Module.finrank (ZMod 2)
      (fixedSpace MathieuCode.m23CodeRepresentation (zpowers (c : M23))) = 7 := by
    rw [MathieuCode.m23CodeRepresentation, fixedSpace_comp_map, MonoidHom.map_zpowers]
    apply MathieuCode.octad_kernel_involution_fixed_finrank standardOctad
    · exact hK (mem_map_of_mem _ c.property)
    · intro he
      exact hc (Subtype.ext (MathieuCode.pointEmbedding_injective (he.trans (map_one _).symm)))
  have hfix : fixedSpace MathieuCode.m23CodeRepresentation K =
      fixedSpace MathieuCode.m23CodeRepresentation (zpowers (a : M23)) ⊓
        fixedSpace MathieuCode.m23CodeRepresentation (zpowers (b : M23)) := by
    ext v
    constructor
    · intro hv
      exact ⟨(mem_fixedSpace_zpowers_iff _ _ _).mpr (hv a),
        (mem_fixedSpace_zpowers_iff _ _ _).mpr (hv b)⟩
    · rintro ⟨hv, hw⟩ c
      have hav := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
      have hbv := (mem_fixedSpace_zpowers_iff _ _ _).mp hw
      rcases hcover c with rfl | rfl | rfl | rfl
      · change MathieuCode.m23CodeRepresentation 1 v = v
        simp
      · exact hav
      · exact hbv
      · change MathieuCode.m23CodeRepresentation ((a : M23) * (b : M23)) v = v
        rw [map_mul, Module.End.mul_apply, hbv, hav]
  apply m23Code_fixedSpan_bound_of_common_pair a.property
    (fun he => ha (Subtype.ext he)) b.property (fun he => hb (Subtype.ext he))
    (hdim1 a ha) (hdim1 b hb) _ A hA hcard
  rwa [← hfix]

end CFSG.Quasithin.Chapter7
