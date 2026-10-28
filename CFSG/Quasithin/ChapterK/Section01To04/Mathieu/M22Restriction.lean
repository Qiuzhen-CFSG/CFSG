module

public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.LinearSteps
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions

/-!
# K.4.4 on the native M22 code and cocode

The actual setwise stabilizer of the pair {0,9} acts on the code hyperplane
and the cocode quotient by the pair line. Every inner involution retains its
entire ambient displacement image. Thus the ambient six-dimensional pair span
leaves at least five commutator dimensions on the hyperplane, giving the cocode
bound by coordinate duality. The ambient fixed six-space gives the code bound
four by the hyperplane inequality. Involution displacements also prove m > 2.

The ratio assembly theorems explicitly retain the octad geometry: the rank-two
classification, the ambient fixed six-space, and the pair displacement span.
They do not assert that these geometric premises have yet been established.
The source reference to K.4.3(4) in the proof of K.4.4(1) means the fixed-space
identity in K.4.3(5): ambient dimension eleven minus fixed dimension six is five.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.4.4 and the
code/cocode ratio subsection, printed p.459.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Mathieu

open MathieuCode Sporadic.Mathieu MathieuCode.CocodeOctad.Involutions

theorem m22_hyperplane_codim :
    Module.finrank (ZMod 2) (Code ⧸ m22Hyperplane) = 1 := by
  have h := m22Hyperplane.finrank_quotient_add_finrank
  rw [finrank_code, show Module.finrank (ZMod 2) m22Hyperplane = 10 from finrank_m22Code] at h
  omega

/-- The literal K.4.4(1) restriction, from K.4.3(5)'s fixed six-space. -/
theorem m22_code_bound_of_fixed_six (A : Subgroup m22PairStabilizer)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace codeRepresentation (A.map m22PairStabilizer.subtype)) = 6) :
    4 ≤ fixedCodim m22OuterCodeRepresentation A := by
  have h := fixedCodim_le_subrepresentation_add_codim
    (codeRepresentation.comp m22PairStabilizer.subtype) m22OuterCodeSubrepresentation A
  have hdim := fixedCodim_add_finrank
    (codeRepresentation.comp m22PairStabilizer.subtype) A
  rw [fixedSpace_comp_map, hfixed, finrank_code] at hdim
  change fixedCodim (codeRepresentation.comp m22PairStabilizer.subtype) A ≤
    fixedCodim m22OuterCodeRepresentation A +
      Module.finrank (ZMod 2) (Code ⧸ m22Hyperplane) at h
  rw [m22_hyperplane_codim] at h
  omega

/-- Coordinate duality applies to the full setwise pair extension. -/
theorem m22_cocode_codim_eq_code_dual (A : Subgroup m22PairStabilizer) :
    fixedCodim m22OuterCocodeRepresentation A =
      fixedCodim m22OuterCodeRepresentation.dual A := by
  rw [fixedCodim_dual_eq_commutator]
  exact fixedCodim_of_pairing m22OuterCodeRepresentation m22OuterCocodeRepresentation
    m22CodeCocodeDuality m22CodeCocodeDuality_equivariant A

/-- The rank-five bound of K.4.4(2), on the actual cocode quotient.
The input is the retained z-image and the ambient six-dimensional pair span,
not a dimension bound on the requested quotient. -/
theorem m22_cocode_bound_of_retained_pair (A : Subgroup m22PairStabilizer)
    (z d : m22PairStabilizer) (hz : z ∈ A) (hd : d ∈ A)
    (hzfull : m22Hyperplane.map (displacement codeRepresentation z.val) =
      LinearMap.range (displacement codeRepresentation z.val))
    (hpair : Module.finrank (ZMod 2)
      (LinearMap.range (displacement codeRepresentation z.val) ⊔
       LinearMap.range (displacement codeRepresentation d.val) : Submodule (ZMod 2) Code) = 6) :
    5 ≤ fixedCodim m22OuterCocodeRepresentation A := by
  have h := retained_displacement_pair_bound
    (codeRepresentation.comp m22PairStabilizer.subtype) m22OuterCodeSubrepresentation hz hd hzfull
  change Module.finrank (ZMod 2)
      (LinearMap.range (displacement codeRepresentation z.val) ⊔
       LinearMap.range (displacement codeRepresentation d.val) : Submodule (ZMod 2) Code) ≤
    fixedCodim m22OuterCodeRepresentation.dual A +
      Module.finrank (ZMod 2) (Code ⧸ m22Hyperplane) at h
  rw [hpair, m22_hyperplane_codim, ← m22_cocode_codim_eq_code_dual] at h
  omega

/-- The inner involution in K.4.4 retains its entire ambient displacement image. -/
theorem m22_retained_inner_displacement (x : m22PairStabilizer)
    (hx : orderOf x = 2) (h0 : x.val • (0 : Fin 24) = 0) :
    m22Hyperplane.map (displacement codeRepresentation x.val) =
      LinearMap.range (displacement codeRepresentation x.val) := by
  apply restricted_displacement_eq_of_codim_eq
    (codeRepresentation.comp m22PairStabilizer.subtype) m22OuterCodeSubrepresentation x
  have hinner : fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers x) = 4 := by
    rw [m22Outer_code_cocode_fixedCodim_zpowers]
    exact m22Outer_cocode_involution_displacement_of_fixed_zero x hx h0
  have hconj : IsConj z x.val := by
    have ho := (orderOf_injective m22PairStabilizer.subtype Subtype.val_injective x).trans hx
    rcases M24InvolutionCentralizers.involution_classes x.val ho with hz | ht
    · exact hz
    · obtain ⟨c, hc⟩ := isConj_iff.mp ht
      change c * t * c⁻¹ = x.val at hc
      rw [← hc] at h0
      have h := congrArg (fun i : Fin 24 => c⁻¹ • i) h0
      exact (t_fixedPointFree (c⁻¹ • 0)
        (by simpa only [mul_smul, inv_smul_smul] using h)).elim
  change fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers x) = _
  rw [hinner, fixedCodim, fixedSpace_comp_map, MonoidHom.map_zpowers]
  change 4 = fixedCodim codeRepresentation (Subgroup.zpowers x.val)
  rw [code_cocode_fixedCodim_zpowers, fixedCodim_of_isConj_z _ hconj]

/-- K.4.4's cocode dimension calculation, retaining only the ambient pair geometry. -/
theorem m22_cocode_bound_of_inner_pair (A : Subgroup m22PairStabilizer)
    (x d : m22PairStabilizer) (hx : x ∈ A) (hd : d ∈ A)
    (hx2 : orderOf x = 2) (h0 : x.val • (0 : Fin 24) = 0)
    (hpair : Module.finrank (ZMod 2)
      (LinearMap.range (displacement codeRepresentation x.val) ⊔
       LinearMap.range (displacement codeRepresentation d.val) : Submodule (ZMod 2) Code) = 6) :
    5 ≤ fixedCodim m22OuterCocodeRepresentation A :=
  m22_cocode_bound_of_retained_pair A x d hx hd (m22_retained_inner_displacement x hx2 h0) hpair

theorem m22_code_quadratic_iff_cocode (A : Subgroup m22PairStabilizer) :
    IsQuadratic m22OuterCodeRepresentation A ↔ IsQuadratic m22OuterCocodeRepresentation A := by
  constructor
  · intro h
    apply (quadratic_iff_dual m22OuterCocodeRepresentation A).mpr
    exact quadratic_of_equivariant_surjection m22OuterCodeRepresentation
      m22OuterCocodeRepresentation.dual m22CodeCocodeDuality.toLinearMap
      m22CodeCocodeDuality.surjective m22CodeCocodeDuality_equivariant A h
  · intro h a ha b hb v
    apply m22CodeCocodeDuality.injective
    have hd := (quadratic_iff_dual m22OuterCocodeRepresentation A).mp h
    simpa only [map_sub, m22CodeCocodeDuality_equivariant] using
      hd a ha b hb (m22CodeCocodeDuality v)

theorem m22_code_moduleM_gt_two : 2 < ChapterE.moduleM m22OuterCodeRepresentation := by
  have h : 3 ≤ ChapterE.moduleM m22OuterCodeRepresentation := by
    apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro n (rfl | ⟨x, hx, rfl⟩)
    · change 3 ≤ Module.finrank (ZMod 2) M22Code
      rw [finrank_m22Code]
      decide
    · exact (m22Outer_involution_displacement_ge_three x hx).1
  omega

theorem m22_cocode_moduleM_gt_two : 2 < ChapterE.moduleM m22OuterCocodeRepresentation := by
  have h : 3 ≤ ChapterE.moduleM m22OuterCocodeRepresentation := by
    apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro n (rfl | ⟨x, hx, rfl⟩)
    · change 3 ≤ Module.finrank (ZMod 2) M22Cocode
      rw [finrank_m22Cocode]
      decide
    · exact (m22Outer_involution_displacement_ge_three x hx).2
  omega

/-- Assemble the code bound after the native octad geometry is supplied. -/
theorem m22_code_ratio_of_octad_geometry
    (hgeometry : ∀ A ∈ quadraticSubgroups m22OuterCodeRepresentation,
      rank A = 2 ∧ Module.finrank (ZMod 2)
        (fixedSpace codeRepresentation (A.map m22PairStabilizer.subtype)) = 6) :
    2 ≤ quadraticRatio m22OuterCodeRepresentation := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hquad⟩
  have hrpos := hA.rank_pos
  have hbound : 2 * rank A ≤ fixedCodim m22OuterCodeRepresentation A := by
    by_cases hr : 1 < rank A
    · obtain ⟨hrank, hfixed⟩ := hgeometry A ⟨hA, hr, hquad⟩
      have hd := m22_code_bound_of_fixed_six A hfixed
      omega
    · have hd := ChapterE.moduleM_le_fixedCodim m22OuterCodeRepresentation hA
      have hm := m22_code_moduleM_gt_two
      omega
  rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (Nat.ne_of_gt hrpos)))
    (Or.inl (by simp))]
  exact_mod_cast hbound

/-- The cocode half uses the actual quotient and the actual inner involution.
Its geometric premise is supplied by the octad calculation, not by a ratio hypothesis. -/
theorem m22_cocode_ratio_of_octad_geometry
    (hgeometry : ∀ A ∈ quadraticSubgroups m22OuterCodeRepresentation,
      rank A = 2 ∧ ∃ x d : m22PairStabilizer,
        x ∈ A ∧ d ∈ A ∧ orderOf x = 2 ∧ x.val • (0 : Fin 24) = 0 ∧
        Module.finrank (ZMod 2)
          (LinearMap.range (displacement codeRepresentation x.val) ⊔
           LinearMap.range (displacement codeRepresentation d.val) : Submodule (ZMod 2) Code) = 6) :
    2 < quadraticRatio m22OuterCocodeRepresentation := by
  apply two_lt_quadraticRatio_of_quadraticSubgroups _ m22_cocode_moduleM_gt_two
  intro A hA
  obtain ⟨hr, x, d, hx, hd, hx2, h0, hpair⟩ := hgeometry A
    ⟨hA.1, hA.2.1, (m22_code_quadratic_iff_cocode A).mpr hA.2.2⟩
  have hb := m22_cocode_bound_of_inner_pair A x d hx hd hx2 h0 hpair
  omega

end CFSG.Quasithin.ChapterK.Mathieu
