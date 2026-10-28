module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Planes
public import Theory.Representation.MathieuCodeRestriction.Duality

/-!
# The standard-trio fixed three-space

The native paired translations give eight independent commutators on the dual
Golay code. The code--cocode pairing bounds the intrinsic two-core fixed space
by dimension three, while the affine-plane map supplies a three-dimensional
subspace. This is the theory-layer calculation used by the CFSG adapter.

Source: Aschbacher--Smith, H.15.6(1), printed p.401 (PDF p.412), with the
intrinsic two-core convention from H.14.1.
-/

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode Representation.BinaryOffender
open scoped BigOperators Pointwise
namespace MathieuCode.TrioCalculation
noncomputable section

namespace FixedSpaceCalc

/-- Native row messages of the eight selected displacements. -/
def displacementMessage : Fin 8 → Fin 4096 := ![1856, 1408, 800, 2960, 528, 1283, 298, 25]
def displacementClass (i : Fin 8) : Code := codeLine.mkQ ⟨wordOfMask (m24GolayCode (displacementMessage i)), wordOfMask_code_mem _⟩
def rowIndex (i : Fin 8) : Fin 12 := ![0, 1, 2, 4, 0, 0, 2, 0] i
def rowClass (k : Fin 12) : Code := codeLine.mkQ ⟨row k, row_mem k⟩
def firstVector : Vector := ![1, 0, 0]
def secondVector : Vector := ![0, 1, 0]
def translation (i : Fin 8) : trioStabilizer standardTrio :=
  ![TrioCalculation.pairedTranslation 0 firstVector, TrioCalculation.pairedTranslation 0 firstVector,
    TrioCalculation.pairedTranslation 0 firstVector, TrioCalculation.pairedTranslation 0 firstVector,
    TrioCalculation.pairedTranslation 0 secondVector, TrioCalculation.pairedTranslation 1 firstVector,
    TrioCalculation.pairedTranslation 1 firstVector, TrioCalculation.pairedTranslation 1 secondVector] i
def fixedOctadIndex (i : Fin 8) : Fin 3 := ![0, 0, 0, 0, 0, 1, 1, 1] i
def translationVector (i : Fin 8) : Vector :=
  ![![1, 0, 0],![1, 0, 0],![1, 0, 0],![1, 0, 0],![0, 1, 0],![1, 0, 0],![1, 0, 0],![0, 1, 0]] i
def translatedRowMessage : Fin 8 → Fin 4096 := ![1857, 1410, 804, 2944, 529, 1282, 302, 24]

private lemma action_row (i : Fin 8) :
    m24PermuteMask (pairedTranslationPerm (fixedOctadIndex i) (translationVector i)) (m24GolayRow (rowIndex i)) =
      m24GolayCode (translatedRowMessage i) := by
  ext x
  simp only [Sporadic.Mathieu.m24PermuteMask]
  have hx : x < 24 := by omega
  rw [BitVec.getElem_ofFnLE _ x hx]
  let x' : Fin 24 := ⟨x, hx⟩
  obtain ⟨⟨a, w⟩, hpoint⟩ := point.surjective x'
  have hbit (a : Fin 3) (w : Vector) :
      (m24GolayRow (rowIndex i)).getLsb ((pairedTranslationPerm (fixedOctadIndex i) (translationVector i)).symm (point (a, w))) =
        (m24GolayCode (translatedRowMessage i)).getLsb (point (a, w)) := by
    have hinv : (pairedTranslationPerm (fixedOctadIndex i) (translationVector i)).symm (point (a, w)) =
        point (a, w + if a = fixedOctadIndex i then 0 else translationVector i) := by
      apply (pairedTranslationPerm (fixedOctadIndex i) (translationVector i)).injective
      rw [Equiv.apply_symm_apply, pairedTranslationPerm_point]
      by_cases ha : a = fixedOctadIndex i
      · simp [ha]
      · rw [if_neg ha]
        have hvv : translationVector i + translationVector i = 0 := by
          funext q
          simp
        rw [add_assoc, hvv, add_zero]
    rw [hinv]
    clear hinv
    revert a w
    fin_cases i <;> decide +kernel
  simpa [hpoint] using hbit a w

private lemma golay_action_row (j : Fin 3) (v : Vector) (k : Fin 12) (u : Fin 4096)
    (h : m24PermuteMask (pairedTranslationPerm j v) (m24GolayRow k) = m24GolayCode u) :
    golayRepresentation (pairedTranslation j v).val
      (⟨row k, row_mem k⟩ : golay) =
      ⟨wordOfMask (m24GolayCode u), wordOfMask_code_mem _⟩ := by
  apply Subtype.ext
  funext x
  have hp : (pairedTranslation j v).val.val = pairedTranslationPerm j v := by
    apply Equiv.ext
    intro y
    obtain ⟨⟨i, w⟩, rfl⟩ := point.surjective y
    exact pairedTranslation_point j i v w |>.trans (pairedTranslationPerm_point j i v w).symm
  change (row k) ((pairedTranslation j v).val.val.symm x) = wordOfMask (m24GolayCode u) x
  rw [hp]
  change wordOfMask (m24GolayRow k) ((pairedTranslationPerm j v).symm x) = _
  simp only [wordOfMask]
  simp only [Sporadic.Mathieu.m24PermuteMask] at h
  have hx : (m24GolayRow k).getLsb ((pairedTranslationPerm j v).symm x) =
      (m24GolayCode u).getLsb x := by
    calc
      _ = (BitVec.ofFnLE (fun y => (m24GolayRow k).getLsb
          ((Equiv.symm (pairedTranslationPerm j v)) y))).getLsb x :=
        (BitVec.getLsb_ofFnLE _ _).symm
      _ = (m24GolayCode u).getLsb x := by rw [h]
  rw [hx]

def displacementSpace : Submodule (ZMod 2) Code := Submodule.span (ZMod 2) (Set.range displacementClass)
def displacementDualSpace : Submodule (ZMod 2) (Module.Dual (ZMod 2) Cocode) :=
  displacementSpace.map codeCocodePairing

/-- Independence is checked in the Golay space modulo its all-ones line. -/
private lemma displacementClass_linearIndependent : LinearIndependent (ZMod 2) displacementClass := by
  rw [Fintype.linearIndependent_iff]
  intro c h i
  let u : golay := ∑ j, c j •
      (⟨wordOfMask (m24GolayCode (displacementMessage j)), wordOfMask_code_mem _⟩ : golay)
  have hq : codeLine.mkQ u = 0 := by
    change codeLine.mkQ (∑ j, c j •
      (⟨wordOfMask (m24GolayCode (displacementMessage j)), wordOfMask_code_mem _⟩ : golay)) = 0
    simp only [map_sum, LinearMap.map_smul]
    simpa [displacementClass] using h
  have hm : u ∈ codeLine := (Submodule.Quotient.mk_eq_zero codeLine).mp hq
  change golay.subtype u ∈ Submodule.span (ZMod 2)
    {BinaryPermutation.allOne (Fin 24)} at hm
  have h' : ∃ d : ZMod 2,
      (∑ j, c j • wordOfMask (m24GolayCode (displacementMessage j))) =
        d • BinaryPermutation.allOne (Fin 24) := by
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨d, ?_⟩
    simpa [u] using hd.symm
  clear h hq hm u
  revert i c h'
  decide +kernel

private lemma finrank_displacementSpace : Module.finrank (ZMod 2) displacementSpace = 8 := by
  exact finrank_span_eq_card displacementClass_linearIndependent

private lemma displacementClass_eq_action_sub (i : Fin 8) :
    codeRepresentation (translation i).val (rowClass (rowIndex i)) - rowClass (rowIndex i) = displacementClass i := by
  apply (Submodule.Quotient.eq codeLine).mpr
  change _ ∈ codeLine
  change _ ∈ Submodule.span (ZMod 2) {BinaryPermutation.allOne (Fin 24)}
  rw [Submodule.mem_span_singleton]
  have hcg : translation i = pairedTranslation (fixedOctadIndex i) (translationVector i) := by
    fin_cases i <;> rfl
  rw [hcg]
  have hrow := golay_action_row (fixedOctadIndex i) (translationVector i) (rowIndex i) (translatedRowMessage i) (action_row i)
  rw [hrow]
  fin_cases i <;> decide +kernel

private lemma translation_mem_kernel (i : Fin 8) : (translation i).val ∈ ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype) := by
  fin_cases i <;>
    exact Subgroup.mem_map_of_mem _
      (TrioCalculation.pairedTranslation_mem_twoCore _ _)

private lemma displacementClass_pair_fixed (v : Cocode) (hv : v ∈ fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype)) (i : Fin 8) :
    codeCocodePairing (displacementClass i) v = 0 := by
  have hfix : cocodeRepresentation (translation i).val v = v :=
    hv ⟨(translation i).val, translation_mem_kernel i⟩
  have hinv := codeCocodePairing_invariant (translation i).val (rowClass (rowIndex i)) v
  calc
    codeCocodePairing (displacementClass i) v =
        codeCocodePairing (codeRepresentation (translation i).val (rowClass (rowIndex i)) - rowClass (rowIndex i)) v := by
          rw [displacementClass_eq_action_sub]
    _ = codeCocodePairing (codeRepresentation (translation i).val (rowClass (rowIndex i))) v -
        codeCocodePairing (rowClass (rowIndex i)) v := by
          simp only [map_sub, LinearMap.sub_apply]
    _ = codeCocodePairing (codeRepresentation (translation i).val (rowClass (rowIndex i)))
          (cocodeRepresentation (translation i).val v) - codeCocodePairing (rowClass (rowIndex i)) v := by rw [hfix]
    _ = 0 := by rw [hinv]; exact sub_self _

private lemma fixed_le_annihilator :
    fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype) ≤ displacementDualSpace.dualCoannihilator := by
  intro v hv
  rw [Submodule.mem_dualCoannihilator]
  intro φ hφ
  obtain ⟨w, hw, rfl⟩ := hφ
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact displacementClass_pair_fixed v hv i
  | zero => simp
  | add x y _ _ hx hy => simpa [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x _ hx => simpa [map_smul] using congrArg (c • ·) hx

private lemma finrank_displacementDualSpace : Module.finrank (ZMod 2) displacementDualSpace = 8 := by
  let e := displacementSpace.equivMapOfInjective codeCocodePairing codeCocodePairing_injective
  exact (e.finrank_eq).symm.trans finrank_displacementSpace

private lemma finrank_fixed_le_three :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype)) ≤ 3 := by
  have ha := Subspace.finrank_add_finrank_dualCoannihilator_eq displacementDualSpace
  rw [finrank_displacementDualSpace, finrank_cocode] at ha
  have hmono := Submodule.finrank_mono fixed_le_annihilator
  omega

end FixedSpaceCalc

/-- The entire fixed space of the standard trio two-core is the affine-plane range. -/
public theorem standard_fixedSpace_eq_planeRange : fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype) = MathieuCode.TrioCalculation.standardPlaneMap.range := by
  have hlow : MathieuCode.TrioCalculation.standardPlaneMap.range ≤
      fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype) :=
    TrioCalculation.standardPlaneMap_range_le_fixedSpace
  have hfinlow : Module.finrank (ZMod 2) MathieuCode.TrioCalculation.standardPlaneMap.range ≤
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype)) :=
    Submodule.finrank_mono hlow
  have hfinrange : Module.finrank (ZMod 2) MathieuCode.TrioCalculation.standardPlaneMap.range = 3 :=
    TrioCalculation.finrank_standardPlaneMap_range
  have hfineq : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype)) ≤ 3 :=
    FixedSpaceCalc.finrank_fixed_le_three
  have hfin : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype)) =
      Module.finrank (ZMod 2) MathieuCode.TrioCalculation.standardPlaneMap.range := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hlow hfin.symm).symm

end
end MathieuCode.TrioCalculation
