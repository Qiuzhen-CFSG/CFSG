module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Kernel
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Hyperplane
public import Theory.Representation.BinaryOffender.FixedSpaceSpan

/-!
# Fixed-space and quotient-action interfaces for octad kernels

This module records the linear consequences of the native octad geometry in a
form suitable for the H.15.2 assembly.  The pair space is the common fixed
space once its dimension has been established.  The legacy pair-rank helper is retained for compatibility; the native
fixed-space span calculation is supplied by `Dynamics.FixedSpaces`.  The quotient representation and parity map are constructed
literally, so later finite native action certificates can state their action
without changing the module boundary.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, H.15.2(4--6),
printed p.399.
-/

@[expose] public section

open scoped Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.CocodeOctad
noncomputable section

def intrinsicOctadKernel (O : Octad) : Subgroup M24 :=
  (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype

abbrev octadPairSpace (O : Octad) : Submodule (ZMod 2) Cocode := supportedPairSpace O.val

lemma finrank_fixedSpace_of_fixedCodim (O : Octad) (z : intrinsicOctadKernel O)
    (hcodim : fixedCodim cocodeRepresentation (Subgroup.zpowers z.val) = 4) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (Subgroup.zpowers z.val)) = 7 := by
  have h := fixedCodim_add_finrank cocodeRepresentation (Subgroup.zpowers z.val)
  have hq : Module.finrank (ZMod 2)
      (Cocode ⧸ fixedSpace cocodeRepresentation (Subgroup.zpowers z.val)) = 4 := by
    simpa [fixedCodim] using hcodim
  unfold fixedCodim at h
  rw [finrank_cocode, hq] at h
  have hh : 4 + Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation (Subgroup.zpowers z.val)) = 4 + 7 := by
    norm_num at h ⊢
    exact h
  exact Nat.add_left_cancel hh

lemma octadPairSpace_eq_fixedSpace_of_finrank
    (O : Octad) (A : Subgroup M24)
    (hU : octadPairSpace O ≤ fixedSpace cocodeRepresentation A)
    (hF : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation A) = 6) :
    fixedSpace cocodeRepresentation A = octadPairSpace O := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq hU
  rw [finrank_supportedPairSpace O, hF]

lemma fixedSpace_eq_octadPairSpace_of_noncyclic
    (O : Octad) (A : Subgroup M24) (_hA : A ≤ intrinsicOctadKernel O)
    (_hnc : ¬ IsCyclic A)
    (hU : octadPairSpace O ≤ fixedSpace cocodeRepresentation A)
    (hF : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation A) = 6) :
    fixedSpace cocodeRepresentation A = octadPairSpace O := by
  exact octadPairSpace_eq_fixedSpace_of_finrank O A hU hF

lemma fixedSpaceSpan_eq_octadHyperplane_of_pair
    (O : Octad) (K : Subgroup M24)
    (_hK : K ≤ octadStabilizer O)
    (hcentral : ∀ a ∈ K, a ≠ 1 →
      fixedSpace cocodeRepresentation (Subgroup.zpowers a) ≤ octadHyperplane O)
    {a b : M24} (ha : a ∈ K) (ha1 : a ≠ 1)
    (hb : b ∈ K) (hb1 : b ≠ 1)
    (hd : Module.finrank (ZMod 2) (octadHyperplane O) +
        Module.finrank (ZMod 2)
          ↥(fixedSpace cocodeRepresentation (Subgroup.zpowers a) ⊓
            fixedSpace cocodeRepresentation (Subgroup.zpowers b)) =
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (Subgroup.zpowers a)) +
        Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (Subgroup.zpowers b))) :
    fixedSpaceSpan cocodeRepresentation K = octadHyperplane O := by
  apply fixedSpaceSpan_eq_of_pair cocodeRepresentation ha ha1 hb hb1
    (octadHyperplane O) hcentral hd

def quotientOctadParity (O : Octad) :
    (Cocode ⧸ octadPairSpace O) →ₗ[ZMod 2] ZMod 2 :=
  (octadPairSpace O).liftQ (octadParity O)
    (fun _v hv => (supportedPairSpace_le_octadHyperplane O) hv)

@[simp] lemma quotientOctadParity_mkQ (O : Octad) (v : Cocode) :
    quotientOctadParity O ((octadPairSpace O).mkQ v) = octadParity O v := rfl

lemma quotientOctadParity_surjective (O : Octad) :
    Function.Surjective (quotientOctadParity O) := by
  intro c
  obtain ⟨v, hv⟩ := octadParity_surjective O c
  exact ⟨(octadPairSpace O).mkQ v, by rw [quotientOctadParity_mkQ, hv]⟩

lemma quotientOctadParity_eq_zero_iff (O : Octad) (v : Cocode) :
    quotientOctadParity O ((octadPairSpace O).mkQ v) = 0 ↔
      v ∈ octadHyperplane O := by
  rw [quotientOctadParity_mkQ]
  rfl

def quotientTransvection (O : Octad) (a : Cocode ⧸ octadPairSpace O) :
    (Cocode ⧸ octadPairSpace O) →ₗ[ZMod 2] (Cocode ⧸ octadPairSpace O) where
  toFun x := x + quotientOctadParity O x • a
  map_add' x y := by
    simp [add_smul, add_assoc, add_left_comm]
  map_smul' c x := by
    simp [smul_add, smul_smul]

@[simp] lemma quotientTransvection_apply (O : Octad)
    (a x : Cocode ⧸ octadPairSpace O) :
    quotientTransvection O a x = x + quotientOctadParity O x • a := rfl

lemma quotientTransvection_eq_of_parity_eq
    (O : Octad) {a b : Cocode ⧸ octadPairSpace O}
    (h : a = b) : quotientTransvection O a = quotientTransvection O b := by
  rw [h]

end
end MathieuCode.CocodeOctad
