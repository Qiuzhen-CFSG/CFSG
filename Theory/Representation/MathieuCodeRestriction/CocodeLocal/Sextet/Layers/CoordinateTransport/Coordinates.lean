module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.Parity
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.AtlasModel

/-!
# Compatible coordinates and their linear transport

A marking consists of an actual point bijection, a bijection of the six parts,
and preservation of the Golay code. Coordinate sums identify the even cores;
quotienting then identifies the literal cocodes. The constructions below retain
the coordinate formulas needed for equivariance and for the geometric layers.

This module is conditional on a marking. Its construction for every native
sextet and the comparison of the two automorphism groups are separate results;
no existence or group identification is assumed as a theorem here.

Source: Aschbacher–Smith H.15.3(1), printed p.400. The concrete ATLAS code and
affine sextet model are by Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the ATLAS Research and Attribution
License 1.0; see LICENSES/ATLAS.txt.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped BigOperators
namespace MathieuCode.SextetLayers.CoordinateTransport
noncomputable section

/-- Concrete code-preserving coordinates, with the literal column membership retained. -/
structure Marking (S : Sextet) where
  pointEquiv : Atlas.Codes.Omega ≃ Fin 24
  partEquiv : Atlas.Codes.HexIndex ≃ SextetPart S
  mem_part : ∀ p i, pointEquiv p ∈ (partEquiv i).val ↔ p.1 = i
  golay_iff : ∀ w : Atlas.Codes.BinaryWord,
    w ∈ Atlas.Codes.golay ↔ (fun x => w (pointEquiv.symm x)) ∈ golay

namespace Marking
variable {S : Sextet} (m : Marking S)

def wordEquiv : Atlas.Codes.BinaryWord ≃ₗ[ZMod 2] Full :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) m.pointEquiv.symm

lemma wordEquiv_apply (w : Atlas.Codes.BinaryWord) (i : Fin 24) :
    m.wordEquiv w i = w (m.pointEquiv.symm i) := rfl

lemma wordEquiv_symm_apply (w : Full) (p : Atlas.Codes.Omega) :
    m.wordEquiv.symm w p = w (m.pointEquiv p) := rfl

lemma mem_golay_iff (w : Atlas.Codes.BinaryWord) :
    w ∈ Atlas.Codes.golay ↔ m.wordEquiv w ∈ golay := m.golay_iff w

lemma golay_map : Atlas.Codes.golay.map m.wordEquiv.toLinearMap = golay := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (m.mem_golay_iff v).mp hv
  · intro hw
    refine ⟨m.wordEquiv.symm w, ?_, m.wordEquiv.apply_symm_apply w⟩
    exact (m.mem_golay_iff _).mpr (by simpa using hw)

lemma mem_core_iff (w : Atlas.Codes.BinaryWord) :
    w ∈ AtlasCore ↔ m.wordEquiv w ∈ Core := by
  change (∑ p, w p) = 0 ↔ (∑ i, w (m.pointEquiv.symm i)) = 0
  rw [Equiv.sum_comp]

lemma core_map : AtlasCore.map m.wordEquiv.toLinearMap = Core := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (m.mem_core_iff v).mp hv
  · intro hw
    refine ⟨m.wordEquiv.symm w, ?_, m.wordEquiv.apply_symm_apply w⟩
    exact (m.mem_core_iff _).mpr (by simpa using hw)

def coreEquiv : AtlasCore ≃ₗ[ZMod 2] Core :=
  m.wordEquiv.ofSubmodules _ _ m.core_map

lemma coreEquiv_val (w : AtlasCore) : (m.coreEquiv w).val = m.wordEquiv w.val := rfl

lemma codeInCore_map : atlasCodeInCore.map m.coreEquiv.toLinearMap = codeInCore := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (m.mem_golay_iff v.val).mp hv
  · intro hw
    refine ⟨m.coreEquiv.symm w, ?_, m.coreEquiv.apply_symm_apply w⟩
    apply (m.mem_golay_iff _).mpr
    change (m.coreEquiv (m.coreEquiv.symm w)).val ∈ golay
    rw [LinearEquiv.apply_symm_apply]
    exact hw

/-- The quotient equivalence uses the same point coordinates as the marking. -/
def cocodeEquiv : AtlasCocode ≃ₗ[ZMod 2] Cocode :=
  Submodule.Quotient.equiv _ _ m.coreEquiv m.codeInCore_map

lemma cocodeEquiv_mk (v : AtlasCore) :
    m.cocodeEquiv (atlasCodeInCore.mkQ v) = codeInCore.mkQ (m.coreEquiv v) := rfl

lemma part_eq_image (i : Atlas.Codes.HexIndex) :
    (m.partEquiv i).val = (Atlas.Codes.tetrad i).image m.pointEquiv := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_image.mpr ⟨m.pointEquiv.symm x, ?_, m.pointEquiv.apply_symm_apply x⟩
    exact (Atlas.Codes.mem_tetrad _ _).mpr ((m.mem_part _ _).mp (by simpa using hx))
  · rintro hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact (m.mem_part _ _).mpr ((Atlas.Codes.mem_tetrad _ _).mp hp)

lemma mem_part_iff (x : Fin 24) (i : Atlas.Codes.HexIndex) :
    x ∈ (m.partEquiv i).val ↔ (m.pointEquiv.symm x).1 = i := by
  simpa using m.mem_part (m.pointEquiv.symm x) i

lemma parity_wordEquiv (v : Atlas.Codes.BinaryWord) (i : Atlas.Codes.HexIndex) :
    sextetParity S (m.wordEquiv v) (m.partEquiv i) = atlasColumnParity v i := by
  change (∑ x ∈ (m.partEquiv i).val, v (m.pointEquiv.symm x)) = ∑ k, v (i,k)
  rw [m.part_eq_image, Finset.sum_image (by intro a _ b _ h; exact m.pointEquiv.injective h)]
  simp only [Equiv.symm_apply_apply, Atlas.Codes.tetrad, Finset.sum_map]
  rfl

lemma parity_zero_iff (v : Atlas.Codes.BinaryWord) :
    atlasColumnParity v = 0 ↔ sextetParity S (m.wordEquiv v) = 0 := by
  constructor
  · intro hv
    ext B
    obtain ⟨i,rfl⟩ := m.partEquiv.surjective B
    exact (m.parity_wordEquiv v i).trans (congrFun hv i)
  · intro hv
    ext i
    exact (m.parity_wordEquiv v i).symm.trans (congrFun hv (m.partEquiv i))

lemma tetradCore_val (i : Atlas.Codes.HexIndex) :
    (m.coreEquiv (atlasTetradCore i)).val = wordOfSet (m.partEquiv i).val := by
  ext x
  simp only [coreEquiv_val, wordEquiv_apply, atlasTetradCore, wordOfSet, m.mem_part_iff]

lemma cocodeEquiv_tetrad (i : Atlas.Codes.HexIndex) :
    m.cocodeEquiv (atlasCodeInCore.mkQ (atlasTetradCore i)) = sextetVector S := by
  rw [m.cocodeEquiv_mk, sextetVector_eq S (m.partEquiv i).property]
  apply congrArg codeInCore.mkQ
  exact Subtype.ext (m.tetradCore_val i)

lemma tetradLine_map : atlasTetradLine.map m.cocodeEquiv.toLinearMap = sextetTetradLine S := by
  rw [atlasTetradLine, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun v => Submodule.span (ZMod 2) {v}) (m.cocodeEquiv_tetrad (0,0))

/-- Equality with the literal span of pairs, using column parity in both directions. -/
lemma pairSpace_map : atlasPairSpace.map m.cocodeEquiv.toLinearMap =
    ⨆ B ∈ S.parts, supportedPairSpace B := by
  apply le_antisymm
  · rintro x ⟨y,⟨v,hv,rfl⟩,rfl⟩
    change m.cocodeEquiv (atlasCodeInCore.mkQ v) ∈ _
    rw [m.cocodeEquiv_mk]
    apply sextetParity_zero_class_mem
    exact (m.parity_zero_iff v.val).mp hv
  · refine iSup_le fun B => iSup_le fun hB => ?_
    apply Submodule.span_le.mpr
    rintro x ⟨P,hP,rfl⟩
    let v : Core := ⟨wordOfSet P.val, wordOfSet_mem_core P⟩
    have hv : sextetParity S v.val = 0 := by
      obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp P.property
      have hi : i ∈ B := hP (by rw [he]; simp)
      have hj : j ∈ B := hP (by rw [he]; simp)
      have hp : wordOfSet P.val = Pi.single i 1 + Pi.single j 1 := by
        rw [he]
        ext k
        by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [wordOfSet]
      change sextetParity S (wordOfSet P.val) = 0
      rw [hp, map_add, sextetParity_single S ⟨B,hB⟩ hi,
        sextetParity_single S ⟨B,hB⟩ hj]
      ext k
      exact CharTwo.add_self_eq_zero _
    refine ⟨atlasCodeInCore.mkQ (m.coreEquiv.symm v), ?_, ?_⟩
    · refine ⟨m.coreEquiv.symm v, ?_, rfl⟩
      apply (m.parity_zero_iff _).mpr
      change sextetParity S (m.coreEquiv (m.coreEquiv.symm v)).val = 0
      rwa [LinearEquiv.apply_symm_apply]
    · change m.cocodeEquiv (atlasCodeInCore.mkQ (m.coreEquiv.symm v)) = _
      rw [m.cocodeEquiv_mk, LinearEquiv.apply_symm_apply]
      rfl

/-- Pointwise coordinate intertwining already implies intertwining on all words. -/
lemma wordEquiv_equivariant (s : Atlas.Codes.SextetStabilizer) (g : M24)
    (h : ∀ p, g.val (m.pointEquiv p) = m.pointEquiv (s.val.val p))
    (v : Atlas.Codes.BinaryWord) :
    m.wordEquiv (atlasFullRepresentation s v) = fullRepresentation g (m.wordEquiv v) := by
  ext x
  change v (s.val.val.symm (m.pointEquiv.symm x)) =
    v (m.pointEquiv.symm (g.val.symm x))
  apply congrArg v
  apply m.pointEquiv.injective
  apply g.val.injective
  rw [h]
  simp only [Equiv.apply_symm_apply]

lemma coreEquiv_equivariant (s : Atlas.Codes.SextetStabilizer) (g : M24)
    (h : ∀ p, g.val (m.pointEquiv p) = m.pointEquiv (s.val.val p)) (v : AtlasCore) :
    m.coreEquiv (atlasCoreRepresentation s v) = coreRepresentation g (m.coreEquiv v) := by
  apply Subtype.ext
  exact m.wordEquiv_equivariant s g h v.val

/-- Equivariance of the actual quotient map, under pointwise-compatible group elements. -/
lemma cocodeEquiv_equivariant (s : Atlas.Codes.SextetStabilizer) (g : M24)
    (h : ∀ p, g.val (m.pointEquiv p) = m.pointEquiv (s.val.val p)) (v : AtlasCocode) :
    m.cocodeEquiv (atlasCocodeRepresentation s v) =
      cocodeRepresentation g (m.cocodeEquiv v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change m.cocodeEquiv (atlasCocodeRepresentation s (atlasCodeInCore.mkQ v)) =
      cocodeRepresentation g (m.cocodeEquiv (atlasCodeInCore.mkQ v))
    rw [atlasCocodeRepresentation_mk, m.cocodeEquiv_mk, m.cocodeEquiv_mk,
      cocodeRepresentation_mk, m.coreEquiv_equivariant s g h]

end Marking
end
end MathieuCode.SextetLayers.CoordinateTransport
