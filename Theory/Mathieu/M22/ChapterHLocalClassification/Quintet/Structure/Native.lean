module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Structure.AtlasLocal
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Translations
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient.Geometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport

/-!
# Native pair lifts and the quintet part-action kernel

The proved native coordinate comparison places the literal points 0 and 9 in
one hexacode column. Transporting the affine pair calculation lifts every part
permutation fixing their tetrad while fixing both points. It also identifies
the literal part-action kernel with the restricted source translations.
Translation membership is checked against the intrinsic source sextet core,
so this comparison is independent of choices of coordinates.

Source: Aschbacher--Smith H.14.3(2) and its proof, printed p.397, setup p.396.
The licensed ATLAS calculations are documented in the imported AtlasLocal
and CoordinateTransport modules.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode MathieuCode.M22Quintet
open Atlas.Codes
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.Quintet.Structure
open MathieuCode.SextetLayers.CoordinateTransport
open MathieuCode.M22Quintet.CocodeTransfer
namespace Native
abbrev point := nativePointEquiv m22SourceSextet
abbrev parts := nativePartEquiv m22SourceSextet
abbrev equiv := nativeStabilizerEquiv m22SourceSextet

theorem coordinates (s : SextetStabilizer) (p : Omega) :
    (equiv s).val.val (point p) = point (s.val.val p) :=
  nativeStabilizer_coordinates m22SourceSextet s p

def first : HexIndex := parts.symm (NaturalQuotient.partNumbering 0)
def rowZero : Fin 4 := (point.symm 0).2
def rowNine : Fin 4 := (point.symm 9).2

private theorem pair_first (x : Fin 24) (hx : x ∈ m22SourceTetrad 0) :
    (point.symm x).1 = first := by
  apply (nativePointEquiv_mem_part m22SourceSextet (point.symm x) first).mp
  rw [point.apply_symm_apply, first, parts.apply_symm_apply]
  exact hx

theorem zero_coordinates : point (first,rowZero) = 0 := by
  rw [← pair_first 0 (by decide)]
  exact point.apply_symm_apply 0

theorem nine_coordinates : point (first,rowNine) = 9 := by
  rw [← pair_first 9 (by decide)]
  exact point.apply_symm_apply 9

theorem rows_ne : rowZero ≠ rowNine := by
  intro h
  have he : (0 : Fin 24) = 9 := zero_coordinates.symm.trans (h ▸ nine_coordinates)
  exact (by decide : (0 : Fin 24) ≠ 9) he

/-- Translation membership is intrinsic, independently of the chosen native marking. -/
theorem core_mem (g : sextetStabilizer m22SourceSextet) :
    g.val ∈ Sextet.sourceCore ↔ sextetQuotient (equiv.symm g) = 1 := by
  have hc := pCore_map_iso 2 equiv.symm
  rw [SextetCore.atlas_core_eq_kernel] at hc
  have he : g.val ∈ Sextet.sourceCore ↔ g ∈ pCore 2 (sextetStabilizer m22SourceSextet) := by
    constructor
    · rintro ⟨h,hh,he⟩
      exact (Subtype.ext he : h = g) ▸ hh
    · intro h
      exact ⟨g,h,rfl⟩
  rw [he, ← Subgroup.mem_map_iff_mem (f := equiv.symm.toMonoidHom) equiv.symm.injective, hc]
  rfl

/-- All five-part permutations lift with the deleted points fixed individually. -/
theorem lift_parts (σ : Equiv.Perm (SextetPart m22SourceSextet))
    (hσ : σ (NaturalQuotient.partNumbering 0) = NaturalQuotient.partNumbering 0) :
    ∃ g : Q, NaturalQuotient.partAction g = σ ∧ g.val.val.val 0 = 0 := by
  let τ := parts.symm.permCongr σ
  have ht : τ first = first := by
    change parts.symm (σ (parts first)) = first
    rw [first,parts.apply_symm_apply,hσ]
  obtain ⟨s,hs,h0,h9⟩ := atlas_pair_lift first rowZero rowNine rows_ne τ ht
  let t := equiv s
  have hzero : t.val.val 0 = 0 := by
    rw [← zero_coordinates]
    exact (coordinates s _).trans (congrArg point h0)
  have hnine : t.val.val 9 = 9 := by
    rw [← nine_coordinates]
    exact (coordinates s _).trans (congrArg point h9)
  have hpair : t.val ∈ m22PairStabilizer := by
    change m22Pair.image t.val.val = m22Pair
    simp only [m22Pair,Finset.image_insert,Finset.image_singleton,hzero,hnine]
  let g : Q := ⟨⟨t.val,hpair⟩,t.property⟩
  refine ⟨g,?_,hzero⟩
  apply Equiv.ext
  intro B
  obtain ⟨i,rfl⟩ := parts.surjective B
  change sextetPartPerm m22SourceSextet (equiv s) (parts i) = _
  rw [nativePartPerm_apply]
  have hi : hexCoordinateHom (sextetQuotient s) i = τ i :=
    (sextet_coordinate_compatibility s i 0).symm.trans (hs i 0)
  rw [hi]
  exact parts.apply_symm_apply _

/-- The literal part-action kernel consists precisely of the restricted translations. -/
theorem part_kernel :
    NaturalQuotient.partAction.ker = Sextet.outerTranslations.subgroupOf Q := by
  ext g
  change NaturalQuotient.partAction g = 1 ↔ g.val.val ∈ Sextet.sourceCore
  constructor
  · intro hg
    apply (core_mem (QToSextet g)).mpr
    let s := equiv.symm (QToSextet g)
    have he : equiv s = QToSextet g := equiv.apply_symm_apply _
    have hc : hexCoordinateHom (sextetQuotient s) = 1 := by
      apply Equiv.ext
      intro i
      apply parts.injective
      have h := nativePartPerm_apply m22SourceSextet s i
      rw [he] at h
      change NaturalQuotient.partAction g (parts i) = _ at h
      rw [hg] at h
      exact h.symm
    have hm (x : Fin 24) (hx : x ∈ m22Pair) : g.val.val.val x ∈ m22Pair :=
      (MulAction.mem_stabilizer_finset'.mp g.val.property) hx
    have hz : g.val.val.val 0 = 0 ∨ g.val.val.val 0 = 9 := by
      simpa only [m22Pair,Finset.mem_insert,Finset.mem_singleton] using hm 0 (by decide)
    have hn : g.val.val.val 9 = 0 ∨ g.val.val.val 9 = 9 := by
      simpa only [m22Pair,Finset.mem_insert,Finset.mem_singleton] using hm 9 (by decide)
    have hcoord (p : Omega) : point (s.val.val p) = g.val.val.val (point p) := by
      rw [← coordinates,he]
      rfl
    apply atlas_pair_kernel first rowZero rowNine rows_ne s hc
    · have hz' := hz
      rw [← zero_coordinates, ← hcoord] at hz'
      exact hz'.imp (fun h => point.injective h) (fun h => point.injective (h.trans nine_coordinates.symm))
    · have hn' := hn
      rw [← nine_coordinates, ← hcoord] at hn'
      exact hn'.imp (fun h => point.injective (h.trans zero_coordinates.symm)) (fun h => point.injective h)
  · intro hg
    apply Equiv.ext
    intro B
    obtain ⟨i,rfl⟩ := NaturalQuotient.partNumbering.surjective B
    apply Subtype.ext
    exact sourceCore_fixes_tetrad g.val.val hg i
end Native


end Sporadic.Mathieu.M22ChapterH.Quintet.Structure
