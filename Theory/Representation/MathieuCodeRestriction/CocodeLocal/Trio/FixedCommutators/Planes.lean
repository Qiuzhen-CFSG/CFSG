module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Translations
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Geometry
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The affine-plane three-space in the standard trio cocode

A linear coordinate function on the first octad, extended by zero, is an
even word. Nonzero such words have weight four, so the Golay minimum distance
makes their cocode map injective. Its range is three-dimensional and lies
in the pair space. Every pure translation changes a plane word only by a
multiple of the octad word, which is Golay. Thus this three-space is fixed
by the intrinsic two-core. The reverse fixed-space inclusion and the full
linear action are not asserted here.

Source: Aschbacher–Smith, H.15.6(1–2), printed p.401. The map uses the
native standard-trio affine coordinates, with no assumed flag or action image.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open Representation.BinaryOffender
open scoped BigOperators Pointwise
namespace MathieuCode.TrioCalculation
noncomputable section

/-- Linear coordinate functions on octad zero, extended by zero to the other octads. -/
def standardPlaneWord : Vector →ₗ[ZMod 2] Full where
  toFun a x := if (coordinates x).1 = 0 then ∑ k, a k * (coordinates x).2 k else 0
  map_add' a b := by
    funext x
    by_cases hx : (coordinates x).1 = 0 <;>
      simp [hx, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext x
    by_cases hx : (coordinates x).1 = 0 <;>
      simp [hx, Finset.mul_sum, mul_assoc]

lemma standardPlaneWord_point (a : Vector) (i : Fin 3) (v : Vector) :
    standardPlaneWord a (point (i,v)) = if i = 0 then ∑ k, a k * v k else 0 := by
  simp [standardPlaneWord, coordinates_point]

lemma standardPlaneWord_mem_core (a : Vector) : standardPlaneWord a ∈ Core := by
  change (∑ x, standardPlaneWord a x) = 0
  revert a
  decide +kernel

/-- The affine-plane words as elements of the even core. -/
def standardPlaneCore : Vector →ₗ[ZMod 2] Core :=
  standardPlaneWord.codRestrict Core standardPlaneWord_mem_core

/-- The geometric three-space map into the actual cocode. -/
def standardPlaneMap : Vector →ₗ[ZMod 2] Cocode := codeInCore.mkQ.comp standardPlaneCore

lemma standardPlaneWord_weight (a : Vector) (ha : a ≠ 0) :
    hammingNorm (standardPlaneWord a) = 4 := by
  revert a
  decide +kernel

lemma standardPlaneMap_injective : Function.Injective standardPlaneMap := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm ?_ bot_le
  intro a ha
  change a = 0
  by_contra hne
  have hg : standardPlaneWord a ∈ golay :=
    (Submodule.Quotient.mk_eq_zero codeInCore).mp ha
  have hw := standardPlaneWord_weight a hne
  have hn : standardPlaneWord a ≠ 0 := by
    intro h
    rw [h, hammingNorm_zero] at hw
    omega
  have hmin := native_golay_minimum hg hn
  omega

lemma finrank_standardPlaneMap_range :
    Module.finrank (ZMod 2) standardPlaneMap.range = 3 := by
  rw [LinearMap.finrank_range_of_inj standardPlaneMap_injective]
  simp

lemma standardPlaneCore_mem_pairCore (a : Vector) :
    standardPlaneCore a ∈ pairCore standardTrio := by
  rw [mem_pairCore_iff]
  intro B hB
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
  change (∑ x ∈ standardTrioOctad i, standardPlaneWord a x) = 0
  revert a i
  decide +kernel

lemma standardPlaneMap_range_le_pairSpace :
    standardPlaneMap.range ≤ ⨆ B ∈ standardTrio.parts, supportedPairSpace B := by
  rw [← pairCore_quotient_image]
  rintro _ ⟨a,rfl⟩
  exact Submodule.mem_map_of_mem (standardPlaneCore_mem_pairCore a)

lemma standardPlaneMap_fixed (a : Vector) (g : trioStabilizer standardTrio)
    (hg : g ∈ pCore 2 (trioStabilizer standardTrio)) :
    cocodeRepresentation g.val (standardPlaneMap a) = standardPlaneMap a := by
  obtain ⟨t,ht⟩ := (mem_standardTwoCore_iff g⁻¹).mp ((pCore 2 _).inv_mem hg)
  change codeInCore.mkQ (coreRepresentation g.val (standardPlaneCore a)) =
    codeInCore.mkQ (standardPlaneCore a)
  apply (Submodule.Quotient.eq codeInCore).mpr
  change (coreRepresentation g.val (standardPlaneCore a)).val -
    (standardPlaneCore a).val ∈ golay
  have he : (coreRepresentation g.val (standardPlaneCore a)).val -
      (standardPlaneCore a).val = (∑ k, a k * t 0 k) • wordOfSet (standardTrioOctad 0) := by
    funext x
    obtain ⟨⟨i,v⟩,rfl⟩ := point.surjective x
    change standardPlaneWord a ((g⁻¹).val.val (point (i,v))) -
      standardPlaneWord a (point (i,v)) = _
    rw [ht, standardPlaneWord_point, standardPlaneWord_point]
    simp only [Pi.smul_apply, smul_eq_mul, wordOfSet, point_mem_octad_iff]
    by_cases hi : i = 0
    · subst i
      simp [mul_add, Finset.sum_add_distrib]
    · simp [hi]
  rw [he]
  apply golay.smul_mem
  rw [golay_eq_span_octads]
  exact Submodule.subset_span ⟨standardTrioOctad 0, standardTrioOctad_mem 0, rfl⟩

lemma standardPlaneMap_range_le_fixedSpace :
    standardPlaneMap.range ≤ fixedSpace cocodeRepresentation
      ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype) := by
  rintro _ ⟨a,rfl⟩ ⟨_,g,hg,rfl⟩
  exact standardPlaneMap_fixed a g hg

end
end MathieuCode.TrioCalculation
