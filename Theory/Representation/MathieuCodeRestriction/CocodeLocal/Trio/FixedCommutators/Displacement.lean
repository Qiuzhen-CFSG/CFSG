module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Geometry
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Pair-space criteria for cocode commutators

An actor fixing every part of a Golay trio has displacement even on each
part, so its commutator lies in the pair-generated subspace. Conversely,
if it can move any point to any other point in one part while fixing an
external point, the displacement of their cross-part pair gives every
pair generator. Both statements concern the actual even-core/Golay quotient.

Source: Aschbacher–Smith, H.15.6(1), printed p.401.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Representation.BinaryOffender
open scoped BigOperators Pointwise
namespace MathieuCode.TrioCalculation
noncomputable section

lemma commutator_le_pairSpace_of_fixes_parts (T : Trio) (H : Subgroup M24)
    (hH : ∀ g ∈ H, ∀ B ∈ T.parts, g • B = B) :
    subspaceCommutator cocodeRepresentation ⊤ H ≤
      ⨆ B ∈ T.parts, supportedPairSpace B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, q, _, rfl⟩
  obtain ⟨v, rfl⟩ := codeInCore.mkQ_surjective q
  rw [cocodeRepresentation_mk, ← map_sub, ← pairCore_quotient_image]
  apply Submodule.mem_map_of_mem
  rw [mem_pairCore_iff]
  intro B hB
  change (∑ x ∈ B, (v.val (g.val.symm x) - v.val x)) = 0
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  apply Finset.sum_equiv g.val.symm
  · intro x
    have he := hH g hg B hB
    calc
      x ∈ B ↔ x ∈ g • B := by rw [he]
      _ ↔ g.val.symm x ∈ B := by
        change x ∈ g • B ↔ g⁻¹ • x ∈ B
        exact Finset.inv_smul_mem_iff.symm
  · intros; rfl

lemma pairVector_mem_commutator_of_move (H : Subgroup M24)
    (g : M24) (hg : g ∈ H) (x y z : Fin 24)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmove : g • x = y) (hfix : g • z = z) :
    pairVector ⟨{x,y}, by simp [hxy]⟩ ∈ subspaceCommutator cocodeRepresentation ⊤ H := by
  let P : PointPair := ⟨{x,z}, by simp [hxz]⟩
  have he : mapPair g P = (⟨{y,z}, by simp [hyz]⟩ : PointPair) := by
    apply Subtype.ext
    change g • {x,z} = {y,z}
    simp only [Finset.smul_finset_def, Finset.image_insert, Finset.image_singleton,
      hmove, hfix]
  have hd : cocodeRepresentation g (pairVector P) - pairVector P =
      pairVector ⟨{x,y}, by simp [hxy]⟩ := by
    rw [pairVector_equivariant, he]
    change codeInCore.mkQ _ - codeInCore.mkQ _ = codeInCore.mkQ _
    rw [← map_sub]
    apply congrArg codeInCore.mkQ
    apply Subtype.ext
    funext i
    change wordOfSet {y,z} i - wordOfSet {x,z} i = wordOfSet {x,y} i
    by_cases hix : i = x
    · subst i
      simp [wordOfSet, hxy, hxz]
    · by_cases hiy : i = y
      · subst i
        simp [wordOfSet, hix, hyz]
      · by_cases hiz : i = z
        · subst i
          simp [wordOfSet, hix, hiy]
        · simp [wordOfSet, hix, hiy, hiz]
  rw [← hd]
  exact Submodule.subset_span ⟨g, hg, pairVector P, Submodule.mem_top, rfl⟩

lemma pairSpace_le_commutator_of_move (T : Trio) (H : Subgroup M24)
    (hm : ∀ B ∈ T.parts, ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      ∃ g ∈ H, ∃ z, x ≠ z ∧ y ≠ z ∧ g • x = y ∧ g • z = z) :
    (⨆ B ∈ T.parts, supportedPairSpace B) ≤ subspaceCommutator cocodeRepresentation ⊤ H := by
  refine iSup_le fun B => iSup_le fun hB => Submodule.span_le.mpr ?_
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨x,y,hxy,hPxy⟩ := Finset.card_eq_two.mp P.property
  have hx : x ∈ B := hP (by simp [hPxy])
  have hy : y ∈ B := hP (by simp [hPxy])
  obtain ⟨g,hg,z,hxz,hyz,hmove,hfix⟩ := hm B hB x hx y hy hxy
  have he : P = (⟨{x,y}, by simp [hxy]⟩ : PointPair) := Subtype.ext hPxy
  rw [he]
  exact pairVector_mem_commutator_of_move H g hg x y z hxy hxz hyz hmove hfix

end
end MathieuCode.TrioCalculation
