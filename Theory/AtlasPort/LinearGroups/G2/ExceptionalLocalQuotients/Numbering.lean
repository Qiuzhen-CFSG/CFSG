module
public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients

/-!
# Numbering the derived binary G₂ parabolics by their Sylow center

Commuting with two specified elements of the 32-row overlap forces its
row to commute with the cubic of the first parabolic. Word induction then
proves commutation with that whole parabolic. The checked realization and
literal subgroup inclusions transport this to the original derived pair.
This uses the entire cyclic center, including its order-four elements,
as required by the numbering convention before F.1.12(I).

Source: Aschbacher--Smith, F.1.12, printed pp.262--263. The inherited
root-word tables and their realization carry the ATLAS attribution in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.ExceptionalLocalQuotients
open LieAutomorphismExtensions LieAutomorphismExtensions.BinaryAmalgamBound
open BinaryParabolicPair LieParabolicSetup

private theorem center_rows : ∀ i : Fin 32,
    leftTable.mul (leftTable.overlap i) (leftTable.overlap 1) =
      leftTable.mul (leftTable.overlap 1) (leftTable.overlap i) →
    leftTable.mul (leftTable.overlap i) (leftTable.overlap 2) =
      leftTable.mul (leftTable.overlap 2) (leftTable.overlap i) →
    leftTable.mul (leftTable.overlap i) 2 =
      leftTable.mul 2 (leftTable.overlap i) := by
  decide +kernel

private theorem center_of_word_rows {G B : Type*} [Group G] [Group B]
    (T : WordTable) (hT : T.Valid) (E : T.Realization G)
    (f : B →* G) (b : Fin 32 ≃ B)
    (ho : ∀ j, E.equiv (T.overlap j) = f (b j))
    (hr : ∀ i : Fin 32,
      T.mul (T.overlap i) (T.overlap 1) = T.mul (T.overlap 1) (T.overlap i) →
      T.mul (T.overlap i) (T.overlap 2) = T.mul (T.overlap 2) (T.overlap i) →
      T.mul (T.overlap i) 2 = T.mul 2 (T.overlap i))
    (z : Subgroup.center B) (g : G) : f z.val * g = g * f z.val := by
  obtain ⟨i,hi⟩ := b.surjective z.val
  obtain ⟨k,rfl⟩ := E.equiv.surjective g
  have hc (j : Fin 32) :
      T.mul (T.overlap i) (T.overlap j) = T.mul (T.overlap j) (T.overlap i) := by
    apply E.equiv.injective
    rw [E.mul_eq, E.mul_eq, ho, ho, hi]
    simpa only [map_mul] using
      (congrArg f (Subgroup.mem_center_iff.mp z.prop (b j))).symm
  have h₁ : Commute (f z.val) (E.equiv 1) := by
    rw [← hT.common, ho]
    exact (Commute.symm (show Commute (b 1) z.val from
      Subgroup.mem_center_iff.mp z.prop (b 1))).map f
  have h₂ : Commute (f z.val) (E.equiv 2) := by
    change f z.val * E.equiv 2 = E.equiv 2 * f z.val
    rw [← hi, ← ho, ← E.mul_eq, ← E.mul_eq, hr i (hc 1) (hc 2)]
  have hw (w : List Bool) :
      Commute (f z.val) (groupWord (E.equiv 1) (E.equiv 2) w) := by
    induction w with
    | nil => exact Commute.one_right _
    | cons c w ih =>
      cases c
      · exact h₁.mul_right ih
      · exact h₂.mul_right ih
  rw [← E.word_eq hT k]
  exact (hw _).eq

/-- The center of the entire overlap is centralized by the first parabolic. -/
theorem first_centralizes_overlap_center (z : Subgroup.center binaryOverlap) (g : BinaryLeft) :
    binaryAmalgam.left z.val * g = g * binaryAmalgam.left z.val :=
  center_of_word_rows leftTable left_valid binaryConcreteRealization.left
    binaryAmalgam.left binaryConcreteRealization.middle binaryConcreteRealization.left_overlap
    center_rows z g

/-- The overlap in the automorphism calculation is the same marked Sylow subgroup. -/
theorem overlap_eq_derivedSylow : binaryOverlap = (derivedSylow : Subgroup DerivedModel) := by
  rw [binaryOverlap_eq, derivedSylow_eq]

/-- The source's numbering uses the full center, including its elements of order four. -/
theorem derivedFirst_centralizes_sylow_center
    (z : Subgroup.center (derivedSylow : Subgroup DerivedModel)) (g : derivedFirst) :
    z.val.val * g.val = g.val * z.val.val := by
  let b : binaryOverlap := ⟨z.val.val, overlap_eq_derivedSylow.symm ▸ z.val.prop⟩
  have hb : b ∈ Subgroup.center binaryOverlap := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact congrArg (fun y : (derivedSylow : Subgroup DerivedModel) => y.val)
      (Subgroup.mem_center_iff.mp z.prop
      ⟨x.val, overlap_eq_derivedSylow ▸ x.prop⟩)
  have hg : g.val ∈ BinaryLeft := by
    change g.val.val ∈ parabolic₁ (F := ZMod 2)
    rw [parabolic₁_binary]
    exact g.prop
  exact congrArg (fun x : BinaryLeft => x.val)
    (first_centralizes_overlap_center ⟨b,hb⟩ ⟨g.val,hg⟩)

end Atlas.G2.ExceptionalLocalQuotients
