module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.Defs
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarDefs
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
import Mathlib.Tactic.Group

/-!
# Transporting the local centralizer count to the marked star-pair stabilizer

The quotient-to-star equivalence intertwines the actual kernel conjugation
with the pair-label action. Thus every element centralizing the seed fixes
its unordered pair. The converse is unnecessary: the resulting injection
bounds each quotient class by the corresponding star-pair stabilizer class.

The intertwining proof follows the generator argument of
`QuotientCount.Image.Comparison`, using its certified generator equations.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits Simplicity.Max1Fusion.QuotientInvolutions
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private noncomputable def starMap : Local hA hB →* Equiv.Perm (Fin 24) :=
  StarGroup.subtype.comp ((quotientStarEquiv hA hB).toMonoidHom.comp (projection hA hB))

private theorem starMap_x : starMap hA hB (localX hA hB) = starX := by
  exact congrArg Subtype.val (quotientStarEquiv_x hA hB)

private theorem starMap_y : starMap hA hB (localY hA hB) = starY := by
  exact congrArg Subtype.val (quotientStarEquiv_y hA hB)

private abbrev labelValue (i j : Fin 24) : Local hA hB := maskValue hA hB (pairLabel i j)

private def Compatible (g : Local hA hB) : Prop := ∀ i j,
  g * labelValue hA hB i j * g⁻¹ =
    labelValue hA hB (starMap hA hB g i) (starMap hA hB g j)

private theorem compatible_inv (g : Local hA hB) (h : Compatible hA hB g) :
    Compatible hA hB g⁻¹ := by
  intro i j
  have he : g * labelValue hA hB ((starMap hA hB g)⁻¹ i)
      ((starMap hA hB g)⁻¹ j) * g⁻¹ = labelValue hA hB i j := by
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using
      h ((starMap hA hB g)⁻¹ i) ((starMap hA hB g)⁻¹ j)
  rw [map_inv]
  calc
    _ = g⁻¹ * (g * labelValue hA hB ((starMap hA hB g)⁻¹ i)
        ((starMap hA hB g)⁻¹ j) * g⁻¹) * g := by rw [he, inv_inv]
    _ = _ := by group

private theorem compatible_x_inv : Compatible hA hB (localX hA hB)⁻¹ := by
  intro i j
  simp only [inv_inv, map_inv, starMap_x, starX]
  exact (right_conj_mask_x hA hB (pairLabel i j)).trans
    (congrArg (fun m => (maskValue hA hB m : Local hA hB)) (pairLabel_rightX i j).symm)

private theorem compatible_y_inv : Compatible hA hB (localY hA hB)⁻¹ := by
  intro i j
  simp only [inv_inv, map_inv, starMap_y, starY]
  exact (right_conj_mask_y hA hB (pairLabel i j)).trans
    (congrArg (fun m => (maskValue hA hB m : Local hA hB)) (pairLabel_rightY i j).symm)

private theorem compatible (g : Local hA hB) : Compatible hA hB g := by
  have hg : g ∈ Subgroup.closure {localX hA hB, localY hA hB} := by
    rw [localXY_generate]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · simpa only [inv_inv] using compatible_inv hA hB _ (compatible_x_inv hA hB)
    · obtain rfl := Set.mem_singleton_iff.mp hg
      simpa only [inv_inv] using compatible_inv hA hB _ (compatible_y_inv hA hB)
  | one => intro i j; simp [map_one]
  | mul g k _ _ ihg ihk =>
    intro i j
    calc
      _ = g * (k * labelValue hA hB i j * k⁻¹) * g⁻¹ := by group
      _ = _ := by rw [ihk, ihg, map_mul]; rfl
  | inv g _ ih => exact compatible_inv hA hB g ih

private theorem mask_injective {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : (maskValue hA hB m : Local hA hB) = maskValue hA hB n) : m = n := by
  have hb := coordinates_injective hA hB (Subtype.ext h : maskValue hA hB m = maskValue hA hB n)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · exact congrFun hb ⟨j, hj⟩
  · have hp : 2^11 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn hp)]

private theorem centralizer_fixes_pair (g : Local hA hB) (hg : g ∈ centralizer hA hB) :
    pairLabel (starMap hA hB g 0) (starMap hA hB g 1) = 1 := by
  have he := compatible hA hB g 0 1
  change g * (maskValue hA hB 1 : Local hA hB) * g⁻¹ = _ at he
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [maskValue_one, hc, mul_assoc, mul_inv_cancel, mul_one] at he
  apply mask_injective hA hB (pairLabel_lt _ _) (by decide)
  exact he.symm.trans (maskValue_one hA hB).symm

private theorem quotientStarEquiv_base (b : Bool) :
    quotientStarEquiv hA hB (projection hA hB (base hA hB b)) = starBase b := by
  cases b
  · exact quotientStarEquiv_x hA hB
  · exact quotientStarEquiv_xy_seven hA hB

/-- The quotient classes occurring in the actual seed centralizer inject
into the concrete star-group classes fixing the marked unordered pair. -/
theorem quotientClass_card_le_starClass (b : Bool) :
    Nat.card (QuotientClass hA hB b) ≤ Nat.card (StarClass b) := by
  let f : QuotientClass hA hB b → StarClass b := fun q =>
    ⟨quotientStarEquiv hA hB q.val, by
      obtain ⟨g, hg, he⟩ := q.property.1
      rw [← he]
      exact centralizer_fixes_pair hA hB g hg,
      by
        have hc := (quotientStarEquiv hA hB).toMonoidHom.map_isConj q.property.2
        change IsConj (quotientStarEquiv hA hB (projection hA hB (base hA hB b)))
          (quotientStarEquiv hA hB q.val) at hc
        rw [quotientStarEquiv_base] at hc
        exact hc⟩
  apply Nat.card_le_card_of_injective f
  intro q r h
  apply Subtype.ext
  exact (quotientStarEquiv hA hB).injective (congrArg Subtype.val h)

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
