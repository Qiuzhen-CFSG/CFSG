module

public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.Representation.CubicFixedSpace

/-!
# A cubic fixer for the binary derived G₂ natural module

Two positive-root products in the actual derived Sylow force its fixed
vectors onto the first of the six off-diagonal octonion coordinates.
The products are `C(1)D(1)` (the existing commutator `binaryA`) and `C(1)F(1)`;
the long-root quotient proves the second belongs to the derived group.
The nonidentity cubic `E(1)R` fixes that coordinate line and itself belongs
to G₂(2)′. Sylow conjugacy supplies the corresponding cubic for every Sylow.

All membership statements use the genuine derived subgroup and its order-32
Sylow, whose ambient image is the intersection with the order-64 positive-root
subgroup. These are fixed vectors in the natural representation, independently
of pointwise automorphism fixers of the Sylow as a group.

This is the binary G₂ module calculation used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
15.4.18, printed p.1163, with the natural section in B.4.2(4), p.86,
and its extensions in B.5.1, p.99. Root and Weyl coordinates are inherited
from the licensed ATLAS ports in the imports; no additional ATLAS source
is copied here.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.Natural Atlas.G2.BinaryCore
open Atlas.G2.BinaryParabolicPair

namespace Atlas.G2.Natural.BinarySylowFixedSpace

private theorem binaryA_eq_roots :
    (binaryA (ZMod 2)).val = rootC 1 * rootD 1 := by
  apply Atlas.Algebra.MultiplicativeLinearAut.ext
  intro x
  change (binaryA (ZMod 2)).val.val x = (rootC (1 : ZMod 2) * rootD 1).val x
  rw [binaryA_apply]
  ext i
  fin_cases i <;>
    simp [rootC, rootD, rootCEquiv, rootDEquiv, rootCLinear, rootDLinear,
      rootCApply, rootDApply, sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf
  all_goals reduce_mod_char!

private theorem rootCF_mem_derived :
    rootC (1 : ZMod 2) * rootF 1 ∈ DerivedModel := by
  rw [DerivedModel, commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (rootC 1 * rootF 1) = 1
  rw [map_mul, BinaryException.project_C_eq_D, BinaryException.project_D_eq_F,
    ← map_mul, rootF_add]
  rw [show (1 : ZMod 2) + 1 = 0 by decide, rootF_zero, map_one]

private def rootCF : DerivedModel := ⟨rootC 1 * rootF 1, rootCF_mem_derived⟩

private theorem mem_derivedSylow {g : DerivedModel} (hg : g.val ∈ unipotent) :
    g ∈ derivedSylow := by
  have hm : g.val ∈ (derivedSylow : Subgroup DerivedModel).map DerivedModel.subtype := by
    rw [derivedSylow_map_subtype]
    exact ⟨hg, g.property⟩
  obtain ⟨x, hx, he⟩ := hm
  exact (Subtype.ext he : x = g) ▸ hx

private theorem binaryA_mem : binaryA (ZMod 2) ∈ derivedSylow := by
  apply mem_derivedSylow
  rw [binaryA_eq_roots]
  apply unipotent.mul_mem <;> apply Subgroup.subset_closure <;> simp

private theorem rootCF_mem : rootCF ∈ derivedSylow := by
  apply mem_derivedSylow
  apply unipotent.mul_mem <;> apply Subgroup.subset_closure <;> simp

private theorem coordinates_rootCF (v : Space (ZMod 2)) :
    binaryCoordinates (ZMod 2) (derivedAction (ZMod 2) rootCF v) =
      ![binaryCoordinates (ZMod 2) v 0 + binaryCoordinates (ZMod 2) v 1 + binaryCoordinates (ZMod 2) v 5,
        binaryCoordinates (ZMod 2) v 1 + binaryCoordinates (ZMod 2) v 3,
        binaryCoordinates (ZMod 2) v 2 + binaryCoordinates (ZMod 2) v 3 + binaryCoordinates (ZMod 2) v 4 + binaryCoordinates (ZMod 2) v 5,
        binaryCoordinates (ZMod 2) v 3,
        binaryCoordinates (ZMod 2) v 4 + binaryCoordinates (ZMod 2) v 5,
        binaryCoordinates (ZMod 2) v 5] := by
  obtain ⟨x, rfl⟩ := mk_surjective (ZMod 2) v
  have ht : x.val 3 + x.val 4 = 0 := x.property
  rw [derivedAction_mk]
  change binaryOffDiagonal (ZMod 2) ((rootC (1 : ZMod 2) * rootF 1).val x.val) = _
  ext i
  fin_cases i <;>
    simp [binaryOffDiagonal, binaryCoordinates_mk, rootC, rootF, rootCEquiv,
      rootFEquiv, rootCLinear, rootFLinear, rootCApply, rootFApply,
      sub_eq_add_neg, CharTwo.neg_eq] <;> linear_combination (norm := (ring_nf <;> reduce_mod_char!)) ht

private theorem coordinates_movingActor (v : Space (ZMod 2)) :
    binaryCoordinates (ZMod 2) (action (ZMod 2) movingActor v) =
      ![binaryCoordinates (ZMod 2) v 0,
        binaryCoordinates (ZMod 2) v 1 + binaryCoordinates (ZMod 2) v 2,
        binaryCoordinates (ZMod 2) v 1,
        binaryCoordinates (ZMod 2) v 3 + binaryCoordinates (ZMod 2) v 4,
        binaryCoordinates (ZMod 2) v 3,
        binaryCoordinates (ZMod 2) v 5] := by
  obtain ⟨x, rfl⟩ := mk_surjective (ZMod 2) v
  rw [action_mk]
  change binaryOffDiagonal (ZMod 2) (movingActor.val x.val) = _
  ext i
  fin_cases i <;>
    simp [binaryOffDiagonal, binaryCoordinates_mk, movingActor, weylR, weylREquiv,
      weylRLinear, weylRApply, rootE, rootEEquiv, rootELinear, rootEApply,
      sub_eq_add_neg, CharTwo.neg_eq, add_comm]

/-- Every vector fixed by the actual derived Sylow is supported on the first
of the six off-diagonal octonion coordinates. -/
theorem derivedSylow_fixed_coordinates (v : Space (ZMod 2))
    (hv : v ∈ fixedSpace (g2DerivedNatural (ZMod 2))
      (derivedSylow : Subgroup DerivedModel)) :
    binaryCoordinates (ZMod 2) v = ![binaryCoordinates (ZMod 2) v 0, 0, 0, 0, 0, 0] := by
  have h := binaryCoordinates_binaryA (ZMod 2) v
  have ha : derivedAction (ZMod 2) (binaryA (ZMod 2)) v = v := hv ⟨_, binaryA_mem⟩
  rw [ha] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3
  have h4 : binaryCoordinates (ZMod 2) v 4 = 0 := by linear_combination -h2
  have h5 : binaryCoordinates (ZMod 2) v 5 = 0 := by linear_combination -h3
  have h2' : binaryCoordinates (ZMod 2) v 2 = 0 := by linear_combination -h0 - h5
  have h3' : binaryCoordinates (ZMod 2) v 3 = 0 := by linear_combination -h1 - h4 - h5
  have hc := coordinates_rootCF v
  have hb : derivedAction (ZMod 2) rootCF v = v := hv ⟨_, rootCF_mem⟩
  rw [hb] at hc
  have hc0 := congrFun hc 0
  simp only [Matrix.cons_val_zero] at hc0
  have h1' : binaryCoordinates (ZMod 2) v 1 = 0 := by linear_combination -hc0 - h5
  ext i
  fin_cases i <;> simp [h1', h2', h3', h4, h5]

/-- The long-root cubic fixes the fixed space of the genuine order-32 Sylow. -/
theorem movingActor_fixes_derivedSylow (v : Space (ZMod 2))
    (hv : v ∈ fixedSpace (g2DerivedNatural (ZMod 2))
      (derivedSylow : Subgroup DerivedModel)) :
    g2DerivedNatural (ZMod 2) ⟨movingActor, movingActor_mem_derived⟩ v = v := by
  apply binaryCoordinates_injective (ZMod 2)
  change binaryCoordinates (ZMod 2) (action (ZMod 2) movingActor v) = _
  rw [coordinates_movingActor, derivedSylow_fixed_coordinates v hv]
  rfl

/-- Every Sylow of G₂(2)′ has a nonidentity cubic fixing its natural fixed space. -/
theorem derived_sylow_enlargement (S : Sylow 2 DerivedModel) :
    ∃ d : DerivedModel, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (g2DerivedNatural (ZMod 2)) (S : Subgroup DerivedModel),
        g2DerivedNatural (ZMod 2) d v = v := by
  apply sylow_fixedSpace_enlargement_of_cubic (g2DerivedNatural (ZMod 2))
    (derivedSylow : Subgroup DerivedModel) derivedSylow.isPGroup'
    ⟨movingActor, movingActor_mem_derived⟩ (Subtype.ext movingActor_cube) _
    movingActor_fixes_derivedSylow S
  intro he
  have he' : movingActor = 1 := congrArg Subtype.val he
  apply movingActor_moves
  simp [he']

end Atlas.G2.Natural.BinarySylowFixedSpace
