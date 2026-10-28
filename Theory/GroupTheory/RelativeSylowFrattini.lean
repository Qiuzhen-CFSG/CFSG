module
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Exact relative Frattini factorization

If C is normal in W, then W is the product of C and the normalizer in W
of any specified Sylow subgroup of C. The proof restricts to W, applies
Frattini's argument, and maps back through the original subtype maps.
The factors remain inside W; no ambient normality of C is required.

Source application: Aschbacher--Smith 8.3.7, printed p.724, with
C the section centralizer Y_z, W=N_{G_z}(X), and Sylow subgroup S.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Frattini generation inside the specified overgroup, with the original Sylow. -/
theorem relative_sylow_frattini {p : ℕ} [Fact p.Prime]
    (C W : Subgroup G) (hCW : C ≤ W) (hWC : W ≤ normalizer (C : Set G))
    (R : Sylow p C) :
    C ⊔ (W ⊓ normalizer ((R : Subgroup C).map C.subtype : Set G)) = W := by
  let C' := C.subgroupOf W
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hWC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCW).symm
  let R' : Sylow p C' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : ((R' : Subgroup C').map C'.subtype).map W.subtype =
      (R : Subgroup C).map C.subtype := by
    change (((R : Subgroup C).map e.toMonoidHom).map C'.subtype).map W.subtype = _
    rw [map_map, map_map]
    rfl
  have hf := congrArg (fun K : Subgroup W => K.map W.subtype) R'.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, W.range_subtype] at hf
  change _ ⊔ (C.subgroupOf W).map W.subtype = W at hf
  rw [map_subgroupOf_eq_of_le hCW] at hf
  apply le_antisymm (sup_le hCW inf_le_left)
  apply hf.symm.le.trans
  apply sup_le _ le_sup_left
  apply le_trans _ le_sup_right
  apply le_inf (map_subtype_le _)
  have hh := ((R' : Subgroup C').map C'.subtype).le_normalizer_map W.subtype
  rwa [hm] at hh

/-- The same relative factorization as an exact setwise product. -/
theorem relative_sylow_frattini_product {p : ℕ} [Fact p.Prime]
    (C W : Subgroup G) (hCW : C ≤ W) (hWC : W ≤ normalizer (C : Set G))
    (R : Sylow p C) :
    (W : Set G) = (C : Set G) *
      (W ⊓ normalizer ((R : Subgroup C).map C.subtype : Set G) : Subgroup G) := by
  rw [← coe_mul_of_right_le_normalizer_left C _ (inf_le_left.trans hWC),
    relative_sylow_frattini C W hCW hWC R]
end Subgroup
