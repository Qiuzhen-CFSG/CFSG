module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreSeedCoordinates

/-!
# Compatibility of the full HS core action with its doubled seed

The matrix action on C₄³ and the original seed action agree on every doubled
binary vector in the same coordinates. This supplies the binary reductions
of the actual matrices used in the dual-plane lift construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The whole-core matrix action restricts to the literal seed action in
the compatible doubled coordinates. -/
theorem TypeAt.coreMatrixAction_on_seed (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (g : normalizer (V : Set G)) (v : Multiplicative (Fin 3 → ZMod 2)) :
    (h.coreMatrixAction e g).mulVec (fun i => binaryDouble (v.toAdd i)) =
      fun i => binaryDouble
        ((h.seedCoordinates e (V.normalizerMonoidHom g ((h.seedCoordinates e).symm v))).toAdd i) := by
  let q := e.symm (Multiplicative.ofAdd (fun i => binaryDouble (v.toAdd i)))
  let w := V.normalizerMonoidHom g ((h.seedCoordinates e).symm v)
  have hqv : ((q : normalizer (V : Set G)) : G) = ((h.seedCoordinates e).symm v : G) :=
    (h.seedCoordinates_symm_apply e v).symm
  have hw : (w : G) =
      ((e.symm (Multiplicative.ofAdd (fun i => binaryDouble ((h.seedCoordinates e w).toAdd i))) :
        normalizer (V : Set G)) : G) := by
    simpa only [MulEquiv.symm_apply_apply] using
      h.seedCoordinates_symm_apply e (h.seedCoordinates e w)
  have hq : MulAut.conjNormal g q =
      e.symm (Multiplicative.ofAdd (fun i => binaryDouble ((h.seedCoordinates e w).toAdd i))) := by
    apply Subtype.ext
    apply Subtype.ext
    change (g : G) * ((q : normalizer (V : Set G)) : G) * (g : G)⁻¹ = _
    rw [hqv]
    exact hw
  have hh := h.coreMatrixAction_apply e g q
  rw [hq, e.apply_symm_apply] at hh
  simpa only [q, e.apply_symm_apply, toAdd_ofAdd, w] using hh

end CFSG.Quasithin.HigmanSims
