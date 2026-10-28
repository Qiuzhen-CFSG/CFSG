module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Existence
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Normalization of the marked source flag by the Cartan

Conjugating a field subspace by the marked action of an element of L
conjugates its literal preimage in V. The source normalizer N_L(T_L)
preserves T intersect L, so it permutes the field subspaces invariant
under that intersection, preserving their dimensions. Uniqueness for
the inner Sylow therefore fixes each of the three flag spaces. Every
source Cartan normalizes the flag, and Hall existence supplies one.

Only the precise inner-Sylow uniqueness premise remains explicit;
its marked-model producers and discharge belong to the flag assembly.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
the Chapter 11 setup and the normalization preceding 11.1.2,
printed pp.759--761.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
namespace Coordinates
variable (c : Coordinates D F)

/-- The field-linear equivalence associated to the actual marked action. -/
def modelLinearEquiv (g : c.ModelGroup) : c.Space ≃ₗ[F.Carrier] c.Space :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (c.modelAction.asGroupHom g)

/-- Field-subspace conjugation matches conjugation of the original quotient preimage. -/
theorem preimage_map_action (l : L) (U : Submodule F.Carrier c.Space) :
    c.preimage (U.map (c.modelAction (c.quotientMap l))) =
      (c.preimage U).map (MulAut.conj (l : G)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have hx : x ∈ V ↔ (MulAut.conj (l : G)).symm x ∈ V := by
    simpa only [MulAut.conj_symm_apply, inv_inv, SetLike.mem_coe] using
      (D.normalizes (L.inv_mem l.property) x)
  by_cases hxV : x ∈ V
  · let v : V := ⟨x, hxV⟩
    let w := V.normalizerMonoidHom (inclusion D.normalizes l⁻¹) v
    have hw : (MulAut.conj (l : G)).symm x = (w : G) := by
      change (MulAut.conj (l : G)).symm x = (l : G)⁻¹ * x * ((l : G)⁻¹)⁻¹
      rw [MulAut.conj_symm_apply, inv_inv]
    rw [hw, c.mem_preimage _ v, c.mem_preimage U w]
    change (c.projection v).toAdd ∈ U.map (c.modelLinearEquiv (c.quotientMap l)).toLinearMap ↔ _
    rw [Submodule.mem_map_equiv]
    have he : (c.modelLinearEquiv (c.quotientMap l)).symm (c.projection v).toAdd =
        (c.projection w).toAdd := by
      rw [c.projection_component_conjugation, map_inv]
      rfl
    rw [he]
    rfl
  · constructor
    · intro h
      exact (hxV (D.centralQuotientPreimage_le _ h)).elim
    · intro h
      exact (hxV (hx.mpr (D.centralQuotientPreimage_le _ h))).elim

end Coordinates

namespace InvariantFlag
variable {c : Coordinates D F} (f : InvariantFlag c)

/-- Uniqueness under T intersect L, the inner Sylow used by the source Cartan. -/
def IsInnerUnique : Prop :=
  ∀ (i : Fin 3) (U : Submodule F.Carrier c.Space),
    Module.finrank F.Carrier U = i.val + 1 →
    (T : Subgroup G) ⊓ L ≤ normalizer (c.preimage U : Set G) → U = f.space i

/-- The whole source normalizer fixes every member of an inner-unique flag. -/
theorem normalizer_le_flag_normalizer (hu : f.IsInnerUnique) (i : Fin 3) :
    cartanNormalizer T L ≤ normalizer (f.Vi i : Set G) := by
  intro x hx
  let l : L := ⟨x, hx.1⟩
  let U := (f.space i).map (c.modelAction (c.quotientMap l))
  have hdim : Module.finrank F.Carrier U = i.val + 1 :=
    ((c.modelLinearEquiv (c.quotientMap l)).finrank_map_eq (f.space i)).trans (f.dimension i)
  have hP : ((T : Subgroup G) ⊓ L).map (MulAut.conj x).toMonoidHom =
      (T : Subgroup G) ⊓ L := mem_normalizer_iff_map_conj_eq.mp
        (cartanNormalizer_normalizes_intersection hx)
  have hU : (T : Subgroup G) ⊓ L ≤ normalizer (c.preimage U : Set G) := by
    rw [c.preimage_map_action, ← hP]
    exact (map_mono (inf_le_left.trans (f.invariant i))).trans_eq
      (map_equiv_normalizer_eq _ (MulAut.conj x))
  have he := hu i U hdim hU
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (c.preimage (f.space i)).map (MulAut.conj x).toMonoidHom = _
  rw [← c.preimage_map_action l]
  exact congrArg c.preimage he

/-- Every actual source Cartan normalizes each literal flag preimage. -/
theorem cartan_normalizes {X : Subgroup G} (hu : f.IsInnerUnique)
    (hX : IsCartan T L X) (i : Fin 3) : X ≤ normalizer (f.Vi i : Set G) :=
  hX.1.trans (f.normalizer_le_flag_normalizer hu i)

/-- Hall existence and inner uniqueness give the original flag-normalizing Cartan. -/
theorem exists_normalizing_cartan (hu : f.IsInnerUnique) :
    ∃ X : Subgroup G, IsCartan T L X ∧ ∀ i, X ≤ normalizer (f.Vi i : Set G) := by
  obtain ⟨X,hX⟩ := exists_cartan D
  exact ⟨X,hX,f.cartan_normalizes hu hX⟩
end InvariantFlag
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
