module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Model
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transport of the literal natural-module geometry

Conjugating matrix actors intertwines their action with the natural vector
map. Consequently pointwise fixed spaces and the fixed spaces of full
intrinsic two-cores are transported by that same map. Invariant subgroups
pull back along the inverse vector map. These facts preserve the action
and ambient subgroup conventions of the fixed-value construction.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (1.7)(i), p.847.
-/

@[expose] public section
open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof

theorem action_mul (a b : SL) (v : VectorGroup) :
    vectorAction (a * b) v = vectorAction a (vectorAction b v) := by
  change (a.val * b.val).mulVec v.toAdd = a.val.mulVec (b.val.mulVec v.toAdd)
  exact (Matrix.mulVec_mulVec _ _ _).symm
@[simp] theorem action_one (v : VectorGroup) : vectorAction 1 v = v := by
  change (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v.toAdd = v.toAdd
  simp
@[simp] theorem action_inv_cancel (a : SL) (v : VectorGroup) :
    vectorAction a (vectorAction a⁻¹ v) = v := by rw [← action_mul, mul_inv_cancel, action_one]
@[simp] theorem action_inv_cancel' (a : SL) (v : VectorGroup) :
    vectorAction a⁻¹ (vectorAction a v) = v := by rw [← action_mul, inv_mul_cancel, action_one]

theorem action_conj (g a : SL) (v : VectorGroup) :
    vectorAction (MulAut.conj g a) (vectorAction g v) =
      vectorAction g (vectorAction a v) := by
  simp only [MulAut.conj_apply, action_mul, action_inv_cancel']

theorem map_action_mul (a b : SL) (A : Subgroup VectorGroup) :
    (A.map (vectorAction b).toMonoidHom).map (vectorAction a).toMonoidHom =
      A.map (vectorAction (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  apply congrArg (fun f : VectorGroup →* VectorGroup => A.map f)
  apply MonoidHom.ext
  intro v
  exact (action_mul a b v).symm
@[simp] theorem map_action_one (A : Subgroup VectorGroup) :
    A.map (vectorAction 1).toMonoidHom = A := by
  have he : (vectorAction (1 : SL)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro v
    exact action_one v
  rw [he, Subgroup.map_id]
@[simp] theorem map_action_cancel (a : SL) (A : Subgroup VectorGroup) :
    (A.map (vectorAction a⁻¹).toMonoidHom).map (vectorAction a).toMonoidHom = A := by
  rw [map_action_mul, mul_inv_cancel, map_action_one]
@[simp] theorem map_action_cancel' (a : SL) (A : Subgroup VectorGroup) :
    (A.map (vectorAction a).toMonoidHom).map (vectorAction a⁻¹).toMonoidHom = A := by
  rw [map_action_mul, inv_mul_cancel, map_action_one]

theorem map_action_conj (g a : SL) (A : Subgroup VectorGroup) :
    (A.map (vectorAction g).toMonoidHom).map (vectorAction (MulAut.conj g a)).toMonoidHom =
      (A.map (vectorAction a).toMonoidHom).map (vectorAction g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : VectorGroup →* VectorGroup => A.map f)
  apply MonoidHom.ext
  intro v
  exact action_conj g a v

theorem fixedSpace_conj (g : SL) (P : Subgroup SL) :
    fixedSpace (P.map (MulAut.conj g).toMonoidHom) =
      (fixedSpace P).map (vectorAction g).toMonoidHom := by
  ext v
  obtain ⟨v, rfl⟩ := (vectorAction g).surjective v
  constructor
  · intro h
    refine ⟨v, ?_, rfl⟩
    intro a ha
    apply (vectorAction g).injective
    rw [← action_conj]
    exact h _ (mem_map_of_mem _ ha)
  · rintro ⟨w, hw, he⟩
    have hv : w = v := (vectorAction g).injective he
    subst w
    intro a ha
    obtain ⟨a, ha, rfl⟩ := ha
    change vectorAction (MulAut.conj g a) (vectorAction g v) = vectorAction g v
    rw [action_conj, hw a ha]

theorem values_eq_core (σ : MulAut SL) (g : SL) (i : Bool) :
    modelValues σ g i = fixedSpace ((markedParabolic σ g i).pCoreIn 2) := by
  unfold modelValues markedParabolic
  rw [← Subgroup.map_pCoreIn_of_injective 2 _ _ σ.injective]
  rfl

theorem core_fixed_conj (g : SL) (P : Subgroup SL) :
    fixedSpace ((P.map (MulAut.conj g).toMonoidHom).pCoreIn 2) =
      (fixedSpace (P.pCoreIn 2)).map (vectorAction g).toMonoidHom := by
  rw [← Subgroup.map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective, fixedSpace_conj]

theorem invariant_pullback (g : SL) (P : Subgroup SL) (A : Subgroup VectorGroup)
    (hi : ∀ a ∈ P.map (MulAut.conj g).toMonoidHom,
      A.map (vectorAction a).toMonoidHom = A) :
    ∀ a ∈ P, (A.map (vectorAction g⁻¹).toMonoidHom).map (vectorAction a).toMonoidHom =
      A.map (vectorAction g⁻¹).toMonoidHom := by
  intro a ha
  apply Subgroup.map_injective (f := (vectorAction g).toMonoidHom) (vectorAction g).injective
  rw [← map_action_conj g a (A.map (vectorAction g⁻¹).toMonoidHom), map_action_cancel]
  exact hi _ (mem_map_of_mem _ ha)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
