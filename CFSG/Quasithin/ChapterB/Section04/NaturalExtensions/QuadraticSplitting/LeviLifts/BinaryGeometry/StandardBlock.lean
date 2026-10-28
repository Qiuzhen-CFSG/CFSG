module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry.Models
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Coordinates for the standard binary Levi

Deleting coordinate `j` splits the natural space into its fixed coordinate line
and the hyperplane `x_j = 0`. Restriction to the latter gives the actor
isomorphism with SL_(n-1)(2): the inverse extends a binary linear automorphism
by the identity on the line, using the binary SL/GL comparison. In these
coordinates every elementary root avoiding `j` is the corresponding unit
transvection on the remaining coordinates.

This constructs the `BlockCoordinates` input to
`coordinates_of_block_and_original`; transport from the original natural
submodule is independent of this standard matrix calculation.

Source: Aschbacher–Smith, Lemma B.4.9(1), printed pp.92–93, the fixed line and
natural hyperplane of the Levi complement.
-/

@[expose] public section

open Representation Representation.BinaryOffender Matrix.SpecialLinearGroup
open Representation.OneCohomology.SLHigherNatural
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry
open QuasisimpleSource
namespace StandardBlock
variable {m : ℕ} (j : Fin (m + 1))

/-- The deleted coordinate followed by the remaining coordinates in their original order. -/
private noncomputable def split : (Fin (m + 1) → ZMod 2) ≃ₗ[ZMod 2]
    ZMod 2 × (Fin m → ZMod 2) :=
  { (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ZMod 2) j).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp] private theorem split_apply (v : Fin (m + 1) → ZMod 2) :
    split j v = (v j, fun i => v (j.succAbove i)) := rfl

@[simp] private theorem split_single (c : ZMod 2) : split j (Pi.single j c) = (c, 0) := by
  apply Prod.ext
  · simp
  · funext i
    simp

private theorem line_mem (c : ZMod 2) : (split j).symm (c, 0) ∈ standardLine (m+1) j := by
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  apply (split j).injective
  rw [map_smul, split_single, LinearEquiv.apply_symm_apply]
  simp

private theorem axis_mem (v : Fin m → ZMod 2) :
    (split j).symm (0, v) ∈ standardAxis (m+1) j := by
  exact congrArg Prod.fst ((split j).apply_symm_apply (0,v))

/-- The induced map on the complementary hyperplane, expressed on `Fin m`. -/
private noncomputable def blockEnd (g : standardLevi (m+1) j) :
    Module.End (ZMod 2) (Fin m → ZMod 2) :=
  (LinearMap.snd (ZMod 2) (ZMod 2) (Fin m → ZMod 2)).comp
    ((split j).toLinearMap.comp ((standardAction (m+1) j g).comp
      ((split j).symm.toLinearMap.comp (LinearMap.inr (ZMod 2) (ZMod 2) (Fin m → ZMod 2)))))

private theorem normal_form (g : standardLevi (m+1) j) (c : ZMod 2) (v : Fin m → ZMod 2) :
    split j (standardAction (m+1) j g ((split j).symm (c,v))) =
      (c, blockEnd j g v) := by
  have hd : (split j).symm (c,v) =
      (split j).symm (c,0) + (split j).symm (0,v) := by
    rw [← map_add]
    congr 1
    simp
  have hf := g.property.2.2 _ (line_mem j c)
  have ha := (g.property.1 _).2 (axis_mem j v)
  rw [hd, map_add]
  change split j (specialLinearNatural (m+1) g.val ((split j).symm (c,0)) + _) = _
  rw [hf, map_add, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · change c + (specialLinearNatural (m+1) g.val ((split j).symm (0,v))) j = c
    change (specialLinearNatural (m+1) g.val ((split j).symm (0,v))) j = 0 at ha
    simp [ha]
  · change 0 + blockEnd j g v = blockEnd j g v
    exact zero_add _

private theorem blockEnd_one : blockEnd j 1 = 1 := by
  apply LinearMap.ext
  intro v
  funext i
  change (split j (standardAction (m+1) j 1 ((split j).symm (0,v)))).2 i = v i
  simp

private theorem blockEnd_mul (g h : standardLevi (m+1) j) :
    blockEnd j (g*h) = blockEnd j g * blockEnd j h := by
  apply LinearMap.ext
  intro v
  funext i
  have hh := (split j).symm_apply_apply (standardAction (m+1) j h ((split j).symm (0,v)))
  rw [normal_form] at hh
  change (split j (standardAction (m+1) j (g*h) ((split j).symm (0,v)))).2 i = _
  rw [map_mul, Module.End.mul_apply, ← hh]
  exact congrArg (fun p => p.2 i) (normal_form j g 0 (blockEnd j h v))

/-- Restriction of the actual Levi to its natural hyperplane. -/
private noncomputable def blockHom : standardLevi (m+1) j →* LinearGroup m :=
  { toFun := fun g =>
      { blockEnd j g with
        invFun := blockEnd j g⁻¹
        left_inv := fun v => by
          change (blockEnd j g⁻¹ * blockEnd j g) v = v
          rw [← blockEnd_mul, inv_mul_cancel, blockEnd_one, Module.End.one_apply]
        right_inv := fun v => by
          change (blockEnd j g * blockEnd j g⁻¹) v = v
          rw [← blockEnd_mul, mul_inv_cancel, blockEnd_one, Module.End.one_apply] }
    map_one' := by
      apply LinearEquiv.ext
      intro v
      exact congrArg (fun f : Module.End (ZMod 2) (Fin m → ZMod 2) => f v) (blockEnd_one j)
    map_mul' := fun g h => by
      apply LinearEquiv.ext
      intro v
      exact congrArg (fun f : Module.End (ZMod 2) (Fin m → ZMod 2) => f v) (blockEnd_mul j g h) }

private theorem intertwines (g : standardLevi (m+1) j) (v : Fin (m+1) → ZMod 2) :
    split j (standardAction (m+1) j g v) = ((split j v).1, blockHom j g (split j v).2) := by
  have h := normal_form j g (split j v).1 (split j v).2
  simp only [Prod.mk.eta, LinearEquiv.symm_apply_apply] at h
  exact h

private theorem blockHom_injective : Function.Injective (blockHom j) := by
  intro g h he
  apply Subtype.ext
  apply (slEquivLinear (m+1)).injective
  apply LinearEquiv.ext
  intro v
  apply (split j).injective
  change split j (standardAction (m+1) j g v) = split j (standardAction (m+1) j h v)
  rw [intertwines, intertwines, he]

/-- Extend a linear automorphism by the identity on the fixed coordinate line. -/
private noncomputable def liftLinear (e : LinearGroup m) : LinearGroup (m+1) :=
  (split j).trans (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr e).trans (split j).symm)

private theorem liftLinear_apply (e : LinearGroup m) (v : Fin (m+1) → ZMod 2) :
    split j (liftLinear j e v) = ((split j v).1, e (split j v).2) := by
  simp [liftLinear]

private theorem lift_mem (e : LinearGroup m) :
    (slEquivLinear (m+1)).symm (liftLinear j e) ∈ standardLevi (m+1) j := by
  have he (v : Fin (m+1) → ZMod 2) :
      specialLinearNatural (m+1) ((slEquivLinear (m+1)).symm (liftLinear j e)) v =
        liftLinear j e v := by
    change slEquivLinear (m+1) ((slEquivLinear (m+1)).symm (liftLinear j e)) v = _
    rw [MulEquiv.apply_symm_apply]
  constructor
  · intro v
    change (specialLinearNatural (m+1) _ v) j = 0 ↔ v j = 0
    rw [he]
    have hf := congrArg Prod.fst (liftLinear_apply j e v)
    change liftLinear j e v j = v j at hf
    rw [hf]
  · refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [he]
    apply (split j).injective
    rw [liftLinear_apply, map_smul, split_single]
    simp

private theorem blockHom_surjective : Function.Surjective (blockHom j) := by
  intro e
  refine ⟨⟨(slEquivLinear (m+1)).symm (liftLinear j e), lift_mem j e⟩, ?_⟩
  apply LinearEquiv.ext
  intro v
  change (split j (slEquivLinear (m+1) ((slEquivLinear (m+1)).symm (liftLinear j e))
    ((split j).symm (0,v)))).2 = e v
  rw [MulEquiv.apply_symm_apply, liftLinear_apply, LinearEquiv.apply_symm_apply]

/-- The actor isomorphism, using that every binary invertible matrix has determinant one. -/
private noncomputable def actorEquiv : standardLevi (m+1) j ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) :=
  (MulEquiv.ofBijective (blockHom j) ⟨blockHom_injective j, blockHom_surjective j⟩).trans
    (slEquivLinear m).symm

/-- The actual product decomposition of the natural Levi action. -/
private noncomputable def actionEquiv : ActionEquiv (standardAction (m+1) j) (binaryModel m) where
  groupEquiv := actorEquiv j
  linearEquiv := split j
  intertwines := by
    intro g v
    rw [intertwines]
    change ((split j v).1, blockHom j g (split j v).2) =
      ((split j v).1, slEquivLinear m ((slEquivLinear m).symm (blockHom j g)) (split j v).2)
    rw [MulEquiv.apply_symm_apply]

private theorem actorEquiv_root {u v : Fin m} (huv : u ≠ v) :
    actorEquiv j (standardRoot
      (fun h => huv (Fin.succAbove_right_injective h))
      (Fin.succAbove_ne j u) (Fin.succAbove_ne j v)) = transvection huv 1 := by
  apply (slEquivLinear m).injective
  change slEquivLinear m ((slEquivLinear m).symm (blockHom j _)) = _
  rw [MulEquiv.apply_symm_apply]
  apply LinearEquiv.ext
  intro w
  funext i
  change (specialLinearNatural (m+1) (transvection (fun h => huv (Fin.succAbove_right_injective h)) 1) ((split j).symm (0,w)))
      (j.succAbove i) = specialLinearNatural m (transvection huv 1) w i
  rw [action_transvection, action_transvection]
  have hc (q : Fin m) : (split j).symm (0,w) (j.succAbove q) = w q :=
    congrArg (fun p => p.2 q) ((split j).apply_symm_apply (0,w))
  simp only [Pi.add_apply, one_mul, hc]
  simp [Pi.single_apply]

private theorem roots (a b : Fin (m+1)) (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j) :
    ∃ u v : Fin m, ∃ huv : u ≠ v,
      (actionEquiv j).groupEquiv (standardRoot hab haj hbj) = transvection huv 1 := by
  obtain ⟨u,rfl⟩ := Fin.exists_succAbove_eq haj
  obtain ⟨v,rfl⟩ := Fin.exists_succAbove_eq hbj
  have huv : u ≠ v := fun h => hab (congrArg j.succAbove h)
  exact ⟨u, v, huv, actorEquiv_root j huv⟩

end StandardBlock

/-- Delete the fixed coordinate to identify the literal binary Levi action and its roots. -/
theorem nonempty_blockCoordinates {n : ℕ} (hn : 4 ≤ n) (j : Fin n) :
    Nonempty (BlockCoordinates n j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ⟨⟨StandardBlock.actionEquiv j, StandardBlock.roots j⟩⟩
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry
