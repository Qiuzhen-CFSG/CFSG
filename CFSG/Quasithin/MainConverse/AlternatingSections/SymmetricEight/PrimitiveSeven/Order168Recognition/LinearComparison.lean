module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.Order168Recognition.Generators
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.PSL3Two.Parabolics.Fano
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The two seven-point actions of the binary linear group

The displayed labeling of the nonzero vectors of F₂³ sends a Singer matrix
to the fixed seven-cycle and the transvection I + E₀₁ to the first marked
involution. Six checked matrix words give all elementary transvections;
`Atlas.sl_elementary_induction` therefore identifies the image with the
first seed subgroup. A coordinate permutation conjugates it to the second.
The canonical quotient SL₃(2) → PSL₃(2) supplies the final equivalences.

These are the actual model comparisons needed in the alternating examples'
condition (K) calculation, Aschbacher–Smith, printed pp.4 and 482. The
binary-plane model is the one in `Theory.SpecificGroups.PSL3Two.Parabolics`.
-/

namespace CFSG.Quasithin.MainConverse.Order168Recognition

open Equiv Matrix
private abbrev P := Equiv.Perm (Fin 7)
private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
private abbrev Point := Matrix.PSL3Two.Fano.Point
private abbrev V := Matrix.PSL3Two.Fano.Vector

private def pointAction : SL →* Equiv.Perm Point where
  toFun g :=
    let e := (GeneralLinearGroup.toLin (SpecialLinearGroup.toGL g)).toLinearEquiv
    Equiv.Perm.subtypePerm e.toEquiv (fun v => by simp)
  map_one' := by ext v i; simp
  map_mul' g h := by
    ext v i
    change (((g * h : SL) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.val) i =
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.val)) i
    exact congrFun (Matrix.mulVec_mulVec v.val g.val h.val).symm i

private theorem pointAction_injective : Function.Injective pointAction := by
  intro g h heq
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  by_cases hv : v = 0
  · simp [hv]
  · exact congrArg Subtype.val (Equiv.congr_fun heq ⟨v, hv⟩)

private def vectors : Fin 7 → V := ![
  ![1,0,0], ![1,0,1], ![1,1,1], ![0,1,1],
  ![1,1,0], ![0,0,1], ![0,1,0]]
private def points (i : Fin 7) : Point := ⟨vectors i, (by decide : ∀ j, vectors j ≠ 0) i⟩
private noncomputable def label : Fin 7 ≃ Point := Equiv.ofBijective points (by decide)
private noncomputable def action : SL →* P :=
  (Equiv.permCongrHom label.symm).toMonoidHom.comp pointAction

private theorem action_apply (g : SL) (i : Fin 7) :
    vectors (action g i) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ vectors i := by
  change (label (label.symm (pointAction g (label i)))).val = _
  rw [label.apply_symm_apply]
  rfl

private def C : SL := ⟨!![1,1,0;0,0,1;1,0,0], by decide⟩
private def T : SL := SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1

private abbrev c := cycle
private abbrev t := involution false

private theorem action_C : action C = c := by
  apply Equiv.ext
  intro i
  apply label.injective
  apply Subtype.ext
  change vectors (action C i) = vectors (c i)
  rw [action_apply]
  exact (by decide : ∀ j, (C : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ vectors j = vectors (c j)) i

private theorem action_T : action T = t := by
  apply Equiv.ext
  intro i
  apply label.injective
  apply Subtype.ext
  change vectors (action T i) = vectors (t i)
  rw [action_apply]
  exact (by decide : ∀ j, (T : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ vectors j = vectors (t j)) i

private def elementaryWord (i j : Fin 3) : List Bool :=
  ![![[], [true], [false,false,true,false,false,false,true,false,false,false]],
    ![[false,true,false,false,false,true,false,false,false,false], [],
      [true,false,true,false,true,false,false]],
    ![[false,false,false,false,false,true,false,false],
      [false,false,false,true,false,false,false,true,false,false,true], []]] i j

private theorem elementary_word : ∀ (i j : Fin 3) (hij : i ≠ j),
    SpecialLinearGroup.transvection hij (1 : ZMod 2) = word C T (elementaryWord i j) := by
  decide +kernel

private theorem generation : Subgroup.closure ({C, T} : Set SL) = ⊤ := by
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ Subgroup.closure ({C,T} : Set SL))
    ?_ (fun _ _ => Subgroup.mul_mem _) g
  intro i j hij a
  have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases ha with rfl | rfl
  · simp
  · rw [elementary_word]
    exact word_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) _

private theorem action_injective : Function.Injective action :=
  (Equiv.permCongrHom label.symm).injective.comp pointAction_injective

private theorem range_eq_seed : action.range = seed false := by
  rw [MonoidHom.range_eq_map, ← generation, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, action_C, action_T]
  rfl

private noncomputable def firstEquiv : seed false ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  ((MulEquiv.subgroupCongr range_eq_seed.symm).trans
    (MonoidHom.ofInjective action_injective).symm).trans Matrix.PSL3Two.equiv

private def reflection : P where
  toFun := ![1,0,6,5,4,3,2]
  invFun := ![1,0,6,5,4,3,2]
  left_inv := by decide
  right_inv := by decide

private theorem reflection_cycle : MulAut.conj reflection cycle = cycle⁻¹ := by decide
private theorem reflection_involution : MulAut.conj reflection (involution false) = involution true :=
  by decide

private theorem reflection_seed : (seed false).map (MulAut.conj reflection).toMonoidHom = seed true := by
  rw [seed, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
    reflection_cycle, reflection_involution]
  change Subgroup.closure {cycle⁻¹, involution true} = Subgroup.closure {cycle, involution true}
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simpa only [Set.mem_singleton_iff.mp hx] using
        (show involution true ∈ ({cycle, involution true} : Set P) by simp))
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | hx
    · exact inv_inv cycle ▸ Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simpa only [Set.mem_singleton_iff.mp hx] using
        (show involution true ∈ ({cycle⁻¹, involution true} : Set P) by simp))

/-- Identification of each displayed permutation group with the actual projective matrix group. -/
public noncomputable def modelEquiv (b : Bool) :
    seed b ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) := by
  cases b
  · exact firstEquiv
  · exact (((MulAut.conj reflection).subgroupMap (seed false)).trans
      (MulEquiv.subgroupCongr reflection_seed)).symm.trans firstEquiv

/-- The orders follow from the constructed matrix equivalences. -/
public theorem card_seed (b : Bool) : Nat.card (seed b) = 168 :=
  (Nat.card_congr (modelEquiv b).toEquiv).trans Matrix.PSL3Two.card_PSL

end CFSG.Quasithin.MainConverse.Order168Recognition
