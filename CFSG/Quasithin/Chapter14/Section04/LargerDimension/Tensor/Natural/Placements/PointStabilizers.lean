module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Quotients
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
/-!
# Four-point coordinates at the marked Borel point

Restriction to the complement of the specified point identifies its S₅
stabilizer with S₄. Restriction preserves sign, so the even stabilizer is
identified with A₄. The normalizer calculation uses the same point.

Source application: Aschbacher–Smith, Lemma 14.4.10, printed pp.1010–1011.
-/

public section

open Subgroup
open Theory.SpecificGroups.TensorThreeFive
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private def pointHom (i : Fin 5) :
    Equiv.Perm {x : Fin 5 // x ≠ i} →* MulAction.stabilizer S5 i :=
  Equiv.Perm.ofSubtype.codRestrict _ (fun f =>
    Equiv.Perm.ofSubtype_apply_of_not_mem f (not_not_intro rfl))

private theorem pointHom_bijective (i : Fin 5) : Function.Bijective (pointHom i) := by
  constructor
  · intro x y h
    exact Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)
  · intro g
    have hg : g.val i = i := g.property
    have hp : ∀ x : Fin 5, g.val x ≠ i ↔ x ≠ i := by
      intro x
      exact ⟨fun h hx => h (hx ▸ hg),
        fun h hx => h (g.val.injective (hx.trans hg.symm))⟩
    refine ⟨g.val.subtypePerm hp, Subtype.ext ?_⟩
    exact Equiv.Perm.ofSubtype_subtypePerm hp (fun x hx hxi => hx (by simpa [hxi] using hg))

/-- Restrict the point stabilizer to the other four points. -/
noncomputable def pointEquiv (i : Fin 5) : MulAction.stabilizer S5 i ≃* S4 :=
  (MulEquiv.ofBijective (pointHom i) (pointHom_bijective i)).symm.trans
    (Equiv.permCongrHom (Fintype.equivFinOfCardEq (by simp :
      Fintype.card {x : Fin 5 // x ≠ i} = 4)))

/-- The isomorphism to S₄ preserves permutation sign. -/
theorem pointEquiv_sign (i : Fin 5) (g : MulAction.stabilizer S5 i) :
    (pointEquiv i g).sign = g.val.sign := by
  let q := MulEquiv.ofBijective (pointHom i) (pointHom_bijective i)
  have he := congrArg (fun x : MulAction.stabilizer S5 i => x.val.sign) (q.apply_symm_apply g)
  change (Equiv.Perm.ofSubtype (q.symm g)).sign = g.val.sign at he
  rw [Equiv.Perm.sign_ofSubtype] at he
  change (Equiv.permCongrHom _ (q.symm g)).sign = _
  rw [Equiv.permCongrHom_coe, Equiv.Perm.sign_permCongr]
  exact he

/-- Restrict an even point stabilizer to the alternating four-point group. -/
noncomputable def evenPointEquiv (i : Fin 5) :
    (A5 ⊓ MulAction.stabilizer S5 i : Subgroup S5) ≃* A4 := by
  let f : (A5 ⊓ MulAction.stabilizer S5 i : Subgroup S5) →* A4 :=
    { toFun := fun g => ⟨pointEquiv i ⟨g.val,g.property.2⟩,
        Equiv.Perm.mem_alternatingGroup.mpr ((pointEquiv_sign i _).trans
          (Equiv.Perm.mem_alternatingGroup.mp g.property.1))⟩
      map_one' := by apply Subtype.ext; exact (pointEquiv i).map_one
      map_mul' := fun x y => by apply Subtype.ext; exact (pointEquiv i).map_mul ⟨x.val,x.property.2⟩ ⟨y.val,y.property.2⟩ }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    have hh := (pointEquiv i).injective (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun z : MulAction.stabilizer S5 i => z.val) hh)
  · intro g
    let t := (pointEquiv i).symm g.val
    have ht : t.val ∈ A5 := by
      rw [Equiv.Perm.mem_alternatingGroup, ← pointEquiv_sign i t]
      simpa only [t, MulEquiv.apply_symm_apply] using
        (Equiv.Perm.mem_alternatingGroup.mp g.property)
    refine ⟨⟨t,⟨ht,t.property⟩⟩, Subtype.ext ?_⟩
    exact (pointEquiv i).apply_symm_apply g.val

/-- The even point stabilizer normalizer acts on the remaining four points. -/
noncomputable def evenPointNormalizerEquiv (i : Fin 5) :
    normalizer ((A5 ⊓ MulAction.stabilizer S5 i : Subgroup S5) : Set S5) ≃* S4 :=
  (MulEquiv.subgroupCongr
    (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.even_stabilizer_normalizer i)).trans
    (pointEquiv i)

/-- The intrinsic A₅ point stabilizer has the same four-point coordinates. -/
noncomputable def alternatingPointEquiv (i : Fin 5) : MulAction.stabilizer A5 i ≃* A4 := by
  let e : MulAction.stabilizer A5 i ≃*
      (A5 ⊓ MulAction.stabilizer S5 i : Subgroup S5) :=
    { toFun := fun g => ⟨g.val.val,⟨g.val.property,g.property⟩⟩
      invFun := fun g => ⟨⟨g.val,g.property.1⟩,g.property.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl
      map_mul' := fun x y => rfl }
  exact e.trans (evenPointEquiv i)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
