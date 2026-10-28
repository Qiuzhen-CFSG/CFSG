module

public import Theory.Representation.SpecialLinearNatural
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# The six- and eight-dimensional binary S8 constituents

The six-space is the even-coordinate permutation module modulo constants.
The eight-space is the pair induced from the natural A8 = SL4(2) module:
an even permutation acts on the natural and outer-conjugate four-spaces,
and the transposition (0 1) interchanges them. The four parity cases verify
the multiplication law. All group comparisons use the existing attributed
ATLAS exceptional-isomorphism port, not equality of group orders.

These are the actual models in Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, HS paragraph, preprint pp.16--17.
This module does not identify an arbitrary HS module with these factors.
-/

public section
open scoped MatrixGroups
open Representation Representation.BinaryOffender
namespace Representation.SymmetricEightConstituents
noncomputable section
abbrev S8 := Equiv.Perm (Fin 8)
abbrev Four := Fin 4 → ZMod 2
abbrev Eight := Four × Four
abbrev Six := Atlas.Order20160A8.DeletedEight.W

/-- The actual exceptional isomorphism used to mark the natural module. -/
def comparison : alternatingGroup (Fin 8) ≃* SL(4, ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    Atlas.Order20160A8.sl4TwoEquivPSL.symm

/-- Specification of the fixed exceptional marking on the common six-space. -/
theorem comparison_orthogonal (a : alternatingGroup (Fin 8)) :
    Atlas.Order20160A8.DeletedEight.orthogonalHom a.val =
      Atlas.Order20160A8.Exterior.toOrthogonal (comparison a) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two_orthogonal a

/-- The natural four-space, transported through the specified comparison. -/
@[expose] def natural : Representation (ZMod 2) (alternatingGroup (Fin 8)) Four :=
  (specialLinearNatural 4).comp comparison.toMonoidHom

/-- Column-vector coordinates on the marked natural module. -/
theorem natural_apply (a : alternatingGroup (Fin 8)) (v : Four) :
    natural a v = Matrix.mulVec (comparison a).val v := rfl

theorem natural_faithful : Function.Injective natural := by
  intro a b h
  apply comparison.injective
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) Four => f v) h

def transposition : Equiv.Perm (Fin 8) := Equiv.swap 0 1

theorem transposition_eq_swap : transposition = Equiv.swap 0 1 := by rfl

theorem transposition_sq : transposition ^ 2 = 1 := by decide

/-- Conjugation by the odd involution (0 1). -/
def outer : MulAut (alternatingGroup (Fin 8)) where
  toFun a := ⟨transposition * a.val * transposition, by
    change Equiv.Perm.sign _ = 1
    simp only [map_mul, show Equiv.Perm.sign transposition = -1 by decide,
      show Equiv.Perm.sign a.val = 1 from a.property]
    decide⟩
  invFun a := ⟨transposition * a.val * transposition, by
    change Equiv.Perm.sign _ = 1
    simp only [map_mul, show Equiv.Perm.sign transposition = -1 by decide,
      show Equiv.Perm.sign a.val = 1 from a.property]
    decide⟩
  left_inv a := by
    apply Subtype.ext
    change transposition * (transposition * a.val * transposition) * transposition = a.val
    simp [transposition, mul_assoc]
  right_inv a := by
    apply Subtype.ext
    change transposition * (transposition * a.val * transposition) * transposition = a.val
    simp [transposition, mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    change transposition * (a.val * b.val) * transposition =
      (transposition * a.val * transposition) * (transposition * b.val * transposition)
    simp [transposition, mul_assoc]

/-- The outer conjugate of the restricted natural module. -/
def outerNatural : Representation (ZMod 2) (alternatingGroup (Fin 8)) Four :=
  natural.comp outer.toMonoidHom

theorem outer_val (a : alternatingGroup (Fin 8)) :
    (outer a).val = transposition * a.val * transposition := by rfl

theorem outerNatural_apply (a : alternatingGroup (Fin 8)) (v : Four) :
    outerNatural a v = natural (outer a) v := by rfl

theorem outerNatural_faithful : Function.Injective outerNatural :=
  natural_faithful.comp outer.injective

private theorem sign_of_odd (g : Equiv.Perm (Fin 8)) (hg : g.sign ≠ 1) : g.sign = -1 :=
  (Int.units_eq_one_or g.sign).resolve_left hg

private def evenPart (g : Equiv.Perm (Fin 8)) : alternatingGroup (Fin 8) :=
  ⟨if g.sign = 1 then g else g * transposition, by
    rw [Equiv.Perm.mem_alternatingGroup]
    split_ifs with h
    · exact h
    · rw [map_mul, sign_of_odd g h, show transposition.sign = -1 by decide]
      decide⟩

private def actionMap (g : Equiv.Perm (Fin 8)) : Module.End (ZMod 2) Eight :=
  if g.sign = 1 then
    (natural (evenPart g)).prodMap (outerNatural (evenPart g))
  else
    ((natural (evenPart g)).prodMap (outerNatural (evenPart g))).comp
      (LinearEquiv.prodComm (ZMod 2) Four Four).toLinearMap

private theorem actionMap_apply (g : Equiv.Perm (Fin 8)) (v : Eight) :
    actionMap g v = if g.sign = 1 then
      (natural (evenPart g) v.1, outerNatural (evenPart g) v.2) else
      (natural (evenPart g) v.2, outerNatural (evenPart g) v.1) := by
  unfold actionMap
  split_ifs <;> rfl

private theorem actionMap_mul (g h : Equiv.Perm (Fin 8)) :
    actionMap (g * h) = actionMap g * actionMap h := by
  apply LinearMap.ext
  intro v
  change actionMap (g * h) v = actionMap g (actionMap h v)
  have work (hg : g.sign = 1 ∨ g.sign = -1) (hh : h.sign = 1 ∨ h.sign = -1) :
      actionMap (g * h) v = actionMap g (actionMap h v) := by
    rcases hg with hg | hg <;> rcases hh with hh | hh
    all_goals
      simp only [actionMap_apply, map_mul, hg, hh]
      apply Prod.ext
    all_goals
      change natural _ _ = natural _ (natural _ _)
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      apply Subtype.ext
      simp [evenPart, outer, transposition, map_mul, hg, hh, mul_assoc]
  exact work (Int.units_eq_one_or g.sign) (Int.units_eq_one_or h.sign)

/-- The induced pair: two conjugate natural A₈ actions, exchanged by (0 1). -/
def symmetricRepresentation : Representation (ZMod 2) (Equiv.Perm (Fin 8)) Eight where
  toFun := actionMap
  map_one' := by
    apply LinearMap.ext
    intro v
    have he : evenPart 1 = 1 := by apply Subtype.ext; simp [evenPart]
    simp [actionMap_apply, he]
  map_mul' := actionMap_mul

theorem symmetricRepresentation_inner (a : alternatingGroup (Fin 8)) (v : Eight) :
    symmetricRepresentation a.val v = (natural a v.1, outerNatural a v.2) := by
  have he : evenPart a.val = a := by
    apply Subtype.ext
    simp [evenPart, show a.val.sign = 1 from a.property]
  change actionMap a.val v = _
  simp only [actionMap_apply, show a.val.sign = 1 from a.property, if_true, he]

theorem symmetricRepresentation_transposition (v : Eight) :
    symmetricRepresentation transposition v = (v.2, v.1) := by
  have he : evenPart transposition = 1 := by
    apply Subtype.ext
    simp [evenPart, transposition]
  change actionMap transposition v = _
  simp only [actionMap_apply, show transposition.sign ≠ 1 by decide, if_false, he,
    map_one, Module.End.one_apply]


/-- The deleted permutation action on the six-dimensional quotient. -/
@[expose] def deleted : Representation (ZMod 2) S8 Six where
  toFun := Atlas.Order20160A8.DeletedEight.quotientPermMap
  map_one' := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => rfl

/-- The quotient action retains its literal permutation coordinates. -/
theorem deleted_apply (a : S8) (v : Six) :
    deleted a v = Atlas.Order20160A8.DeletedEight.quotientPerm a v := rfl

theorem deleted_faithful : Function.Injective deleted := by
  intro a b h
  apply Atlas.Order20160A8.DeletedEight.permutationHom_injective
  apply Subtype.ext
  apply LinearEquiv.ext
  exact LinearMap.congr_fun h

theorem six_finrank : Module.finrank (ZMod 2) Six = 6 :=
  Atlas.Order20160A8.DeletedEight.quotient_finrank

theorem eight_finrank : Module.finrank (ZMod 2) Eight = 8 := by
  simp [Eight, Four, Module.finrank_prod]

/-- Every nontrivial subgroup moves the deleted six-space. -/
theorem deleted_fixedCodim_pos (B : Subgroup S8) (hB : B ≠ ⊥) :
    1 ≤ fixedCodim deleted B := by
  by_contra hn
  have hz : fixedCodim deleted B = 0 := by omega
  have hfix := (fixedCodim_eq_zero_iff deleted B).mp hz
  obtain ⟨b, hb, hb1⟩ := B.bot_or_exists_ne_one.resolve_left hB
  apply hb1
  apply deleted_faithful
  apply LinearMap.ext
  intro v
  have hv : v ∈ fixedSpace deleted B := by rw [hfix]; trivial
  rw [map_one]
  exact hv ⟨b, hb⟩

end
end Representation.SymmetricEightConstituents
