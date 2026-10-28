module
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Natural

/-!
# The eight-dimensional symmetric extension of the natural A₇ action

Write an even permutation as `a` and an odd permutation as `a t`, where
`t = (0 1)`. On the two coordinate summands let `a` act as the natural
representation and its conjugate by `t`, and let `t` exchange coordinates.
The four parity cases prove the multiplication law. Restriction to the first
coordinate and the exchange of the two axes prove faithfulness.

The coordinate projections give actual intertwining equivalences from the
summands to `natural` and `outerNatural`. The conditional constructor at the
end isolates irreducibility and inequivalence; it does not assert that those
remaining facts, or H.8, have already been proved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.8, printed p.389/PDF p.400.
-/

public section

open Representation
namespace Representation.AlternatingSevenConjugatePair.Model
noncomputable section

private theorem sign_of_odd (g : Equiv.Perm (Fin 7)) (hg : g.sign ≠ 1) : g.sign = -1 :=
  (Int.units_eq_one_or g.sign).resolve_left hg

private def evenPart (g : Equiv.Perm (Fin 7)) : alternatingGroup (Fin 7) :=
  ⟨if g.sign = 1 then g else g * transposition, by
    rw [Equiv.Perm.mem_alternatingGroup]
    split_ifs with h
    · exact h
    · rw [map_mul, sign_of_odd g h, show transposition.sign = -1 by decide]
      decide⟩

private def actionMap (g : Equiv.Perm (Fin 7)) : Module.End (ZMod 2) Eight :=
  if g.sign = 1 then
    (natural (evenPart g)).prodMap (outerNatural (evenPart g))
  else
    ((natural (evenPart g)).prodMap (outerNatural (evenPart g))).comp
      (LinearEquiv.prodComm (ZMod 2) Four Four).toLinearMap

private theorem actionMap_apply (g : Equiv.Perm (Fin 7)) (v : Eight) :
    actionMap g v = if g.sign = 1 then
      (natural (evenPart g) v.1, outerNatural (evenPart g) v.2) else
      (natural (evenPart g) v.2, outerNatural (evenPart g) v.1) := by
  unfold actionMap
  split_ifs <;> rfl

private theorem actionMap_mul (g h : Equiv.Perm (Fin 7)) :
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

/-- The actual faithful S₇ representation extending the two conjugate actions. -/
def symmetricRepresentation : Representation (ZMod 2) (Equiv.Perm (Fin 7)) Eight where
  toFun := actionMap
  map_one' := by
    apply LinearMap.ext
    intro v
    have he : evenPart 1 = 1 := by apply Subtype.ext; simp [evenPart]
    simp [actionMap_apply, he]
  map_mul' := actionMap_mul

theorem symmetricRepresentation_inner (a : alternatingGroup (Fin 7)) (v : Eight) :
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

/-- The first actual A₇-invariant coordinate summand. -/
@[expose] def first : Subrepresentation
    (symmetricRepresentation.comp (alternatingGroup (Fin 7)).subtype) where
  toSubmodule := LinearMap.ker (LinearMap.snd (ZMod 2) Four Four)
  apply_mem_toSubmodule := by
    intro a v hv
    change (symmetricRepresentation a.val v).2 = 0
    rw [symmetricRepresentation_inner]
    change outerNatural a v.2 = 0
    rw [show v.2 = 0 from hv, map_zero]

/-- The second actual A₇-invariant coordinate summand. -/
@[expose] def second : Subrepresentation
    (symmetricRepresentation.comp (alternatingGroup (Fin 7)).subtype) where
  toSubmodule := LinearMap.ker (LinearMap.fst (ZMod 2) Four Four)
  apply_mem_toSubmodule := by
    intro a v hv
    change (symmetricRepresentation a.val v).1 = 0
    rw [symmetricRepresentation_inner]
    change natural a v.1 = 0
    rw [show v.1 = 0 from hv, map_zero]

/-- Projection identifies the first summand with the restricted natural four-space. -/
@[expose] def firstEquiv : first.toRepresentation.Equiv natural where
  toFun v := v.val.1
  invFun v := ⟨(v, 0), rfl⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext rfl v.property.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' a := by
    apply LinearMap.ext
    intro v
    exact congrArg Prod.fst (symmetricRepresentation_inner a v.val)

/-- Projection identifies the second summand with its outer conjugate. -/
@[expose] def secondEquiv : second.toRepresentation.Equiv outerNatural where
  toFun v := v.val.2
  invFun v := ⟨(0, v), rfl⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext v.property.symm rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' a := by
    apply LinearMap.ext
    intro v
    exact congrArg Prod.snd (symmetricRepresentation_inner a v.val)

theorem first_second_complementary : IsCompl first.toSubmodule second.toSubmodule := by
  change IsCompl (LinearMap.ker (LinearMap.snd (ZMod 2) Four Four))
    (LinearMap.ker (LinearMap.fst (ZMod 2) Four Four))
  rw [LinearMap.ker_snd, LinearMap.ker_fst]
  exact LinearMap.isCompl_range_inl_inr

theorem first_dimension : Module.finrank (ZMod 2) first.toSubmodule = 4 :=
  firstEquiv.toLinearEquiv.finrank_eq.trans four_dimension

theorem second_dimension : Module.finrank (ZMod 2) second.toSubmodule = 4 :=
  secondEquiv.toLinearEquiv.finrank_eq.trans four_dimension

theorem symmetricRepresentation_swap_first (g : Equiv.Perm (Fin 7))
    (hg : g ∉ alternatingGroup (Fin 7)) (v : Eight) (hv : v ∈ first.toSubmodule) :
    symmetricRepresentation g v ∈ second.toSubmodule := by
  have hs : g.sign ≠ 1 := hg
  change (actionMap g v).1 = 0
  rw [actionMap_apply, if_neg hs]
  change natural (evenPart g) v.2 = 0
  rw [show v.2 = 0 from hv, map_zero]

theorem symmetricRepresentation_swap_second (g : Equiv.Perm (Fin 7))
    (hg : g ∉ alternatingGroup (Fin 7)) (v : Eight) (hv : v ∈ second.toSubmodule) :
    symmetricRepresentation g v ∈ first.toSubmodule := by
  have hs : g.sign ≠ 1 := hg
  change (actionMap g v).2 = 0
  rw [actionMap_apply, if_neg hs]
  change outerNatural (evenPart g) v.1 = 0
  rw [show v.1 = 0 from hv, map_zero]

theorem symmetricRepresentation_faithful : Function.Injective symmetricRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro g hg
  have hact : symmetricRepresentation g = 1 := hg
  by_cases hs : g ∈ alternatingGroup (Fin 7)
  · have he : natural (⟨g, hs⟩ : alternatingGroup (Fin 7)) = natural 1 := by
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun f : Module.End (ZMod 2) Eight => (f (v, 0)).1) hact
      rw [symmetricRepresentation_inner ⟨g, hs⟩] at hv
      simpa only [map_one, Module.End.one_apply] using hv
    exact congrArg Subtype.val (natural_faithful he)
  · have hv := symmetricRepresentation_swap_first g hs (fun _ => 1, 0) rfl
    change (symmetricRepresentation g (fun _ => 1, 0)).1 = 0 at hv
    rw [hact] at hv
    have hx := congrFun hv 0
    exact (one_ne_zero hx).elim

private theorem irreducible_of_equiv {U W : Type*}
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) U}
    {σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W}
    (e : ρ.Equiv σ) (hσ : IsIrreducible σ) : IsIrreducible ρ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule σ).mp hσ)

/-- The concrete S₇ action is a conjugate pair once the two remaining
four-dimensional representation-theoretic facts are established. -/
@[expose] def pairOfIrreducibleInequivalent
    (hfirst : IsIrreducible natural) (hsecond : IsIrreducible outerNatural)
    (hne : ¬ Nonempty (natural.Equiv outerNatural)) : Pair Eight where
  representation := symmetricRepresentation
  faithful := symmetricRepresentation_faithful
  first := first
  second := second
  complementary := first_second_complementary
  first_dim := first_dimension
  second_dim := second_dimension
  first_irreducible := by exact irreducible_of_equiv firstEquiv hfirst
  second_irreducible := by exact irreducible_of_equiv secondEquiv hsecond
  inequivalent := by
    rintro ⟨e⟩
    exact hne ⟨firstEquiv.symm.trans (e.trans secondEquiv)⟩
  swap_first := symmetricRepresentation_swap_first
  swap_second := symmetricRepresentation_swap_second

end
end Representation.AlternatingSevenConjugatePair.Model
