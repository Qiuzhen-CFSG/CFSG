module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage

/-!
# Natural SL3 modules for one actor

The actual special linear group determines the binary field degree, even
when its scalar center is nontrivial. A finite-field isomorphism therefore
puts two natural markings over one field. Full automorphism coverage then
compares the markings: GL conjugation and field automorphisms have explicit
binary-linear intertwiners, while inverse transpose gives the binary dual
through the field-trace pairing. The resulting equivalence preserves the
original actor on both modules.

Source: Aschbacher--Smith, B.5.1, printed p.101, the natural-constituent
reconstruction; GLS3 Theorem 2.5.12 and §2.7 supply the proved automorphism
coverage used here.
-/

public noncomputable section
open Representation Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
open Matrix.PSL3.OuterSolvable Matrix.PSL3.CartanActions.SixCommutators
universe u v w

private def actionTrans {G H J X Y Z : Type*} [Group G] [Group H] [Group J]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) G X} {σ : Representation (ZMod 2) H Y}
    {τ : Representation (ZMod 2) J Z} (a : ActionEquiv ρ σ) (b : ActionEquiv σ τ) :
    ActionEquiv ρ τ where
  groupEquiv := a.groupEquiv.trans b.groupEquiv
  linearEquiv := a.linearEquiv.trans b.linearEquiv
  intertwines g x := by
    change b.linearEquiv (a.linearEquiv (ρ g x)) = _
    rw [a.intertwines, b.intertwines]
    rfl

private def fieldCoordinates (F E : BinaryField) (f : F.Carrier ≃+* E.Carrier) :
    (Fin 3 → F.Carrier) ≃ₗ[ZMod 2] (Fin 3 → E.Carrier) where
  toFun v i := f (v i)
  invFun v i := f.symm (v i)
  left_inv v := funext (fun i => f.symm_apply_apply (v i))
  right_inv v := funext (fun i => f.apply_symm_apply (v i))
  map_add' v w := funext (fun i => f.map_add (v i) (w i))
  map_smul' c v := funext (fun i => ZMod.map_smul f.toAddMonoidHom c (v i))

private def fieldAction (F E : BinaryField) (f : F.Carrier ≃+* E.Carrier) :
    ActionEquiv (linearNatural F 3) (linearNatural E 3) where
  groupEquiv := Atlas.fieldEquivSL 3 f
  linearEquiv := fieldCoordinates F E f
  intertwines g v := by
    ext i
    change f (∑ j, g.val i j * v j) = ∑ j, f (g.val i j) * f (v j)
    simp only [map_sum, map_mul]

private def linearAction (F : BinaryField) (m : GL (Fin 3) F.Carrier) :
    ActionEquiv (linearNatural F 3) (linearNatural F 3) where
  groupEquiv := linearConjSL F.Carrier m
  linearEquiv := (Matrix.GeneralLinearGroup.toLin m).toLinearEquiv.restrictScalars (ZMod 2)
  intertwines g v := by
    have he := congrArg (fun x : GL (Fin 3) F.Carrier => x.val)
      (linearConjSL_toGL F.Carrier m g)
    change (linearConjSL F.Carrier m g).val = m.val * g.val * (m⁻¹).val at he
    change m.val.mulVec (g.val.mulVec v) =
      (linearConjSL F.Carrier m g).val.mulVec (m.val.mulVec v)
    rw [he]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
    have hc : (m⁻¹).val * m.val = 1 := congrArg Units.val (inv_mul_cancel m)
    rw [hc, mul_one]

private def graphAction (F : BinaryField) :
    ActionEquiv (linearNatural F 3).dual (linearNatural F 3) where
  groupEquiv := graphSL F.Carrier
  linearEquiv := (linearThreeGraphDualAction F).linearEquiv.symm
  intertwines g v := by
    have h := (ExtensionConsequences.actionSymm (linearThreeGraphDualAction F)).intertwines g v
    change (linearThreeGraphDualAction F).linearEquiv.symm ((linearNatural F 3).dual g v) =
      linearNatural F 3 ((linearThreeGraphDualAction F).groupEquiv.symm g)
        ((linearThreeGraphDualAction F).linearEquiv.symm v) at h
    rw [linearThreeGraphDualAction_groupEquiv] at h
    exact h

private def untwist {G H X Y Z : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) G X} {σ : Representation (ZMod 2) H Y}
    {τ : Representation (ZMod 2) H Z}
    (a : ActionEquiv ρ τ) (b : ActionEquiv σ τ) (mark : G ≃* H)
    (h : ∀ g, b.groupEquiv (mark g) = a.groupEquiv g) :
    ρ.Equiv (σ.comp mark.toMonoidHom) :=
  .mk (a.linearEquiv.trans b.linearEquiv.symm) (by
    intro g
    apply LinearMap.ext
    intro v
    apply b.linearEquiv.injective
    change b.linearEquiv (b.linearEquiv.symm (a.linearEquiv (ρ g v))) =
      b.linearEquiv (σ (mark g) (b.linearEquiv.symm (a.linearEquiv v)))
    rw [b.linearEquiv.apply_symm_apply, b.intertwines,
      b.linearEquiv.apply_symm_apply, h, a.intertwines])

private theorem linearThree_natural_fixed_mark
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (F : BinaryField)
    (hρ : IsLinearNatural ρ F 3) (mark : G ≃* SL(3,F.Carrier)) :
    Nonempty (ρ.Equiv ((linearNatural F 3).comp mark.toMonoidHom)) ∨
    Nonempty (ρ.Equiv ((linearNatural F 3).dual.comp mark.toMonoidHom)) := by
  obtain ⟨a⟩ := hρ
  let α : MulAut SL(3,F.Carrier) := mark.symm.trans a.groupEquiv
  obtain ⟨m,f,ε,hα⟩ := Matrix.PSL3.CartanActions.ActorCoverage.specialCoverage_of_standard_eq_top
    F.Carrier (standard_eq_top_of_two_power_card F.Carrier F.degree_pos F.card_eq) α
  cases ε
  · let b := actionTrans (fieldAction F F f) (linearAction F m)
    have hb : b.groupEquiv = α := by
      rw [hα]
      ext g
      rfl
    exact Or.inl ⟨untwist a b mark (by
      intro g
      rw [hb]
      exact congrArg a.groupEquiv (mark.symm_apply_apply g))⟩
  · let b := actionTrans (graphAction F)
      (actionTrans (linearAction F (Matrix.PSL3.OuterSolvable.OddPrimeCoverage.reversalGL F.Carrier))
        (actionTrans (fieldAction F F f) (linearAction F m)))
    have hb : b.groupEquiv = α := by
      rw [hα]
      ext g
      rfl
    exact Or.inr ⟨untwist a b mark (by
      intro g
      rw [hb]
      exact congrArg a.groupEquiv (mark.symm_apply_apply g))⟩

private def dualEquiv {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) G X} {σ : Representation (ZMod 2) G Y}
    (e : ρ.Equiv σ) : ρ.dual.Equiv σ.dual :=
  .mk e.symm.toLinearEquiv.dualMap (by
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro w
    change f (ρ g⁻¹ (e.symm w)) = f (e.symm (σ g⁻¹ w))
    exact congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' g⁻¹) w).symm)

private theorem dual_comp_eq {G H X : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) H X) (f : G →* H) :
    Representation.dual (σ.comp f) = σ.dual.comp f := by
  ext g l v
  change l (σ (f g⁻¹) v) = l (σ ((f g)⁻¹) v)
  rw [map_inv]

/-- Natural modules of dimension three for the same actual actor are
isomorphic or contragredient, even when their field markings differ. -/
theorem linearThree_naturals_same_or_dual
    {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (F E : BinaryField) (hρ : IsLinearNatural ρ F 3) (hσ : IsLinearNatural σ E 3) :
    Nonempty (ρ.Equiv σ) ∨ Nonempty (ρ.Equiv σ.dual) := by
  obtain ⟨a⟩ := hρ
  obtain ⟨b⟩ := hσ
  have hd := linearThree_degree_eq F E (a.groupEquiv.symm.trans b.groupEquiv)
  let := Fintype.ofFinite F.Carrier
  let := Fintype.ofFinite E.Carrier
  let f : E.Carrier ≃+* F.Carrier := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, E.card_eq, F.card_eq, hd])
  let b' := actionTrans b (fieldAction E F f)
  let e : σ.Equiv ((linearNatural F 3).comp b'.groupEquiv.toMonoidHom) :=
    .mk b'.linearEquiv (by intro g; apply LinearMap.ext; intro v; exact b'.intertwines g v)
  rcases linearThree_natural_fixed_mark ρ F ⟨a⟩ b'.groupEquiv with h | h
  · obtain ⟨h⟩ := h
    exact Or.inl ⟨h.trans e.symm⟩
  · obtain ⟨h⟩ := h
    have he := (dualEquiv e).symm
    rw [dual_comp_eq] at he
    exact Or.inr ⟨h.trans he⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
