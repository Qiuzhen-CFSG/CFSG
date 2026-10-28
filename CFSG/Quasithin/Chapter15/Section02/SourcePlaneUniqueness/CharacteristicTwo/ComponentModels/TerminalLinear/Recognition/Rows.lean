module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Rows
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorMoved
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels

/-!
# Moving the B.5 binary alternatives onto the specified carrier

Equivariant coordinates transport the repeated-natural and natural-plus-dual
models. The orthogonal alternative pulls back the actual fixed-space quotient.
For the irreducible ten-space, the checked I.1.6(7) classification supplies an
intertwiner with the exterior square or cube. These constructions retain both
the group marking and the linear map, including when a moved space is all of U.

Source: Aschbacher--Smith B.5.1, I.1.6(7), and 15.2.23(a)--(d).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open ChapterB.QuasisimpleSource.ExtensionConsequences
variable {D E W V : Type*} [Group D] [Group E]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D W} {τ : Representation (ZMod 2) E V}
  {L : Subgroup E}

private def repeatedOne (σ : Representation (ZMod 2) D W) : ActionEquiv σ (repeated σ 1) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := {
    toFun := fun v _ => v
    invFun := fun w => w 0
    left_inv := fun _ => rfl
    right_inv := fun w => funext fun _i => congrArg w (Subsingleton.elim _ _)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  intertwines _ _ := rfl

/-- Restrict an image subgroup through an overgroup without changing its action. -/
def subgroupOfActionEquiv (ρ : Representation (ZMod 2) D W)
    {A B : Subgroup D} (h : A ≤ B) :
    ActionEquiv (ρ.comp A.subtype) ((ρ.comp B.subtype).comp (A.subgroupOf B).subtype) :=
  ⟨(subgroupOfEquivOfLe h).symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩

/-- A moved section equal to the entire space retains the original action. -/
def movedTopActionEquiv (s : MovedSection τ L) (h : s.space.toSubmodule = ⊤) :
    ActionEquiv (τ.comp L.subtype) (s.space.toRepresentation.comp L.subtype) :=
  ⟨MulEquiv.refl _,
    (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] V).symm.trans
      (LinearEquiv.ofEq _ _ h.symm),fun _ _ => Subtype.ext rfl⟩

/-- Pull back the actual fixed quotient along the specified action equivalence. -/
theorem orthogonal_row_of_moved_equiv
    (s : MovedSection τ L)
    (a : ActionEquiv ρ (s.space.toRepresentation.comp L.subtype))
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 8)) :
    ModuleRow ρ := by
  let C : Subrepresentation ρ := {
    toSubmodule := s.central.toSubmodule.comap a.linearEquiv.toLinearMap
    apply_mem_toSubmodule := by
      intro g v hv
      change a.linearEquiv (ρ g v) ∈ s.central.toSubmodule
      rw [a.intertwines]
      exact s.central.apply_mem_toSubmodule (a.groupEquiv g) hv }
  have hfix : C.toSubmodule = fixedSpace ρ ⊤ := by
    ext v
    change a.linearEquiv v ∈ s.central.toSubmodule ↔ _
    rw [s.central_eq]
    constructor
    · intro hv g
      apply a.linearEquiv.injective
      change a.linearEquiv (ρ g.val v) = _
      rw [a.intertwines]
      exact hv (a.groupEquiv g.val)
    · intro hv l
      obtain ⟨g,rfl⟩ := a.groupEquiv.surjective l
      rw [←a.intertwines]
      exact congrArg a.linearEquiv (hv ⟨g,mem_top _⟩)
  have hmap : C.toSubmodule.map a.linearEquiv.toLinearMap = s.central.toSubmodule := by
    exact Submodule.map_comap_eq_of_surjective a.linearEquiv.surjective _
  let f := Submodule.Quotient.equiv C.toSubmodule s.central.toSubmodule a.linearEquiv hmap
  let b : ActionEquiv C.quotientRepresentation (s.action.comp L.subtype) :=
    ⟨a.groupEquiv,f,fun g v => by
      induction v using Submodule.Quotient.induction_on with | _ v =>
      change Submodule.Quotient.mk (a.linearEquiv (ρ g v)) =
        Submodule.Quotient.mk ((s.space.toRepresentation.comp L.subtype) (a.groupEquiv g)
          (a.linearEquiv v))
      rw [a.intertwines]⟩
  exact ModuleRow.orthogonalSix C hfix (b.trans e)

/-- I.1.6(7) identifies the actual irreducible degree-ten action. -/
theorem exterior_row_of_ten
    (e : D ≃* SL(5,ZMod 2)) (hi : IsIrreducible ρ)
    (hd : Module.finrank (ZMod 2) W = 10) : ModuleRow ρ := by
  let a : ActionEquiv ρ (ρ.comp e.symm.toMonoidHom) :=
    ⟨e,LinearEquiv.refl _ _,fun g v => by change ρ g v = ρ (e.symm (e g)) v; rw [e.symm_apply_apply]⟩
  let := irreducible_of_equiv (actionSymm a) hi
  have he := Representation.SL5TenDimensional.Classification.identification_of_finrank_ten
    (ρ.comp e.symm.toMonoidHom) hd
  rcases he with h2 | h3
  · let b := Classical.choice h2
    apply ModuleRow.exteriorFive 2 (Or.inl rfl) hi hd
    refine ⟨e,a.linearEquiv.trans b.toLinearEquiv,?_⟩
    intro g v
    change b (ρ g v) = _
    have hh := LinearMap.congr_fun (b.isIntertwining' (e g)) v
    change b (ρ (e.symm (e g)) v) = _ at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  · let b := Classical.choice h3
    apply ModuleRow.exteriorFive 3 (Or.inr rfl) hi hd
    refine ⟨e,a.linearEquiv.trans b.toLinearEquiv,?_⟩
    intro g v
    change b (ρ g v) = _
    have hh := LinearMap.congr_fun (b.isIntertwining' (e g)) v
    change b (ρ (e.symm (e g)) v) = _ at hh
    rw [e.symm_apply_apply] at hh
    exact hh

/-- The existing B.5 moved-space classifier supplies precisely the four rows
once its space is identified equivariantly with the original module. -/
theorem moduleRow_of_binary_moved_equiv
    (s : MovedSection τ L) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (h : BinaryActor.MovedCase s n)
    (a : ActionEquiv ρ (s.space.toRepresentation.comp L.subtype)) : ModuleRow ρ := by
  cases h with
  | natural e =>
    exact .repeatedNatural n 1 hn (by decide) (by rcases hn with rfl | rfl <;> decide)
      ((a.trans e).trans (repeatedOne _))
  | orthogonal _ e _ _ => exact orthogonal_row_of_moved_equiv s a e
  | exterior _ e hi hd =>
    exact exterior_row_of_ten (a.groupEquiv.trans e) (irreducible_of_equiv a hi)
      (a.linearEquiv.finrank_eq.trans hd)
  | naturalDual he => exact .naturalDual n hn ⟨a.trans he.some⟩
  | repeatedNatural r hp hb he => exact .repeatedNatural n r hn hp hb (a.trans he.some)

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
