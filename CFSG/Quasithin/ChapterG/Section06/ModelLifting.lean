module

public import CFSG.Quasithin.ChapterG.Section06.Source
public import CFSG.Quasithin.ChapterG.Section06.Elementary
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# Transporting an actual source action to a marked G.6 model

The B.5 source contracts describe actions on literal subrepresentations.  The
G.6 contract records the same action as a subgroup equivalence together with a
linear equivalence of the specified subspace.  This file supplies that small
transport step, preserving the actual subspace and its stability proof.

This is only a lifting adapter.  The source-row elimination and the removal of
fixed-space extensions remain with the G.6 assembly owner; in particular this
module does not turn a quotient action into an action on `V`.
-/

@[expose] public section

open Subgroup Representation
namespace CFSG.Quasithin.ChapterG.Section06

open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction.ProjectiveLine

universe u v w

variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- A source action equivalence on a literal invariant subspace is exactly a
`HasModelOn` witness for that subspace.  The subgroup map is the same map used
by the source action, and the stability field is supplied by the
subrepresentation itself. -/
theorem hasModelOn_of_actionEquiv
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Subrepresentation ρ)
    {B : Type w} [Group B] {F : Type*} [AddCommGroup F]
    [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) B F)
    (e : ActionEquiv (W.toRepresentation.comp K.subtype) σ) :
    HasModelOn ρ K W.toSubmodule σ := by
  refine ⟨e.groupEquiv, e.linearEquiv, ?_, ?_⟩
  · intro k w
    exact W.apply_mem_toSubmodule (k : G) w.2
  · intro k w
    exact e.intertwines k ⟨w, w.2⟩

/-- The top-space instance of `hasModelOn_of_actionEquiv`.  This is useful
when a source clause already identifies the whole original action; it does
not identify a quotient with the original module. -/
theorem hasModelOn_top_of_actionEquiv
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    {B : Type w} [Group B] {F : Type*} [AddCommGroup F]
    [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) B F)
    (e : ActionEquiv (ρ.comp K.subtype) σ) :
    HasModelOn ρ K (⊤ : Submodule (ZMod 2) V) σ := by
  let W : Subrepresentation ρ :=
    { toSubmodule := ⊤
      apply_mem_toSubmodule := by
        intro g v hv
        exact Submodule.mem_top }
  let i : W.toSubmodule ≃ₗ[ZMod 2] V :=
    { toFun := fun v => v.1
      invFun := fun v => ⟨v, Submodule.mem_top⟩
      left_inv := by intro v; exact Subtype.ext (by rfl)
      right_inv := by intro v; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let e' : ActionEquiv (W.toRepresentation.comp K.subtype) σ := by
    refine ⟨e.groupEquiv, i.trans e.linearEquiv, ?_⟩
    intro k w
    exact e.intertwines k w.1
  simpa only [W] using hasModelOn_of_actionEquiv ρ K W σ e'

/-- Package a transported binary-linear action into the first G.6 factor
alternative. -/
theorem factorModel_of_binaryLinearAction
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Subrepresentation ρ) (n : ℕ)
    (hn : 2 ≤ n ∧ n ≤ 5)
    (e : ActionEquiv (W.toRepresentation.comp K.subtype)
      (binaryLinearAction n)) :
    FactorModel ρ K W.toSubmodule := by
  exact Or.inl ⟨n, hn.1, hn.2,
    hasModelOn_of_actionEquiv ρ K W (binaryLinearAction n) e⟩

/-- Package a transported deleted-permutation action into the natural
permutation alternative. -/
theorem factorModel_of_naturalRepresentation
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Subrepresentation ρ) (n : ℕ)
    (hn : 5 ≤ n ∧ n ≤ 8)
    (e : ActionEquiv (W.toRepresentation.comp K.subtype)
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    FactorModel ρ K W.toSubmodule := by
  exact Or.inr (Or.inl ⟨n, hn.1, hn.2,
    hasModelOn_of_actionEquiv ρ K W
      (BinaryPermutation.naturalRepresentation (Fin n)) e⟩)

/-- Package a transported permutation-core action into the core alternative;
the even-degree S₆ and S₈ choices are both retained. -/
theorem factorModel_of_coreRepresentation
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Subrepresentation ρ) (n : ℕ)
    (hn : n = 6 ∨ n = 8)
    (e : ActionEquiv (W.toRepresentation.comp K.subtype)
      (BinaryPermutation.coreRepresentation (Fin n))) :
    FactorModel ρ K W.toSubmodule := by
  exact Or.inr (Or.inr ⟨n, hn, hasModelOn_of_actionEquiv ρ K W
    (BinaryPermutation.coreRepresentation (Fin n)) e⟩)

/-- The small two-factor list for a transported binary plane. -/
theorem smallFactorModel_of_binaryLinearAction
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Subrepresentation ρ) (n : ℕ)
    (hn : n = 2 ∨ n = 3)
    (e : ActionEquiv (W.toRepresentation.comp K.subtype)
      (binaryLinearAction n)) :
    SmallFactorModel ρ K W.toSubmodule := by
  rcases hn with rfl | rfl
  · exact Or.inl (hasModelOn_of_actionEquiv ρ K
      W (binaryLinearAction 2) e)
  · exact Or.inr (Or.inl (hasModelOn_of_actionEquiv ρ K W (binaryLinearAction 3) e))

/-- The small two-factor permutation alternative. -/
theorem smallFactorModel_of_naturalFive
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Subrepresentation ρ)
    (e : ActionEquiv (W.toRepresentation.comp K.subtype)
      (BinaryPermutation.naturalRepresentation (Fin 5))) :
    SmallFactorModel ρ K W.toSubmodule :=
  Or.inr (Or.inr (hasModelOn_of_actionEquiv ρ K
    W
    (BinaryPermutation.naturalRepresentation (Fin 5)) e))

end CFSG.Quasithin.ChapterG.Section06

end
