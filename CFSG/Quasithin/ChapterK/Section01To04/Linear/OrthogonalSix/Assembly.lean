module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Ambient
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.Setup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The recognized orthogonal-six branch of K.3.2

The actual exterior-square intertwiner identifies the restricted layer action
with the binary A₈ module. The computed full normalizer and faithfulness then
give precisely the A₈ and S₈ ambient actions. Transporting the checked §B.3
offender calculations proves generation, ratio one and rank-three best
offenders in the A₈ case, and generation and ratio three quarters in the S₈
case. The A₈ action also has no strong offenders.

The final theorem applies this argument to the original SQTK action with
F*(G)=L and constructs the literal corrected B.4.2 catalogue entry. Its only
recognition input is an action equivalence of the restricted L-action with the
actual SL₄(2) exterior square. Exhaustion of the restricted-module possibilities
belongs to the independent K.3.2 recognition argument.

Source: Aschbacher–Smith, K.3.2.2, printed p.455/PDF p.466,
and B.4.2(10), printed p.86/PDF p.97.
-/

public section

open Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- Compose the actual exterior-square comparison with a recognized restricted
SL₄(2) action. Both the group twist and the linear coordinates are retained. -/
noncomputable def exteriorRestrictionEquiv
    (e : ActionEquiv (ρ.comp L.subtype) exteriorRepresentation) :
    ActionEquiv (ρ.comp L.subtype) (alternatingNaturalRepresentation (Fin 8)) where
  groupEquiv := e.groupEquiv.trans exteriorActionEquiv.groupEquiv
  linearEquiv := e.linearEquiv.trans exteriorActionEquiv.linearEquiv
  intertwines l v := (congrArg exteriorActionEquiv.linearEquiv (e.intertwines l v)).trans
    (exteriorActionEquiv.intertwines (e.groupEquiv l) (e.linearEquiv v))

private noncomputable def wholeAction {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W] {σ : Representation (ZMod 2) H W}
    (e : ActionEquiv (ρ.comp L.subtype) σ) (hL : L = ⊤) : ActionEquiv ρ σ := by
  subst L
  exact {
    groupEquiv := Subgroup.topEquiv.symm.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := fun g v => e.intertwines ⟨g, Subgroup.mem_top g⟩ v }

/-- The full B.4.2(10) alternatives on the original ambient action. In the
alternating case every best offender has rank three and no strong offender
exists; in the symmetric case the marked component is the actual A₈ subgroup. -/
theorem ambient_conclusions [L.Normal] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNaturalRepresentation (Fin 8))) :
    offenderSubgroup ρ = ⊤ ∧
      ((L = ⊤ ∧ quadraticRatio ρ = 1 ∧
        (∀ A, IsBestOffender ρ A → rank A = 3) ∧ ¬ IsStrongFFModule ρ) ∨
       (L ≠ ⊤ ∧ Nonempty (MarkedActionEquiv ρ ⊤ L
         (naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8))) ∧
         quadraticRatio ρ = 3 / 4)) := by
  rcases extension_alternatives ρ L hf e with hL | ⟨hL, ⟨a⟩⟩
  · obtain ⟨hg, hq, hb, hs⟩ := alternating_conclusions (wholeAction ρ L e hL)
    exact ⟨hg, Or.inl ⟨hL, hq, hb, hs⟩⟩
  · obtain ⟨hg, hq⟩ := symmetric_conclusions (wholeAction ρ ⊤ a.action rfl)
    exact ⟨hg, Or.inr ⟨hL, ⟨a⟩, hq⟩⟩

/-- Connection to the literal corrected B.4.2 action catalogue. No ambient
normalizer or offender premise remains beyond the restricted action comparison. -/
theorem ambient_case [L.Normal] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNaturalRepresentation (Fin 8))) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨hg, h⟩ := ambient_conclusions ρ L hf e
  rcases h with ⟨hL, hq, hb, _⟩ | ⟨_, ⟨a⟩, hq⟩
  · exact .orthogonalSix (hg.trans hL.symm) hL e hb hq
  · rw [hg]
    exact .symmetricEight rfl a hq

/-- The exact six-dimensional condition follows from the exterior-square
comparison; it is not a further recognition premise. -/
theorem finrank_of_exterior
    (e : ActionEquiv (ρ.comp L.subtype) exteriorRepresentation) :
    Module.finrank (ZMod 2) V = 6 := by
  calc
    Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (natural (Fin 8)) :=
      (exteriorRestrictionEquiv ρ L e).linearEquiv.finrank_eq
    _ = 6 := by rw [finrank_natural_even (Fin 8) (by decide)]; decide

/-- K.3.2.2 and B.4.2(10) for the original faithful SQTK action after the
independent recognition step has identified its restricted exterior square.
Normality is derived from the actual F*(G)=L hypothesis. -/
theorem source_case {K : GroupClass}
    (h : Recognition.SourceHypothesis K ρ L)
    (e : ActionEquiv (ρ.comp L.subtype) exteriorRepresentation) :
    Module.finrank (ZMod 2) V = 6 ∧ offenderSubgroup ρ = ⊤ ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  let : Finite G := h.finite_group
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  let : L.Normal := h.fitting ▸ inferInstance
  let a := exteriorRestrictionEquiv ρ L e
  exact ⟨finrank_of_exterior ρ L e, (ambient_conclusions ρ L h.faithful a).1,
    ambient_case ρ L h.faithful a⟩

end CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
