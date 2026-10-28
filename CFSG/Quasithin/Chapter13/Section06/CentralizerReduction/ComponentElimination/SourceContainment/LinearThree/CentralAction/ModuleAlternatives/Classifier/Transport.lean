module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Returning classified moved sections to the ambient action

For C normal in D and C ≤ H, the C-commutator subspace is unchanged by
restricting D to H. Thus a moved section for H already has a D-invariant
underlying space. Its central denominator is likewise unchanged and invariant.
We extend these two actions without changing either underlying submodule.

The two module alternatives therefore return through the actual isomorphism
C ≃ C.subgroupOf H. Each returned action uses the original linear intertwiner.
The natural branch retains commutator generation; the doubled branch remains
an assertion on the moved space itself. No splitting of a quotient is inferred.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the use of
B.5.1 and B.5.6 in 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
open ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C H : Subgroup D}

/-- Restriction changes neither generators nor their binary span. -/
theorem restricted_commutator (hCH : C ≤ H) (U : Submodule (ZMod 2) V) :
    subspaceCommutator (ρ.comp H.subtype) U (C.subgroupOf H) =
      subspaceCommutator ρ U C := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, w, hw, rfl⟩
    exact ⟨c, hc, w, hw, rfl⟩
  · rintro ⟨c, hc, w, hw, rfl⟩
    exact ⟨⟨c, hCH hc⟩, hc, w, hw, rfl⟩

/-- Retain the exact moved submodule and recover the whole ambient action. -/
noncomputable def liftSpace [C.Normal] (hCH : C ≤ H)
    (s : MovedSection (ρ.comp H.subtype) (C.subgroupOf H)) : Subrepresentation ρ := by
  have he : s.space.toSubmodule = moved ρ C :=
    s.space_eq.trans (restricted_commutator hCH ⊤)
  have hm := (MovedSection.ofNormal ρ C).space.apply_mem_toSubmodule
  refine ⟨s.space.toSubmodule, ?_⟩
  intro g v hv
  rw [he] at hv ⊢
  exact hm g hv

/-- The central denominator is literally the original component fixed space. -/
theorem liftCentral_eq [C.Normal] (hCH : C ≤ H)
    (s : MovedSection (ρ.comp H.subtype) (C.subgroupOf H)) :
    s.central.toSubmodule = fixedSpace (liftSpace hCH s).toRepresentation C := by
  rw [s.central_eq]
  change fixedSpace ((liftSpace hCH s).toRepresentation.comp H.subtype) (C.subgroupOf H) = _
  rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hCH]

/-- Extend both ambient actions, preserving `space_eq` and `central_eq`. -/
noncomputable def liftSection [C.Normal] (hCH : C ≤ H)
    (s : MovedSection (ρ.comp H.subtype) (C.subgroupOf H)) : MovedSection ρ C := by
  let U := liftSpace hCH s
  have hc := fixedSpace_stable_of_normal U.toRepresentation C
  refine ⟨U, s.space_eq.trans (restricted_commutator hCH ⊤),
    ⟨s.central.toSubmodule, ?_⟩, liftCentral_eq hCH s⟩
  intro g v hv
  rw [liftCentral_eq hCH s] at hv ⊢
  exact (hc (mem_top g) v).2 hv

/-- Both literal module alternatives return to D with the same intertwiner. -/
theorem lift_case [C.Normal] (hCH : C ≤ H)
    (hcase : LinearThreeModuleCase (ρ.comp H.subtype) (C.subgroupOf H)) :
    LinearThreeModuleCase ρ C := by
  cases hcase with
  | natural s hg e =>
    refine .natural (liftSection hCH s) ?_ ?_
    · exact (restricted_commutator hCH s.space.toSubmodule).symm.trans hg
    · refine ⟨(subgroupOfEquivOfLe hCH).symm.trans e.groupEquiv, e.linearEquiv, ?_⟩
      intro c w
      exact e.intertwines ((subgroupOfEquivOfLe hCH).symm c) w
  | doubled s e =>
    refine .doubled (liftSection hCH s) ?_
    refine ⟨(subgroupOfEquivOfLe hCH).symm.trans e.groupEquiv, e.linearEquiv, ?_⟩
    intro c w
    exact e.intertwines ((subgroupOfEquivOfLe hCH).symm c) w

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
