module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeReconstruction
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# The original reducible SL3 source excludes minimal parabolicity

Apply the proved B.5.1 reconstruction inside the actual local actor containing
L. Restriction preserves the literal commutator space [V,L], so the resulting
doubled-natural coordinates also describe the component action on the full
ambient moved subrepresentation. Both natural parabolics are then invariant
under the original Sylow, contradicting minimal parabolicity.

The local source hypothesis is the original B.5.1 hypothesis, not a module
chart or a statement about ambient invariant flags. Its preparation in a
particular component quotient is a separate earlier-source application.

Source: Aschbacher–Smith B.5.1 and B.6.9, printed pp.101 and 116
(1 March 2004 manuscript).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
/-- Restricting the actor preserves the literal moved space. -/
theorem moved_restrict_actor {L P : Subgroup G} (hLP : L ≤ P) :
    moved (ρ.comp P.subtype) (L.subgroupOf P) = moved ρ L := by
  have he := subspaceCommutator_map_embedding (ρ.comp P.subtype) ρ P.subtype
    (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl)
    (L.subgroupOf P) (⊤ : Submodule (ZMod 2) V)
  simpa only [Submodule.map_id, map_subgroupOf_eq_of_le hLP] using he

omit [Finite G] in
/-- Natural coordinates on the local moved space keep the original component mark. -/
theorem repeated_natural_moved_of_restriction {L P : Subgroup G} (hLP : L ≤ P)
    (s : MovedSection ρ L) (t : MovedSection (ρ.comp P.subtype) (L.subgroupOf P))
    (F : BinaryField) (r : ℕ)
    (h : IsRepeatedLinearNatural (t.space.toRepresentation.comp
      (L.subgroupOf P).subtype) F 3 r) :
    IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 r := by
  have hm : s.space.toSubmodule = t.space.toSubmodule := by
    rw [s.space_eq, t.space_eq, moved_restrict_actor ρ hLP]
  let e := LinearEquiv.ofEq _ _ hm
  obtain ⟨a⟩ := h
  refine ⟨⟨(subgroupOfEquivOfLe hLP).symm.trans a.groupEquiv,
    e.trans a.linearEquiv, ?_⟩⟩
  intro l w
  exact a.intertwines ((subgroupOfEquivOfLe hLP).symm l) (e w)

/-- The original reducible B.5.1 source in an actor subgroup excludes a minimal-parabolic SL3 supplement. -/
theorem not_minimalParabolic_of_reducible_three_source_restriction
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (T : Sylow 2 G) (L P : Subgroup G) [L.Normal]
    (hLP : L ≤ P) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (h : QuasisimpleSourceHypothesis (ρ.comp P.subtype) K (L.subgroupOf P))
    (hnot : ¬ IsIrrPlus (ρ.comp P.subtype) (L.subgroupOf P)
      (moved (ρ.comp P.subtype) (L.subgroupOf P)))
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  let s := MovedSection.ofNormal ρ L
  let t := h.movedSection (ρ.comp P.subtype)
  obtain ⟨E,he⟩ := SourceCompletion.linearThree_source_moved_double (ρ.comp P.subtype)
    hK hsemisimple h36 earlier h hnot t F ((subgroupOfEquivOfLe hLP).trans mark)
  exact not_minimalParabolic_of_repeated_natural_three T L hgen s.space.toRepresentation E 2
    (by decide) (repeated_natural_moved_of_restriction ρ hLP s t E 2 he)

end CFSG.Quasithin.ChapterB
