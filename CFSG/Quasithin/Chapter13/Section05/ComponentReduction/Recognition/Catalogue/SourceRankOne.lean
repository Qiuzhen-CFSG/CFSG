module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceRows
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
/-!
# The original rank-one natural chief row is impossible

The genuine pair condition forces the defining field to F₂. Its SL₂ is
solvable, contradicting the quasisimple component on the actual chief image.
The model equivalence is a catalogue alternative being excluded.
Source: Aschbacher–Smith13.5.21, p.924.
-/
public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Configuration ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The pair geometry forces a rank-one field to F₂, contradicting quasisimplicity. -/
theorem source_not_linearTwo_action
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E) [IsQuasisimple L]
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField) :
    ¬ Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural F 2)) := by
  rintro ⟨a⟩
  obtain ⟨_,_,⟨b⟩⟩ := LocalModels.DefiningFields.source_binary_linearTwo s h Y hY c
    ρ L comparison F a
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype,←alternatingGroup_eq_sign_ker]
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
    (f := (b.groupEquiv.trans e).toMonoidHom) (b.groupEquiv.trans e).injective
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact Group.IsPerfect.not_isSolvable L inferInstance

/-- Literal B.4.2 rank-one chief action, kept behind a typed interface. -/
@[expose] def LinearTwoChiefAction {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (F : BinaryField) : Prop :=
  Nonempty (ActionEquiv (ρ.comp (generalizedFitting E).subtype) (linearNatural F 2))

private theorem no_linearTwo {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (Y : Subgroup G) (hY : Y ≤ D.L₁)
    (c : SourceConfiguration s h Y hY) (ρ : Representation (ZMod 2) E W)
    [IsQuasisimple (generalizedFitting E)]
    (comparison : Khat s h ≃* ((generalizedFitting E) ⧸ center (generalizedFitting E)))
    (F : BinaryField) : ¬ LinearTwoChiefAction ρ F :=
  source_not_linearTwo_action s h Y hY c ρ (generalizedFitting E) comparison F

variable [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The actual source chief hypotheses and marked quotient discharge the entire linear-two row. -/
theorem source_chief_not_linearTwo
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hirr : IsIrreducible (chiefRepresentation D K h U N))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    (F : BinaryField) :
    ¬ LinearTwoChiefAction (Representation.BinaryOffender.imageRepresentation
      (chiefRepresentation D K h U N)) F := by
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  have hp := source_chief_hypotheses_all D K h s hG hH hi hu hcard U N hn hirr
  let := hp.quasisimple
  exact no_linearTwo s h Y hY c _ comparison F

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
