module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.BinaryGeometry
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Select and mark a constituent of the actual small action

Transport the four-element plane and its order-24 stabilizer through the
full doubled-action equivalence. Disjointness from the stabilizer's fixed
space is preserved, so binary geometry supplies a natural copy containing
the plane. Pulling that copy back preserves genuine Irr⁺, including the
literal central submodule and induced quotient action.

The same model plane also gives separate lines in the two coordinate
summands of the original module. Each has the original parabolic as its
exact stabilizer. The embeddings, projections, complementarity and
reconstruction are the actual maps from Doubled; no nonzero plane is
claimed to lie in both disjoint summands.

The final theorem combines this with the whole-module Irr⁺ branch. Its
consumer in Constituents discharges the full-action and moving-plane
hypotheses from the genuine earlier source inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1ii),
printed p.99, and the first paragraph of the proof of 15.3.31, p.1132.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

section Coordinates
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)
  (e : ActionEquiv ρ (repeated binaryNatural 2))
  (E : Submodule (ZMod 2) V) (P : Subgroup D)

/-- Transport the moving plane and its actual stabilizer to the doubled model,
then select a natural copy containing it. Every geometry premise is proved. -/
theorem binaryLine_of_coordinates (hE : Nat.card E = 4) (hP : Nat.card P = 24)
    (hs : subspaceStabilizer ρ E = P) (hd : Disjoint E (fixedSpace ρ P)) :
    Nonempty (BinaryDoubledLine (E.map e.linearEquiv.toLinearMap)
      (P.map e.groupEquiv.toMonoidHom)) := by
  apply BinaryGeometry.exists_binaryDoubledLine
  · exact (embedding_line_card _ e.linearEquiv.injective E).trans hE
  · exact (Nat.card_congr (e.groupEquiv.subgroupMap P).toEquiv).symm.trans hP
  · exact (hs ▸ map_subspaceStabilizer_equivariant ρ _ e.groupEquiv
      e.linearEquiv e.intertwines E).le
  · apply Submodule.disjoint_def.mpr
    rintro w ⟨v, hv, rfl⟩ hw
    have hvfix : v ∈ fixedSpace ρ P := by
      intro g
      apply e.linearEquiv.injective
      change e.linearEquiv (ρ g v) = e.linearEquiv v
      rw [e.intertwines]
      exact hw ⟨e.groupEquiv g, Subgroup.mem_map_of_mem _ g.property⟩
    change e.linearEquiv v = 0
    exact (congrArg e.linearEquiv (Submodule.disjoint_def.mp hd v hv hvfix)).trans
      e.linearEquiv.map_zero

/-- Pull the selected natural copy back to the original module. Irr⁺ transport
uses the literal fixed submodule and the induced central quotient action. -/
theorem binaryLine_containing
    (b : BinaryDoubledLine (E.map e.linearEquiv.toLinearMap)
      (P.map e.groupEquiv.toMonoidHom)) :
    ∃ W : Submodule (ZMod 2) V, IsIrrPlus ρ ⊤ W ∧ E ≤ W := by
  refine ⟨b.embedding.range.map e.linearEquiv.symm.toLinearMap, ?_, ?_⟩
  · refine IsIrrPlus.map_embedding ρ (repeated binaryNatural 2) e.groupEquiv.toMonoidHom
      e.linearEquiv.symm.toLinearMap e.linearEquiv.symm.injective
      ?_ ⊤ b.embedding.range ?_
    · intro g w
      apply e.linearEquiv.injective
      simp only [LinearEquiv.coe_coe, e.intertwines, LinearEquiv.apply_symm_apply,
        MulEquiv.coe_toMonoidHom]
    · simpa only [map_top_of_surjective e.groupEquiv.toMonoidHom
        e.groupEquiv.surjective] using b.constituent
  · intro v hv
    have hm : e.linearEquiv v ∈ b.plane.map b.embedding := by
      rw [b.image]
      exact ⟨v, hv, rfl⟩
    obtain ⟨w, hw, he⟩ := hm
    exact ⟨e.linearEquiv v, ⟨w, he⟩, e.linearEquiv.symm_apply_apply v⟩

/-- Two actual complementary natural summands carry separate transported
lines with the original stabilizer. Their embeddings use the same actor map. -/
theorem binaryLine_copy_markings
    (b : BinaryDoubledLine (E.map e.linearEquiv.toLinearMap)
      (P.map e.groupEquiv.toMonoidHom)) :
    (∀ i : Fin 2, IsIrrPlus ρ ⊤ (copyEmbedding e i).range ∧
      Nat.card (b.plane.map (copyEmbedding e i)) = 4 ∧
      subspaceStabilizer ρ (b.plane.map (copyEmbedding e i)) = P) ∧
    Disjoint (b.plane.map (copyEmbedding e 0)) (b.plane.map (copyEmbedding e 1)) := by
  obtain ⟨hm, hd⟩ := copy_marked_lines e P b.plane b.plane_card b.stabilizer.symm
  exact ⟨fun i => ⟨copy_isIrrPlus e i BinaryGeometry.natural_isIrrPlus, hm i⟩, hd⟩

end Coordinates

section Selection
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
  (E : Submodule (ZMod 2) V) (P : Subgroup L)

/-- Complete constituent selection from the unmarked full-action alternative.
The doubled output retains the geometry witness for both transported lines. -/
theorem marked_of_smallAction (h : SmallActionAlternative ρ L P)
    (hE : Nat.card E = 4) (hs : subspaceStabilizer (ρ.comp L.subtype) E = P)
    (hd : Disjoint E (fixedSpace (ρ.comp L.subtype) P)) :
    Nonempty (MarkedConstituent ρ L E P) ∧
      (IsIrrPlus ρ L ⊤ ∨ ∃ e : ActionEquiv (ρ.comp L.subtype) (repeated binaryNatural 2),
        Nonempty (BinaryDoubledLine (E.map e.linearEquiv.toLinearMap)
          (P.map e.groupEquiv.toMonoidHom))) := by
  have hdc : Disjoint E (fixedSpace ρ L) := by
    apply hd.mono_right
    intro v hv p
    exact hv p.val
  cases h with
  | single hi =>
    exact ⟨markedConstituent_of_containment ρ L E ⊤ P hE hs hdc hi le_top, Or.inl hi⟩
  | double e hc =>
    obtain ⟨b⟩ := binaryLine_of_coordinates _ e E P hE hc hs hd
    obtain ⟨W, hW, hEW⟩ := binaryLine_containing _ e E P b
    have hi : IsIrrPlus ρ L W := (IsIrrPlus.subgroupOf_iff ρ L L le_rfl W).mp
      (by simpa only [Subgroup.subgroupOf_self] using hW)
    exact ⟨markedConstituent_of_containment ρ L E W P hE hs hdc hi hEW,
      Or.inr ⟨e, ⟨b⟩⟩⟩

end Selection

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
