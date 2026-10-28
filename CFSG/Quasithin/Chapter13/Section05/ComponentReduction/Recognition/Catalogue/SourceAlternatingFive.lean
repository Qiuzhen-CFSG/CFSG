module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceRows
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# Excluding the original alternating-five chief row

Sylow centrality makes the marked involution inner in PSL₂(4)=A₅.
Its conjugate pair condition forces the field to have at most two elements,
a contradiction. The actual chief comparison then excludes the complete
symmetric-five catalogue row without any module-dimension assumption.
Source: Aschbacher–Smith13.5.21, p.924.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source Configuration LocalModels.DefiningFields
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The source marked pair geometry excludes the actual simple quotient A₅. -/
theorem source_not_alternatingFive
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    (e : Khat s h ≃* alternatingGroup (Fin 5)) : False := by
  let f := e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm
  obtain ⟨m⟩ := source_linearTwo_marking s h Y c.proved_prefix (GaloisField 2 2) f
  have hc := Theory.PSL2.field_card_le_two_of_involution_pairs (f m.generator)
    ((f.orderOf_eq m.generator).trans m.order) ((m.pairs s h c.condition_iv).map_equiv f)
  rw [GaloisField.card 2 2 (by decide)] at hc
  norm_num at hc

/-- A central-quotient comparison retains the original chief model. -/
theorem source_not_five_chief_quotient {E : Type*} [Group E] (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L))
    (row : L ≃* alternatingGroup (Fin 5))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) : False := by
  have hZ : center L = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : row x ∈ center (alternatingGroup (Fin 5)) :=
      ((centerCongr row) ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact row.map_eq_one_iff.mp he
  exact source_not_alternatingFive s h Y hY c
    (comparison.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans row)))

variable [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The literal source chief image cannot have the alternating-five component. -/
theorem source_chief_not_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hirr : IsIrreducible (chiefRepresentation D K h U N))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) :
    ¬ Nonempty (generalizedFitting (actionImage (chiefRepresentation D K h U N)) ≃*
      alternatingGroup (Fin 5)) := by
  rintro ⟨row⟩
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  exact source_not_five_chief_quotient s h _ comparison row Y hY c
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
