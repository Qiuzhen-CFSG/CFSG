module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Edges.Tree

/-!
# Residual Fi23 exhaustion edges

Tree edges cancel. On each nontrivial A or B cycle, omit the largest
coordinate among the non-tree edges: its factor is the inverse product of
all other factors. Fixed-point loops must still be certified. This leaves
3058 A and 2578 B membership checks in the published data (diagnostic counts,
not premises of the proof). The reduction quantifies over every coordinate.

Source: the original ATLAS F23G1-p31671B0 generators and the fixed exhaustion
words, motivated by GLS3 Table 5.3u. See `Edges/source/README.md`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
open Fi24Prime.Fi23Lift.Certificate

/-- Retain loops and the smaller edge of an A cycle with no tree edge. -/
def ResidualA (x : Fin 31671) : Prop :=
  ¬ TreeEdge false x ∧
    (sourceA x = x ∨ (¬ TreeEdge false (sourceA x) ∧ x.val < (sourceA x).val))

/-- Retain loops and every non-tree B edge except the largest in its cycle. -/
def ResidualB (x : Fin 31671) : Prop :=
  ¬ TreeEdge true x ∧
    (sourceB x = x ∨
      (¬ TreeEdge true (sourceB x) ∧ x.val < (sourceB x).val) ∨
      (¬ TreeEdge true (sourceB (sourceB x)) ∧ x.val < (sourceB (sourceB x)).val))

instance (x : Fin 31671) : Decidable (ResidualA x) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ (_ ∧ _))))

instance (x : Fin 31671) : Decidable (ResidualB x) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ (_ ∧ _) ∨ (_ ∧ _))))

variable (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)

include hA hB

theorem edge_false_mem_of_residual
    (hres : ∀ x, ResidualA x → inclusion (edge false x) ∈ witnessGroup)
    (x : Fin 31671) : inclusion (edge false x) ∈ witnessGroup := by
  by_cases hx : TreeEdge false x
  · exact edge_mem_of_tree hA hB false x hx
  by_cases hy : TreeEdge false (sourceA x)
  · exact edge_false_mem_of_next hA x (edge_mem_of_tree hA hB false _ hy)
  rcases lt_trichotomy x.val (sourceA x).val with hlt | heq | hgt
  · exact hres x ⟨hx, Or.inr ⟨hy, hlt⟩⟩
  · exact hres x ⟨hx, Or.inl (Fin.ext heq.symm)⟩
  · apply edge_false_mem_of_next hA x
    apply hres (sourceA x)
    exact ⟨hy, Or.inr ⟨by simpa only [sourceA_square] using hx,
      by simpa only [sourceA_square] using hgt⟩⟩

theorem edge_true_mem_of_residual
    (hres : ∀ x, ResidualB x → inclusion (edge true x) ∈ witnessGroup)
    (x : Fin 31671) : inclusion (edge true x) ∈ witnessGroup := by
  by_cases hx : TreeEdge true x
  · exact edge_mem_of_tree hA hB true x hx
  by_cases hfix : sourceB x = x
  · exact hres x ⟨hx, Or.inl hfix⟩
  by_cases hr : ResidualB x
  · exact hres x hr
  have hfix₂ : sourceB (sourceB x) ≠ x := by
    intro h
    have he := congrArg sourceB h
    rw [sourceB_cube] at he
    exact hfix he.symm
  apply edge_true_mem_of_next hB x
  · by_cases hy : TreeEdge true (sourceB x)
    · exact edge_mem_of_tree hA hB true _ hy
    have hnlt : ¬ x.val < (sourceB x).val :=
      fun h => hr ⟨hx, Or.inr (Or.inl ⟨hy, h⟩)⟩
    have hne : (sourceB x).val ≠ x.val := fun h => hfix (Fin.ext h)
    have hlt : (sourceB x).val < x.val := by omega
    apply hres (sourceB x)
    exact ⟨hy, Or.inr (Or.inr ⟨by simpa only [sourceB_cube] using hx,
      by simpa only [sourceB_cube] using hlt⟩)⟩
  · by_cases hz : TreeEdge true (sourceB (sourceB x))
    · exact edge_mem_of_tree hA hB true _ hz
    have hnlt : ¬ x.val < (sourceB (sourceB x)).val :=
      fun h => hr ⟨hx, Or.inr (Or.inr ⟨hz, h⟩)⟩
    have hne : (sourceB (sourceB x)).val ≠ x.val := fun h => hfix₂ (Fin.ext h)
    have hlt : (sourceB (sourceB x)).val < x.val := by omega
    apply hres (sourceB (sourceB x))
    exact ⟨hz, Or.inr (Or.inl ⟨by simpa only [sourceB_cube] using hx,
      by simpa only [sourceB_cube] using hlt⟩)⟩

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
