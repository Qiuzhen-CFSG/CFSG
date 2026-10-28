module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Reduced

/-!
# The b=1 core calculation on the original F1.11 markings

The reduced graph core maps through the actual reduced-completion inclusion
to the original full parabolic core. Applying the paired Frattini calculation
therefore identifies each original core with the image of the actual reduced
Sylow-center span. The original Sylow is not identified with O2(B).

The opposite natural-action geometry is explicit and remains to be constructed
in the Chapter 10 proof. This is a conditional application of its structural
core calculation, not a completed local-profile or recognition theorem.

Source: DGS, *Groups and Graphs* (1985), Part II, reduction pp.95--96 and
10.4--10.5, pp.155--156; Aschbacher--Smith F.1.9, pp.261--262.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The graph core maps to the original endpoint core, through the literal
reduced completion inclusion; the whole original parabolic is retained. -/
theorem reduced_base_Q_map (h : HypothesisF11 L S) (i : Bool) :
    (Q (reducedFamily L S) (base (reducedFamily L S) i)).map (G₀ L S).subtype =
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
  change ((stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).pCoreIn 2).map
    (G₀ L S).subtype = _
  rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
  have hle (j : Fin 2) : P₀ L S j ≤ G₀ L S := by
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  cases i <;>
    rw [reducedFamily, family,
      ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2
        (G₀ L S).subtype (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le (hle _), P₀_core h]
  all_goals simp

/-- Literal F1.11 application of the b=1 core calculation. The opposite
natural-action geometry is still explicit; the original cores and the
reduced-to-original inclusion are not replaced by abstract isomorphisms. -/
theorem original_cores_eq_reduced_center_spans (h : HypothesisF11 L S)
    {u₀ u₁ : Vertex (reducedFamily L S)}
    (d₀ : OppositeCenterGeometry (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) u₀)
    (d₁ : OppositeCenterGeometry (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) u₁) :
    (parabolic L S 0).pCoreIn 2 =
        (Z (reducedFamily L S) (base (reducedFamily L S) false)).map (G₀ L S).subtype ∧
    (parabolic L S 1).pCoreIn 2 =
        (Z (reducedFamily L S) (base (reducedFamily L S) true)).map (G₀ L S).subtype := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers (reduced_triple h) d₀ d₁
  exact ⟨(reduced_base_Q_map h false).symm.trans (congrArg (map (G₀ L S).subtype) h₀),
    (reduced_base_Q_map h true).symm.trans (congrArg (map (G₀ L S).subtype) h₁)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
