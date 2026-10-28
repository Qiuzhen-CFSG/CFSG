module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingActor
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducible

/-!
# The remaining core geometry in alternating row (d)

The actual fixed-space quotient in row (d) reconstructs a six- or eight-
letter augmentation core. This eliminates the odd-degree rows and every
other central extension. In degree eight the multiplier bound also recovers
the original L/O₂(L) actor. Two independent source branches remain: TI for
the six-letter core, and the selected outside fusion pair with its literal
point Sylow in degree eight. They are explicit inputs below.

The second theorem connects this reduction to the original reducible-row
consumer, including the already proved A₈ fixed-line and Sylow adjustment.
These conditional assemblies do not assert the unresolved core geometry.

Source: Aschbacher–Smith, 12.2.16, pp.799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Only the actual six- and eight-letter core geometries remain in row (d).
The degree-eight input uses the recovered original L/O₂(L) conjugation model. -/
theorem alternating_of_core_geometry (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (six : (letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (BinaryPermutation.alternatingCoreRepresentation (Fin 6))) →
        IsTISubgroup V)
    (eight : Chapter6.Source.IsConjugationModel L V
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)) →
        IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V))
    (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n)) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V) := by
  obtain ⟨hn,⟨E⟩⟩ := alternating_core_of_nonzero_fixed D hne n hlo hhi e
  rcases hn with rfl | rfl
  · exact Or.inl (six E)
  · exact eight (alternatingEight_conjugationModel_of_faithfulAction D hq E)

/-- Application to all reducible source rows. The core geometries and the
independent G₂ Weyl geometry are the remaining mathematical inputs. -/
theorem reducible_of_alternating_core_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (six : (letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (BinaryPermutation.alternatingCoreRepresentation (Fin 6))) →
        IsTISubgroup V)
    (eight : Chapter6.Source.IsConjugationModel L V
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)) →
        IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V))
    (g2 : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) →
        IsTISubgroup V) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  exact reducible_of_geometric_rows h D structural hnone rows hne
    (alternating_of_core_geometry D h.quasisimple hne six eight) g2

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
