module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.OddDegree.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.Residual

/-!
# Original Sylow and Cartan placement in the common-core normalizer

The completed odd-degree argument puts T in L. The actual flag calculation
then places T in V L₂, hence in Y=⟨L₂,I⟩. This removes the Sylow-containment
premise from the odd-index residual reduction: only relative normality of Y
remains. The original Cartan normalizes the second flag member, its local
residual, and its characteristic two-core P. Thus X lies in G_P without
assuming an orthogonal marking or Cartan recognition in Y.

Source: Aschbacher--Smith, printed p.774, the paragraph after odd degree.
Relative component recognition and the final orthogonal/Cartan assembly
remain with the common-core orthogonal owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- The original Sylow belongs to the literal Y, by the flag geometry. -/
theorem source_sylow_le_orthogonalJoin :
    (T : Subgroup G) ≤ orthogonalJoin (f.Li 1) V h :=
  (source_sylow_le_local_join_seed d (source_original_sylow_placement d).2.1).trans
    (sup_le le_sup_left (le_sup_left.trans le_sup_right))

/-- Only relative normality remains to identify Y as the odd-index residual. -/
theorem source_orthogonalJoin_eq_oddResidual_of_normal
    (hn : ((orthogonalJoin (f.Li 1) V h).subgroupOf (coreNormalizer V H h)).Normal) :
    orthogonalJoin (f.Li 1) V h =
      (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype :=
  source_orthogonalJoin_eq_oddResidual_of_normal_sylow d hn (source_sylow_le_orthogonalJoin d)

/-- The original Cartan preserves each of the actual local residuals. -/
theorem source_cartan_normalizes_local (i : Fin 2) :
    X ≤ normalizer (f.Li i : Set G) := by
  have hn : X ≤ normalizer (f.Vi i.castSucc : Set G) := by
    rw [source_flag_eq d]
    exact SL3.cartan_normalizes D S m d.cartan i.castSucc
  change X ≤ normalizer (localResidual L (f.Vi i.castSucc) : Set G)
  exact ((le_inf ((d.cartan.1.trans inf_le_left).trans L.le_normalizer)
    (hn.trans (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

/-- Cartan containment in G_P uses the literal P=O₂(L₂). -/
theorem source_cartan_le_coreNormalizer : X ≤ coreNormalizer V H h := by
  rw [coreNormalizer,←d.local_core]
  exact (source_cartan_normalizes_local d 1).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
