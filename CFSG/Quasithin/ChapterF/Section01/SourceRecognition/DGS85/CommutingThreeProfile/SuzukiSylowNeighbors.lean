module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NinePathUntrappedCentralizer

/-!
# Common Sylow images at arbitrary neighbors

A common Sylow image on the base edge propagates to every neighbor of the
marked endpoint by the local star action.  This is the public extension of
the conjugation calculation used internally by the nine-path centralizer
argument; it retains the literal `Q`-image equation needed by the later
Suzuki consumers.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Propagate a marked common Sylow image to any incident edge. -/
theorem source_common_sylow_neighbors
    (h : HypothesisF11 L S) (i : Bool) (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    ∀ v, (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v →
      ∃ R : Sylow 2 (star L S i),
        (R : Subgroup (star L S i)).map (star L S i).subtype =
          Q (reducedFamily L S) v ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let F := reducedFamily L S
  let P := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite P := Finite.of_injective (inclusion (star_le_stabilizer i))
    (inclusion_injective _)
  intro v hv
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,
      Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g, hg, hgm⟩ := star_locally_transitive h i hadj hv
  have hgy : g • base F i = base F i := star_le_stabilizer i hg
  let t : P := ⟨g, hg⟩
  let R := T.mapSurjective (f := (MulAut.conj t).toMonoidHom)
    (MulAut.conj t).surjective
  have hf : P.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp P.subtype := by
    ext u
    rfl
  refine ⟨R, ?_⟩
  change ((T : Subgroup P).map (MulAut.conj t).toMonoidHom).map P.subtype = _
  rw [Subgroup.map_map, hf, ← Subgroup.map_map, hT, Subgroup.map_sup,
    ← Q_translate F, ← Q_translate F, hgm, hgy]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
