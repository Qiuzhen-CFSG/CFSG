module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearNeighborOrbits
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonlinearCoreGeneration

/-!
# Neighbor-core transitivity at the original small Suzuki endpoint

The prescribed common Sylow identifies the image of the entire opposite
core with a Sylow of the literal Sz(2) quotient. Its actual five-point
ovoid action is transitive away from the point fixed by its normalizer.
Matching that normalizer with the original neighbor stabilizer lifts the
orbit through the same source quotient map.

This supplies the parameter-zero neighbor orbit needed by the quintic
nine-path argument. No full generation by two omega subgroups is used.
Source: DGS, Groups and Graphs (1985), 12.1(c,e) and 12.3(a), pp.178--179,
with the actual order-twenty Suzuki action at the small parameter.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The earlier common-Sylow identity makes the opposite vertex core
transitive on the remaining neighbors at the marked Suzuki vertex. -/
theorem small_suzuki_neighbor_core_transitive
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S i))
    (hcommon : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {y z : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hyx : y ≠ base (reducedFamily L S) (!i))
    (hzx : z ≠ base (reducedFamily L S) (!i)) :
    ∃ t ∈ Q (reducedFamily L S) (base (reducedFamily L S) (!i)), t • y = z := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext t
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  let R : Sylow 2 (SuzukiMatrixGroup 0) := T.mapSurjective (f := f) hf
  have hRT : (R : Subgroup (SuzukiMatrixGroup 0)).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  let D := (Q F (base F (!i))).subgroupOf A
  have hDA : Q F (base F (!i)) ≤ A :=
    (le_sup_left.trans hcommon.ge).trans (map_subtype_le _)
  have hTsup : (T : Subgroup A) = D ⊔ pCore 2 A := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hDA]
    change _ = _ ⊔ A.pCoreIn 2
    rw [star_core h i]
    exact hcommon
  have hDmap : D.map f = (R : Subgroup (SuzukiMatrixGroup 0)) := by
    change D.map f = (T : Subgroup A).map f
    rw [hTsup, Subgroup.map_sup]
    have hh : (pCore 2 A).map f = ⊥ := by
      rw [← hk]
      apply bot_unique
      rintro a ⟨t, ht, rfl⟩
      exact ht
    rw [hh, sup_bot_eq]
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨T₀, hT₀⟩ := base_star_sylow_normalizer h i
  have hTfix : (T : Subgroup A).map A.subtype ≤ stabilizer F (base F (!i)) := by
    rw [hcommon]
    exact sup_le (Q_le_stabilizer F _) (((source_Z_Q_U (reduced_triple h) (base F i)).2.trans
      (ballKernel_one_le_edge F hadj)).trans inf_le_right)
  have heT : T = T₀ := sylow_le_normalizer_eq T₀ T (by
    rw [← hT₀]
    exact fun t ht => hTfix (mem_map_of_mem A.subtype ht))
  obtain ⟨p, hp, htrans⟩ := CommutingOneProfile.small_suzuki_orbits R
  have hstab : (MulAction.stabilizer (SuzukiMatrixGroup 0) p).comap f =
      MulAction.stabilizer A (base F (!i)) := by
    rw [← hp]
    change (normalizer ((R : Subgroup (SuzukiMatrixGroup 0)) : Set (SuzukiMatrixGroup 0))).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf, hRT, Sylow.coe_coe, heT, ← hT₀]
    rfl
  obtain ⟨a, ha, hay⟩ := star_locally_transitive h i hadj hy
  obtain ⟨c, hc, hcz⟩ := star_locally_transitive h i hadj hz
  obtain ⟨t, ht, he⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base f D
    (base F (!i)) p hstab (by rw [hDmap]; exact htrans) (⟨a, ha⟩ : A) (⟨c, hc⟩ : A)
    (by simpa only [Subgroup.mk_smul, hay] using hyx)
    (by simpa only [Subgroup.mk_smul, hcz] using hzx)
  refine ⟨t, ht, ?_⟩
  change (t : G₀ L S) • (a • base F (!i)) = c • base F (!i) at he
  rwa [hay, hcz] at he


end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
