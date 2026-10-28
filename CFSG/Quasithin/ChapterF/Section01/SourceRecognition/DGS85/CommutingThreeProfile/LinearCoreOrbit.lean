module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearNeighborOrbits
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearNeighborOrbits
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration

/-!
# The actual common Sylow orbit at a linear vertex

The supplied core product is a Sylow in the starred linear endpoint and
fixes the opposite base vertex. Uniqueness in the corresponding Sylow
normalizer identifies it with the model root group. Its original action
is transitive on all the other neighbors. This refines the earlier
full-edge-core orbit to the literal core product needed to transport the
span--core intersections in (12.9).

Source: DGS85, Groups and Graphs, (12.1)(c,e), (12.9), pp.178,188.
The implementation imports reuse the established projective-line orbit
and base Sylow normalizer without changing their public boundaries.
-/

public noncomputable section
open Subgroup
open BenderSuzuki.Converse
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The two actual cores move every nonbase neighbor to every other one. -/
theorem linear_common_sylow_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {y z : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hyx : y ≠ base (reducedFamily L S) (!i))
    (hzx : z ≠ base (reducedFamily L S) (!i)) :
    ∃ t ∈ Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
      Q (reducedFamily L S) (base (reducedFamily L S) i), t • y = z := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F (base F (!i)) ⊓ stabilizer F (base F i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F (base F i) from inf_le_right))
    (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  obtain ⟨T₀, hT₀⟩ := base_star_sylow_normalizer h i
  have hTT : T = T₀ := sylow_le_normalizer_eq T₀ T (by
    rw [←hT₀]
    intro t ht
    have hm := hT ▸ mem_map_of_mem A.subtype ht
    exact (sup_le (Q_le_stabilizer F _) ((source_Z_Q_U (reduced_triple h) _).2.trans
      ((ballKernel_one_le_edge F (show (graph F).Adj (base F i) (base F (!i)) from
        ⟨by change i ≠ !i; cases i <;> decide,
          Subgroup.CosetGeometry.incident_base F i (!i)⟩)).trans inf_le_right))) hm)
  have hTN := hTT ▸ hT₀
  let R : Sylow 2 (SL2 k) := T.mapSurjective (f := f) hf
  have hRT : (R : Subgroup (SL2 k)).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    have hk : f.ker = pCore 2 A := by
      ext t
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff t
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  obtain ⟨p, hp, htrans⟩ := sylow_affine_transitive R
  have hstab : (MulAction.stabilizer (SL2 k) p).comap f = MulAction.stabilizer A (base F (!i)) := by
    rw [← hp]
    change (normalizer ((R : Subgroup (SL2 k)) : Set (SL2 k))).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf, hRT, Sylow.coe_coe, ← hTN]
    rfl
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a, ha, hay⟩ := star_locally_transitive h i hadj hy
  obtain ⟨c, hc, hcz⟩ := star_locally_transitive h i hadj hz
  obtain ⟨t, ht, he⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base f (T : Subgroup A)
    (base F (!i)) p hstab htrans (⟨a, ha⟩ : A) (⟨c, hc⟩ : A)
    (by simpa only [Subgroup.mk_smul, hay] using hyx)
    (by simpa only [Subgroup.mk_smul, hcz] using hzx)
  refine ⟨t, hT ▸ mem_map_of_mem A.subtype ht, ?_⟩
  change (t : G₀ L S) • (a • base F (!i)) = c • base F (!i) at he
  rwa [hay, hcz] at he

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
