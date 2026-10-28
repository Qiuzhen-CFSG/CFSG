module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionElementary
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The local centralizer and residual in the equality extension

The pointwise eight-group calculation puts C_H(V) inside T. Since z lies
in V, every element centralizing V lies in H, and C_M(V) = O₂(LT).
The earlier-source residual O²(H ∩ M) centralizes V, hence is a two-group;
two-perfection forces it to vanish. The residual–Sylow supplement gives
H ∩ M = T. No bound on C_H(K) or marked S₅ quotient is assumed.

These are the centralizer and residual steps of Aschbacher–Smith 6.2.13,
printed pp.687–688. The remaining marked quotient and transfer arguments
stay with the equality-geometry owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The actual maximal-local action kernel is its elementary two-core. -/
theorem LocalAnalysis.equality_maximal_layer_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    M ⊓ centralizer (layer L R : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := centralizer ({z} : Set G)
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hc := A.equality_layer_centralizer_in_H h611 hnatural hz hp.plusType
  have hVH := layer_le_involution_centralizer h611 hz
  have hmap := congrArg (fun B : Subgroup H => B.map H.subtype) hc
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hVH] at hmap
  change _ = layer L R ⊔ equalityCentralizer L R z at hmap
  have hHC : H ⊓ centralizer (layer L R : Set G) =
      layer L R ⊔ equalityCentralizer L R z := by
    rw [← hmap]
    apply le_antisymm
    · intro x hx
      refine ⟨⟨x,hx.1⟩, ?_, rfl⟩
      intro v hv
      apply Subtype.ext
      exact hx.2 v hv
    · rintro x ⟨xH,hx,rfl⟩
      refine ⟨xH.property, ?_⟩
      intro v hv
      exact congrArg Subtype.val (hx ⟨v,hVH hv⟩ hv)
  have hCH : centralizer (layer L R : Set G) ≤ H := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx z hz.1).symm
  have hQC := local_core_centralizes_layer h611
  have hQM : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ M :=
    (pCoreIn_le 2 _).trans (sup_le h611.L_le h611.sylow_le)
  apply le_antisymm
  · have hQ := A.equality_sylow_layer_centralizer h611 hnatural hz hTH hp.plusType
    rw [equality_sylow_centralizer_eq_core h611 hnatural] at hQ
    rw [hQ]
    exact (le_inf (inf_le_right.trans hCH) inf_le_right).trans hHC.le
  · exact le_inf hQM hQC

/-- The earlier residual-centralizer clause now forces the residual to vanish. -/
theorem LocalAnalysis.equality_intersection_residual_eq_bot
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    pResidual 2 (centralizer ({z} : Set G) ⊓ M : Subgroup G) = ⊥ := by
  let N := centralizer ({z} : Set G) ⊓ M
  let Y := (pResidual 2 N).map N.subtype
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hYQ : Y ≤ Q := by
    change Y ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← A.equality_maximal_layer_centralizer h611 hnatural hz horder hTH hbranch]
    exact le_inf ((map_subtype_le _).trans inf_le_right) A.residual_centralizes
  have htriv := (isPPerfect_embedded_pResidual 2 N).hom_eq_one_of_isPGroup
    (isPGroup_pCoreIn 2 _) (inclusion hYQ)
  have hY : Y = ⊥ := by
    apply bot_unique
    intro y hy
    exact congrArg (fun f : Y →* Q => (f ⟨y,hy⟩ : G)) htriv
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp hY

/-- The chosen involution centralizer meets M in the original Sylow subgroup. -/
theorem LocalAnalysis.equality_intersection_eq_sylow
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    centralizer ({z} : Set G) ⊓ M = (T : Subgroup G) := by
  let N := centralizer ({z} : Set G) ⊓ M
  have hr := A.equality_intersection_residual_eq_bot h611 hnatural hz horder hTH hbranch
  have h := congrArg (fun B : Subgroup N => B.map N.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype (le_inf hTH h611.sylow_le)))
  rw [hr, bot_sup_eq, Sylow.coe_subtype, map_subgroupOf_eq_of_le
    (le_inf hTH h611.sylow_le), ← MonoidHom.range_eq_map, range_subtype] at h
  exact h.symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
