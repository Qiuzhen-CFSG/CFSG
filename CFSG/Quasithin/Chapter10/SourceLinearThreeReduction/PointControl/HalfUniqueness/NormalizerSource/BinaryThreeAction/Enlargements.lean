module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Parabolics
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction

/-!
# The literal normalizer enlargement in source 10.2.5

For a source parabolic H, put X = O²(H), E = <N_G(T₁),H>,
K = <X^E>, and R = T₁ ∩ K. These are the actual subgroups in the
normalizer argument. The original full Sylow restricts to K; R has index
at most two in that restriction and is normalized by N_G(T₁).
The strict branch retains every model in the corrected 10.2.4 list,
including Held. No model-normalizer conclusion is assumed or asserted.

Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

/-- The source's full normalizer enlargement, not a chosen overgroup. -/
def enlargement (T : Sylow 2 G) (L H : Subgroup G) : Subgroup G :=
  normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ⊔ H

/-- The actual normal closure of the parabolic's two-residual. -/
def enlargedResidual (T : Sylow 2 G) (L H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (residual H) (enlargement T L H)

/-- The literal R=T₁∩K, rather than an arbitrary interval subgroup. -/
def stabilizerIntersection (T : Sylow 2 G) (L H : Subgroup G) : Subgroup G :=
  ((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊓ enlargedResidual T L H

theorem Data.enlargement_two_core_ne_bot (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (enlargement T L H).pCoreIn 2 ≠ ⊥ := h.enlargement_mem_H hn

theorem Data.residual_le_enlargedResidual (_h : Data D H) :
    residual H ≤ enlargedResidual T L H := le_conjugateSpanBy _ _

theorem Data.enlargedResidual_le_enlargement (_h : Data D H) :
    enlargedResidual T L H ≤ enlargement T L H :=
  conjugateSpanBy_le_self ((map_subtype_le (pResidual 2 H)).trans le_sup_right)

/-- Normality here is relative to the genuine enlargement E. -/
theorem Data.enlargedResidual_normal (_h : Data D H) :
    ((enlargedResidual T L H).subgroupOf (enlargement T L H)).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)

theorem Data.normalizer_normalizes_enlargedResidual (_h : Data D H) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (enlargedResidual T L H : Set G) :=
  le_sup_left.trans (le_normalizer_conjugateSpanBy _ _)

/-- Both factors of R are normalized by the original N_G(T₁). -/
theorem Data.normalizer_normalizes_intersection (h : Data D H) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (stabilizerIntersection T L H : Set G) := by
  intro g hg
  change g ∈ normalizer ((((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊓
    enlargedResidual T L H) : Set G)
  exact (inf_normalizer_le_normalizer_inf
    (H := (T : Subgroup G) ⊓ normalizer (L : Set G))
    (K := enlargedResidual T L H)) ⟨hg,h.normalizer_normalizes_enlargedResidual hg⟩

theorem Data.sylow_normalizes_enlargedResidual (h : Data D H) :
    (T : Subgroup G) ≤ normalizer (enlargedResidual T L H : Set G) :=
  (h.sylow_le.trans le_sup_right).trans (le_normalizer_conjugateSpanBy _ _)

/-- A.1.6 on the actual Sylow overgroup H bounds the enlargement's core. -/
theorem Data.enlargement_core_le_parabolic_core (h : Data D H) :
    (enlargement T L H).pCoreIn 2 ≤ H.pCoreIn 2 := by
  have hc : (enlargement T L H).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTE : (T : Subgroup G) ≤ enlargement T L H := h.sylow_le.trans le_sup_right
    have hh := pCoreIn_le_sylow (enlargement T L H) (T.subtype hTE)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTE] at hh
    exact hh
  exact (le_inf (hc.trans h.sylow_le) le_rfl).trans
    (inf_pCoreIn_le_of_le 2 le_sup_right)

/-- The two-core of K lies in the literal R, including its T₁ condition. -/
theorem Data.enlargedResidual_core_le_intersection (h : Data D H) :
    (enlargedResidual T L H).pCoreIn 2 ≤ stabilizerIntersection T L H := by
  have hc := pCoreIn_mono_of_normalizes h.enlargedResidual_le_enlargement
    (le_normalizer_conjugateSpanBy (residual H) (enlargement T L H)) (p := 2)
  exact le_inf ((hc.trans h.enlargement_core_le_parabolic_core).trans h.core_le_stabilizer)
    (pCoreIn_le 2 _)

/-- The parabolic intersection is exactly X(T∩K), with the original X. -/
theorem Data.parabolic_intersection (h : Data D H) :
    residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H) =
      H ⊓ enlargedResidual T L H := by
  have hXH : residual H ≤ H := map_subtype_le _
  have hnX : H ≤ normalizer (residual H : Set G) := by
    have hn := (pResidual 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype,residual] using hn
  apply le_antisymm
  · exact sup_le (le_inf hXH h.residual_le_enlargedResidual)
      (le_inf (inf_le_left.trans h.sylow_le) inf_le_right)
  · rintro g ⟨hgH,hgK⟩
    have hg : g ∈ (residual H : Set G) * (T : Set G) := by
      change g ∈ (residual H : Set G) * ((T : Subgroup G) : Set G)
      rw [← coe_mul_of_right_le_normalizer_left (residual H) (T : Subgroup G)
        (h.sylow_le.trans hnX),h.residual_sup_sylow]
      exact hgH
    obtain ⟨x,hx,t,ht,hxt⟩ := hg
    have htK : t ∈ enlargedResidual T L H := by
      have hm := (enlargedResidual T L H).mul_mem
        ((enlargedResidual T L H).inv_mem (h.residual_le_enlargedResidual hx)) hgK
      rwa [← hxt,inv_mul_cancel_left] at hm
    rw [← hxt]
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨ht,htK⟩)

/-- The precise lower core bound in (*) on printed p.748. -/
theorem Data.parabolic_intersection_core_le (h : Data D H) :
    (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2 ≤
      stabilizerIntersection T L H := by
  rw [h.parabolic_intersection]
  have hn : H ≤ normalizer (H ⊓ enlargedResidual T L H : Set G) :=
    (le_inf H.le_normalizer (le_sup_right.trans (le_normalizer_conjugateSpanBy _ _))).trans
      inf_normalizer_le_normalizer_inf
  exact le_inf ((pCoreIn_mono_of_normalizes inf_le_left hn).trans h.core_le_stabilizer)
    ((pCoreIn_le 2 _).trans inf_le_right)

/-- Restrict the original Sylow to K using K's relative normality in E. -/
theorem Data.enlargedResidual_sylow (h : Data D H) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ enlargedResidual T L H)
      (enlargedResidual T L H) := by
  let E := enlargement T L H
  let K := enlargedResidual T L H
  let P := T.subtype (h.sylow_le.trans (show H ≤ E from le_sup_right))
  let : (K.subgroupOf E).Normal := h.enlargedResidual_normal
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal (K.subgroupOf E)
  let e := subgroupOfEquivOfLe h.enlargedResidual_le_enlargement
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup (K.subgroupOf E)).map e.toMonoidHom).map K.subtype = _
  have hc : K.subtype.comp e.toMonoidHom = E.subtype.comp (K.subgroupOf E).subtype := rfl
  rw [Subgroup.map_map,hc,← Subgroup.map_map,hQ,
    Subgroup.map_inf _ _ _ E.subtype_injective]
  rw [show (P : Subgroup E).map E.subtype = (T : Subgroup G) from
    map_subgroupOf_eq_of_le (h.sylow_le.trans le_sup_right),
    map_subgroupOf_eq_of_le h.enlargedResidual_le_enlargement]

/-- The source index bound uses exactly the original index-two stabilizer. -/
theorem Data.intersection_relIndex_le_two (_h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (stabilizerIntersection T L H).relIndex
      ((T : Subgroup G) ⊓ enlargedResidual T L H) ≤ 2 := by
  let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have he : T₁.relIndex (T : Subgroup G) = 2 := by
    rw [inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have hi : stabilizerIntersection T L H =
      T₁ ⊓ ((T : Subgroup G) ⊓ enlargedResidual T L H) := by
    dsimp [stabilizerIntersection,T₁]
    ext x
    exact ⟨fun hx => ⟨hx.1,hx.1.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  rw [hi,inf_relIndex_right]
  exact (relIndex_le_of_le_right inf_le_left (by rw [he]; decide)).trans_eq he

/-- Failure to normalize X makes its actual normal closure strictly larger. -/
theorem Data.residual_lt_enlargedResidual (h : Data D H)
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) :
    residual H < enlargedResidual T L H := by
  refine lt_of_le_of_ne h.residual_le_enlargedResidual ?_
  intro he
  exact hN (he.symm ▸ h.normalizer_normalizes_enlargedResidual)

/-- The non-normalizing branch reaches an actual component and its model,
with the strict closure and literal R retained for the subsequent calculation. -/
theorem Data.strict_models (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) :
    residual H < enlargedResidual T L H ∧ ∃ I : Subgroup G,
      I ∈ Chapter1.cComponentsIn (enlargement T L H) ∧
      IsQuasisimple (Chapter1.XiQuotient I) ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      SourceLinearThreeReplacement.Overgroups.ClosureModel T I := by
  have hlt := h.residual_lt_enlargedResidual hN
  exact ⟨hlt,(h.normalClosure_models hn).resolve_left hlt.ne'⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
