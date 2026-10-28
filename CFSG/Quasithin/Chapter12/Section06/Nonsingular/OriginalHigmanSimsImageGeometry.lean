module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsAllPoints
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsPoint

/-!
# Lifting the original HS action image

The inner part of the original action has a common fixed letter in the
degree-100 HS action. Its full preimage inside the actual component is
precisely the original moved subgroup. Consequently an element of the
actual point centralizer normalizing the action image normalizes that
moved subgroup upstairs, retaining the entire covering center.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Every inner element of the original action image fixes the same actual
letter in the HS permutation model. -/
theorem SourceHypothesis.nonsingular_hs_original_image_common_fixed_point
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    let E := (V.subgroupOf (Gv (v : G))).map (nonsingularModelAction (v : G) e)
    ∃ p : Fin 100, ∀ x : Sporadic.LeechRelated.HS.Carrier,
      MulAut.conj x ∈ E → (x : Equiv.Perm (Fin 100)) p = p := by
  let a := nonsingularModelAction (v : G) e
  let E := (V.subgroupOf (Gv (v : G))).map a
  have hWC := (H.nonsingular_component_rank D v hv).1
  have hi := (H.nonsingular_hs_original_inner_part D v hv hK e).2.2.1
  obtain ⟨p,hp⟩ := H.nonsingular_hs_moved_image_fixed_point D v hv hK e
  refine ⟨p,?_⟩
  intro x hx
  have hxW : MulAut.conj x ∈ ((Vv L V (v : G)).subgroupOf (Gv (v : G))).map a :=
    hi ▸ ⟨hx,⟨x,rfl⟩⟩
  rw [nonsingularModelAction_map (v : G) e _ hWC] at hxW
  obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hxW
  have he : e (QuotientGroup.mk' (center (Kv (v : G))) z) = x :=
    (MulAut.conj_injective_of_center_eq_bot
      Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot) hy
  exact he ▸ hp z hz

/-- The component preimage of the original action image is exactly the
original moved subgroup, including its full central kernel. -/
theorem SourceHypothesis.nonsingular_hs_component_image_mem_iff
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (x : Kv (v : G)) :
    nonsingularModelAction (v : G) e (inclusion (Kv_le_Gv (v : G)) x) ∈
        (V.subgroupOf (Gv (v : G))).map (nonsingularModelAction (v : G) e) ↔
      (x : G) ∈ Vv L V (v : G) := by
  let a := nonsingularModelAction (v : G) e
  have hWC := (H.nonsingular_component_rank D v hv).1
  constructor
  · intro hx
    have hi := (H.nonsingular_hs_original_inner_part D v hv hK e).2.2.1
    have hxW : a (inclusion (Kv_le_Gv (v : G)) x) ∈
        ((Vv L V (v : G)).subgroupOf (Gv (v : G))).map a := by
      rw [←hi]
      exact ⟨hx,by rw [nonsingularModelAction_on_component]; exact ⟨_,rfl⟩⟩
    rw [nonsingularModelAction_map (v : G) e _ hWC] at hxW
    obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hxW
    rw [nonsingularModelAction_on_component] at hy
    have he : e (QuotientGroup.mk' (center (Kv (v : G))) z) =
        e (QuotientGroup.mk' (center (Kv (v : G))) x) :=
      (MulAut.conj_injective_of_center_eq_bot
        Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot) hy
    exact (H.nonsingular_hs_moved_full_preimage D v hv hK e).le ⟨z,hz,he⟩
  · intro hx
    exact mem_map_of_mem _ ((Vv_le_V H.chosen.normalizes _) hx)

/-- Normalization of the actual action image lifts to normalization of
the original moved subgroup in the full ambient group. -/
theorem SourceHypothesis.nonsingular_hs_image_normalizer_preserves_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (c : Gv (v : G))
    (hc : nonsingularModelAction (v : G) e c ∈ normalizer
      (((V.subgroupOf (Gv (v : G))).map (nonsingularModelAction (v : G) e) :
        Subgroup (MulAut Sporadic.LeechRelated.HS.Carrier)) : Set _)) :
    (c : G) ∈ normalizer (Vv L V (v : G) : Set G) := by
  let a := nonsingularModelAction (v : G) e
  have hn : (c : G) ∈ normalizer (Kv (v : G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp
      (Kv_normalIn_Gv (v : G)) c.property
  have hWC := (H.nonsingular_component_rank D v hv).1
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    let y : Kv (v : G) := ⟨x,hWC hx⟩
    let z : Kv (v : G) := ⟨(c : G)*x*(c : G)⁻¹,
      (mem_normalizer_iff.mp hn x).mp y.property⟩
    apply (H.nonsingular_hs_component_image_mem_iff D v hv hK e z).mp
    have hy := (H.nonsingular_hs_component_image_mem_iff D v hv hK e y).mpr hx
    have hz := (mem_normalizer_iff.mp hc _).mp hy
    have hzy : inclusion (Kv_le_Gv (v : G)) z = c * inclusion (Kv_le_Gv (v : G)) y * c⁻¹ := Subtype.ext rfl
    simpa only [hzy,map_mul,map_inv] using hz
  · intro hx
    have hxK : x ∈ Kv (v : G) := (mem_normalizer_iff.mp hn x).mpr (hWC hx)
    let y : Kv (v : G) := ⟨x,hxK⟩
    let z : Kv (v : G) := ⟨(c : G)*x*(c : G)⁻¹,hWC hx⟩
    apply (H.nonsingular_hs_component_image_mem_iff D v hv hK e y).mp
    have hz := (H.nonsingular_hs_component_image_mem_iff D v hv hK e z).mpr hx
    apply (mem_normalizer_iff.mp hc _).mpr
    have hzy : inclusion (Kv_le_Gv (v : G)) z = c * inclusion (Kv_le_Gv (v : G)) y * c⁻¹ := Subtype.ext rfl
    rwa [hzy,map_mul,map_mul,map_inv] at hz

end CFSG.Quasithin.Chapter12.Section06
