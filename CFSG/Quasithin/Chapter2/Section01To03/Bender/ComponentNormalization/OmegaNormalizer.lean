module
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAction
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OmegaNormalizer.Models

/-!
# Bender component control from the actual model

A component intersects the original centralizer Sylow in a Sylow subgroup.
The nested-subgroup maps identify its ambient first omega with exactly
`componentOmega H L S`. Concrete Bender-model simplicity and component
perfectness give centerlessness. The model normalizer theorem supplies the
size, transitivity and cyclic odd image on that same embedded subgroup.
These discharge every intrinsic geometry input of the existing whole-U
Bender consumer. The original z-innerness, Sylow placement, odd-core,
maximality and balance hypotheses retain their source meanings.

Source: Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520.
The earlier component selection is 1.1.5--6 and balance is I.3.2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The actual component Sylow embedding supplies all model-dependent inputs
of the Bender omega consumer. The action is the full relative normalizer image. -/
theorem bender_component_omega_inputs (H L : Subgroup G) (S : Sylow 2 H)
    (hL : IsComponentIn L H) (hm : ClassificationModels.IsBenderModel L) :
    Disjoint L (centralizer (L : Set G)) ∧
    2 < Nat.card (componentOmega H L S) ∧
    IsCyclic (normalizerAction L (componentOmega H L S)).range ∧
    Odd (Nat.card (normalizerAction L (componentOmega H L S)).range) ∧
    (∀ a ∈ componentOmega H L S, a ≠ 1 → ∀ b ∈ componentOmega H L S, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (componentOmega H L S : Set G), n * a * n⁻¹ = b) := by
  let : IsQuasisimple L := hL.quasisimple
  let : Nontrivial L := (nontrivial_iff_ne_bot L).mpr hL.ne_bot
  have hc := OmegaNormalizerModels.centerless_of_bender_model hm
  have hd : Disjoint L (centralizer (L : Set G)) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    rintro x ⟨hxL, hxC⟩
    have hz : (⟨x, hxL⟩ : L) ∈ center L := mem_center_iff.mpr fun y =>
      Subtype.ext (mem_centralizer_iff.mp hxC y y.property)
    rw [hc] at hz
    exact congrArg Subtype.val (show (⟨x, hxL⟩ : L) = 1 from hz)
  obtain ⟨P0, hP0⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) hL.2.1
  let e0 := subgroupOfEquivOfLe hL.1
  let P := P0.mapSurjective (f := e0.toMonoidHom) e0.surjective
  have hP : (P : Subgroup L).map L.subtype = (S : Subgroup H).map H.subtype ⊓ L := by
    change ((P0 : Subgroup (L.subgroupOf H)).map e0.toMonoidHom).map L.subtype = _
    rw [map_map, show L.subtype.comp e0.toMonoidHom =
      H.subtype.comp (L.subgroupOf H).subtype from rfl,
      ← map_map, hP0, subgroupOf_map_subtype,
      Subgroup.map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hL.1]
  have hQ : (omegaOneAmbient (P : Subgroup L)).map L.subtype = componentOmega H L S := by
    rw [map_omegaOneAmbient_injective L.subtype L.subtype_injective, hP]
    rfl
  have hi := SylowCenterAction.Facts.map _
    (OmegaNormalizerModels.of_bender_model hm P) L.subtype L.subtype_injective
  rw [hQ, L.range_subtype] at hi
  exact ⟨hd, hi⟩

/-- Apply the Bender component contradiction with all intrinsic model geometry
proved. Original-z innerness, actual Sylow placement and source balance remain
exactly the earlier-source hypotheses. -/
theorem LocalControlWitness.false_of_bender_model_component
    (w : LocalControlWitness T M) {C : GroupClass} (hG : IsSimpleQTKE C G)
    (hTM : (T : Subgroup G) ≤ M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥) (L : Subgroup G) (hL : IsComponentIn L H)
    (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    (hbalance : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      ∃ K : Subgroup G, IsComponentIn K (centralizer ({v} : Set G)) ∧ L ≤ K)
    (hmodel : ClassificationModels.IsBenderModel L)
    (hzin : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨hd, hs, hc, ho, ht⟩ := bender_component_omega_inputs H L S hL hmodel
  exact w.false_of_bender_omega_component hG hTM H S hUS hST hcore L hL hmax hbalance
    hd hmodel hzin hs hc ho ht
end CFSG.Quasithin.Chapter2.BenderFusion
