module

public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeRadicalCentered

/-!
# The surviving ordinary Ree component

The original C.2.8 moved module survives the ordinary component's central
quotient. Its literal radical intersection is radical, and the module
remains in its center. Applying the full Ree normalizer calculation kills
the module, contradicting C.2.8. The original chosen orbit is retained in
the preceding rank bound; the C.2.8 module supplies this final contradiction.

Source: Aschbacher--Smith C.3.2--5 and 4.2.12--13, pp.149--150,610--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

/-- The literal C.2.8 module survives the central quotient of an ordinary
component, remains centered in its radical intersection, and is moved by F. -/
theorem no_ordinary_ree_of_normalized_rankOne
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : IsComponent H K)
    {m : ℕ} (hm : 1 ≤ m) (e : (K ⧸ center K) ≃* ReeF4.Model m) : False := by
  have hspan := h.normalized_span_eq hn
  have hFH := h.component_le.trans h.local_le
  have hFK := h.ordinary_component_contains_original K hK
  have hWF : W ≤ F := hspan ▸ h.module_le
  have hWH : W ≤ H := hWF.trans hFH
  have hWK : W.subgroupOf H ≤ K := (subgroupOf_mono H hWF).trans hFK
  let FK := (F.subgroupOf H).subgroupOf K
  let WK := (W.subgroupOf H).subgroupOf K
  let P := (R.subgroupOf H).subgroupOf K
  let i := H.subtype.comp K.subtype
  have hi : Function.Injective i := H.subtype_injective.comp K.subtype_injective
  have hFm : FK.map i = F := by
    rw [←map_map,map_subgroupOf_eq_of_le hFK,map_subgroupOf_eq_of_le hFH]
  have hWm : WK.map i = W := by
    rw [←map_map,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hWH]
  have hWne : WK ≠ ⊥ := by
    intro hb
    exact h.module_nontrivial (by rw [←hWm,hb,Subgroup.map_bot])
  have hcomm : WK = ⁅WK,FK⁆ := by
    apply map_injective hi
    rw [map_commutator,hWm,hFm]
    simpa only [hspan] using h.module_commutator
  have hrad := h.ordinary_radical_intersection_isRadical K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hqP : q.ker ≤ P := by
    rw [hqker,hz]
    exact pCore_le_of_pCore_normalizer_le P hrad.isPGroup hrad.2.le
  have hPn : (normalizer (P.map q : Set _)).pCoreIn 2 = P.map q :=
    map_normalizer_core_of_p_kernel P hrad.isPGroup hrad.2 q hq hqP
  have hWP : WK ≤ P ⊓ centralizer (P : Set K) := by
    intro w hw
    obtain ⟨z,hz,he⟩ := h.module_le_center_radical hw
    have he' : (z : G) = ((w : H) : G) := he
    refine ⟨?_,?_⟩
    · change ((w : H) : G) ∈ R
      rw [←he']
      exact z.property
    · intro p hp
      apply hi
      change ((p : H) : G) * ((w : H) : G) = ((w : H) : G) * ((p : H) : G)
      rw [←he']
      exact congrArg R.subtype (mem_center_iff.mp hz ⟨((p : H) : G),hp⟩)
  have hU : WK.map q ≤ P.map q ⊓ centralizer (P.map q : Set _) :=
    le_inf (map_mono (hWP.trans inf_le_left))
      ((map_mono (hWP.trans inf_le_right)).trans (map_centralizer_le_centralizer_image _ _))
  have hUne : WK.map q ≠ ⊥ := by
    intro hb
    have hc : WK ≤ center K := hqker ▸ (map_eq_bot_iff WK).mp hb
    exact hWne (hcomm.trans (commutator_eq_bot_iff_le_centralizer.mpr
      (fun x hx y _ => mem_center_iff.mp (hc hx) y)))
  have hFN : FK ≤ normalizer (P : Set K) := by
    intro f hf r
    exact h.span_normalizes_radical (hspan.symm ▸ hf) ((r : H) : G)
  let a : FK ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFH)
  let : Group.IsPerfect F := hspan ▸ h.span_perfect
  let : Group.IsPerfect FK := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let r := q.comp FK.subtype
  have hr : r.range = FK.map q := by rw [MonoidHom.range_comp,range_subtype]
  have hk : r.ker ≤ center FK := by
    intro x hx
    have hx' : (x : K) ∈ center K := hqker ▸ (show (x : K) ∈ q.ker from hx)
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx' y))
  let : CommGroup (center FK) := IsMulCommutative.instCommGroup
  let : Group.IsSolvable r.ker :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
  apply no_ree_radical_centered_module hS hexp (π.comp a.toMonoidHom)
    (hπ.comp a.surjective) hm (P.map q) (WK.map q) (hrad.isPGroup.map q) hPn hU hUne r
  · rw [hr]
    exact (map_mono hFN).trans (P.le_normalizer_map q)
  · rw [hr,←map_commutator]
    exact congrArg (map q) hcomm

/-- Both marked rank-one families exclude the ordinary component branch,
using the original C.2.8 centered module in the surviving Ree quotient. -/
theorem no_ordinary_normalized_rankOne
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W U : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (hfix : U ⊓ centralizer (F : Set G) = ⊥) (hr : 12 ≤ primeRank 2 U)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  obtain ⟨_,m,hm,⟨e⟩⟩ := ordinary_ree_of_large_rankOne h hn hUF hne hcomm hfix hr
    hS hexp π hπ K hK
  let a := K.equivMapOfInjective H.subtype H.subtype_injective
  let z := QuotientGroup.congr (center K) (center (K.map H.subtype)) a
    (FixedElementary.map_center a)
  exact no_ordinary_ree_of_normalized_rankOne h hn hS hexp π hπ K hK hm (z.trans e)
end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
