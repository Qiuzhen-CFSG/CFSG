module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.ThompsonComponents
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.MovingSetup
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.ClosureControl
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.Displacement
public import Theory.GroupTheory.Fitting.OutsideComponent
/-!
# C.2.4(2) for an ambient group of characteristic two

For the original radical Q and control group M, a component moved by Q
and already contained in M lies in the normal closure of Q there, giving
the full Sylow intersection. For an outside component, the actual normal
module Ω₁Z(O₂(G)) and source B.1.5(4) make J(Q) fix the component. Thompson
heredity then puts the normalizer of N_Q(L) inside M. The radical-stabilizer
and commuting-conjugates argument produces a displaced two-element outside
N_Q(L), while the original normal-closure Sylow condition forces it inside.

The ambient formulation retains the original inclusions and quotient maps.
The final application joins this dichotomy to the Fitting-preimage extraction
used in 13.3.12; it assumes neither a chosen component nor its normalization.

Source: Aschbacher–Smith C.2.4(2), p.144 and 13.3.12, p.889; Aschbacher,
*Some results on pushing up in finite groups*, Math. Z. 177 (1981), 10.3,
p.78. We explicitly retain characteristic two for the ambient group, as in
Aschbacher's Section 10 and the original 13.3.12 local application. The full
C.2.4 statement with this assumption only on L is not asserted here.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

theorem sylow_intersection_or_normalizes_of_characteristicTwo
    {κ : GroupClass} (hG : IsSQTK κ G) (Q M L : Subgroup G)
    (hq : IsPRadical 2 Q) (hcontrol : Q.characteristicNormalizerClosure ≤ M)
    (hs : IsSylowInNormalClosure Q M) (hL : L.IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    (∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = Q ⊓ L) ∨
      Q ≤ normalizer (L : Set G) := by
  classical
  by_cases hm : Q ≤ normalizer (L : Set G)
  · exact Or.inr hm
  left
  by_cases hLM : L ≤ M
  · exact moved_component_inside_control_sylow hs hL hLM hm
  by_contra hn
  let : (normalizer (L : Set G)).Normal := component_normalizer_normal hG hL
  have hJ := thompson_le_component_normalizer_of_characteristicTwo Q M L
    hq hc hcontrol hLM hL
  have hNM := stabilizer_normalizer_control hq hcontrol hJ
  obtain ⟨y,s,hy,hsQ,hp,hwN,hwL,hwout⟩ := moving_component_displacement hq hL hm hn
  exact hwout (displacement_mem_radical_stabilizer hs y s (hNM hy.2) hsQ hp hwL hwN)
/-- The original ambient subgroup formulation, retaining both inclusion maps. -/
theorem sylow_intersection_or_normalizes_in_of_characteristicTwo
    {κ : GroupClass} (H Q M L : Subgroup G) (hG : IsSQTK κ H)
    (hQH : Q ≤ H) (hLH : L ≤ H)
    (hq : IsPRadical 2 (Q.subgroupOf H))
    (hcontrol : (Q.subgroupOf H).characteristicNormalizerClosure ≤ M.subgroupOf H)
    (hs : IsSylowInNormalClosure (Q.subgroupOf H) (M.subgroupOf H))
    (hL : (L.subgroupOf H).IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    (∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = Q ⊓ L) ∨
      Q ≤ normalizer (L : Set G) := by
  let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let : IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  rcases sylow_intersection_or_normalizes_of_characteristicTwo hG
    (Q.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H) hq hcontrol hs hL hc with ht | hn
  · obtain ⟨T,hT⟩ := ht
    left
    refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
    change ((T : Subgroup (L.subgroupOf H)).map e.toMonoidHom).map L.subtype = _
    have he := congrArg (map H.subtype) hT
    rw [map_map] at he ⊢
    have hecomp : L.subtype.comp e.toMonoidHom = H.subtype.comp (L.subgroupOf H).subtype := by
      ext x; rfl
    rw [hecomp,he]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · rintro ⟨hxQ,hxL⟩
      exact ⟨⟨x,hQH hxQ⟩,⟨hxQ,hxL⟩,rfl⟩
  · right
    rw [← subgroupOf_normalizer_eq hLH] at hn
    intro q hq
    exact hn (show (⟨q,hQH hq⟩ : H) ∈ Q.subgroupOf H from hq)

/-- C.2.6 and the actual Fitting-preimage escape supply an outside component;
C.2.4 then retains exactly the full-Sylow or normalized alternatives. -/
theorem exists_outside_component_sylow_or_normalized
    {κ : GroupClass} (hG : IsSQTK κ G) (Q M : Subgroup G)
    (hq : IsPRadical 2 Q) (hcontrol : Q.characteristicNormalizerClosure ≤ M)
    (hs : IsSylowInNormalClosure Q M)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hf : twoFittingCore G ≤ M)
    (hg : ¬ (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ M) :
    ∃ L : Subgroup G, L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧
      generalizedFitting L = pCore 2 L ∧ ¬ L ≤ M ∧
      ((∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = Q ⊓ L) ∨
        Q ≤ normalizer (L : Set G)) := by
  obtain ⟨L,hL,hqL,hfL,hout⟩ := exists_characteristicTwo_cComponent_outside M hc hf hg
  let := hqL
  exact ⟨L,hL,hqL,hfL,hout,
    sylow_intersection_or_normalizes_of_characteristicTwo hG Q M L hq hcontrol hs hL hc⟩
end CFSG.Quasithin.ChapterC.Section02Source
