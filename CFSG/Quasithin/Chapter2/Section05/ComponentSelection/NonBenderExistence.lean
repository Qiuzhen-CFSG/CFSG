module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AllBenderReplacement
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NoComponents
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.SylowLayerNormalizer

/-!
# Existence of an actual non-Bender component

Assume every component of the original source group is Bender. The proved
2.5.3(3) and maximal-pair construction give its literal layer-Sylow
normalizer as a new source group, with the enlarged family of two-normalizers.
Glauberman's proved Sylow-fixer theorem and the odd order theorem discharge
the two-Schreier and component-evenness inputs: that normalizer has no
components. The original component-free contradiction therefore applies.

This proves existence of a non-Bender component in the original H.
The additional source assertion that a component can be chosen with
the correct starred conditions for its join with S remains a separate step.

Source: Aschbacher--Smith 2.5.3(4), printed pp.552--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- All arithmetic and Sylow-fixer inputs to the literal layer-normalizer
component theorem are unconditional for finite groups. -/
theorem not_isComponent_normalizer_layer_sylow
    (P : Sylow 2 (componentLayer G))
    (K : Subgroup (normalizer ((P : Subgroup (componentLayer G)).map
      (componentLayer G).subtype : Set G))) :
    ¬ IsComponent (normalizer ((P : Subgroup (componentLayer G)).map
      (componentLayer G).subtype : Set G)) K := by
  apply not_isComponent_normalizer_layer_sylow_of_twoSchreier
    (ChapterI.SylowAutomorphisms.hasTwoSchreier G) ?_ P K
  intro L hL
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
  by_contra h
  let : Group.IsSolvable (L ⧸ center L) := odd_order_theorem _
    (Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he)))
  exact Group.IsPerfect.not_isSolvable (L ⧸ center L) inferInstance

variable {M H : Subgroup G}

/-- The original normalizer-intersection source group has a non-Bender
component. No component-selection, Schreier, model-action or projection
assumption remains beyond the original QTKE and unique-local hypotheses. -/
theorem exists_non_bender_component_of_normalizer_intersection
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G)) :
    ∃ D : Subgroup H, IsComponent H D ∧ ¬ ClassificationModels.IsBenderModel D := by
  classical
  by_contra! hall
  obtain ⟨P, X, B', hXeq, hX, _hs, _hm, hp', hBX, hXnorm⟩ :=
    exists_all_bender_layer_replacement hG T₀ hM hT₀M hunique hH B hp hBH hHnorm hall
  obtain ⟨K, hK⟩ := exists_component_of_normalizer_intersection hG T₀ hM hT₀M
    hunique hX hempty B' hp' hBX hXnorm
  let N := normalizer ((P : Subgroup (componentLayer H)).map (componentLayer H).subtype : Set H)
  let e : N ≃* X := (N.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hXeq.symm)
  exact not_isComponent_normalizer_layer_sylow P (K.map e.symm.toMonoidHom)
    (hK.map_equiv e.symm)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
