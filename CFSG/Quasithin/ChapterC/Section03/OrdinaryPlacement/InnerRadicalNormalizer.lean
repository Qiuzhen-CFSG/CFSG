module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import Theory.GroupTheory.RadicalInnerNormalizer
public import Theory.GroupTheory.PerfectCentralCoverOuter
/-!
# The original radical normalizer in an inner-automorphism component

C.3 gives a normal ordinary component with two-group center. If its
automorphisms are inner, radical saturation splits the original radical
into its component intersection and its component centralizer. Normalizing
the first factor therefore normalizes the original radical, so the genuine
C.2.8 characteristic-normalizer condition puts the result in the original
local subgroup. No full component Sylow or trivial center is assumed.

The Rudvalis application retains the literal component central quotient.
Source: Aschbacher--Smith C.2.2(1), C.3.3 and 4.2.13, pp.144,149,611--612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- An inner-automorphism component has its radical-intersection normalizer in the source local. -/
theorem ordinary_radical_normalizer_le_local_of_inner
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (hi : ∀ a : MulAut K, a ∈ MulAut.innerSubgroup K) :
    normalizer ((R.subgroupOf H).subgroupOf K : Set K) ≤
      (M.subgroupOf H).subgroupOf K := by
  let := h.ordinary_component_normal K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hZ : IsPGroup 2 (center K) := hz.symm ▸ pCore_isPGroup
  have hr : R.subgroupOf H ≤ K ⊔ centralizer (K : Set H) := by
    rw [←MulAut.conjNormal_comap_innerSubgroup K]
    intro x _
    exact hi (MulAut.conjNormal x)
  have hn := radical_intersection_normalizer_le K (R.subgroupOf H) h.isRadical hZ hr
  have hRH := h.radical_le.trans h.local_le
  intro x hx
  have hx' : (x : H) ∈ normalizer ((R.subgroupOf H) ⊓ K : Set H) := by
    have hh := ((R.subgroupOf H).subgroupOf K).le_normalizer_map K.subtype
      (mem_map_of_mem K.subtype hx)
    rwa [subgroupOf_map_subtype] at hh
  have hh := hn ⟨x.property,hx'⟩
  rw [←subgroupOf_normalizer_eq hRH] at hh
  exact h.normalizer_le ⟨x.val.property,hh⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
