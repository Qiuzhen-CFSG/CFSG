module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.FittingPreimage
public import Theory.GroupTheory.CComponent.FittingNormalizerQuotient
public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity

/-!
# The two-core quotient of a normal containing component

In the original C.2.8 setup, suppose M normalizes L and L/O₂(L) is
quasisimple. C.2.11 puts the Fitting preimage of H inside M. A normal
C-component containing L inherits that containment by Fitting functoriality;
its Fitting preimage therefore normalizes the same embedded L. The
Fitting-normalization criterion makes its two-core quotient quasisimple.

This supplies the containing-component quotient used at the start of
original 4.3.2, without an ordinary/constrained model classification.
Source: Aschbacher--Smith C.2.11 and 4.3.2, printed pp.148,613.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
  {H M L R V : Subgroup G}

/-- A normal containing C-component has quasisimple two-core quotient when
M normalizes the original quasisimple-quotient seed L. -/
theorem normal_containing_component_quotient
    (h : HypothesisC28 κ H M L R V)
    (hMN : M ≤ normalizer (L : Set G)) (hLq : IsQuasisimple (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hLK : L ≤ K.map H.subtype) (hn : K.Normal) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let B := (L.subgroupOf H).subgroupOf K
  have hLH : L ≤ H := h.component_le.trans h.local_le
  have hBK : L.subgroupOf H ≤ K := by
    intro l hl
    obtain ⟨k,hk,he⟩ := hLK hl
    have he' : k = l := Subtype.ext he
    exact he' ▸ hk
  let e : B ≃* L := (subgroupOfEquivOfLe hBK).trans (subgroupOfEquivOfLe hLH)
  have hBq : IsQuasisimple (B ⧸ pCore 2 B) := by
    let := hLq
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr (pCore 2 B) (pCore 2 L) e (pCore_map_iso 2 e)).symm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.subgroupOf le_rfl
  apply quasisimple_quotient_of_fitting_normalizes htop B hBq
  let := hn
  have hF := (twoFittingCore_map_subtype_le_of_normal K).trans h.fitting_preimage_le
  intro x hx
  apply Subgroup.mem_normalizer_iff.mpr
  intro b
  change ((b : H) : G) ∈ L ↔ (((x * b * x⁻¹ : K) : H) : G) ∈ L
  exact (mem_normalizer_iff.mp (hMN (hF (mem_map_of_mem K.subtype hx)))) (b : G)

end CFSG.Quasithin.ChapterC.HypothesisC28
