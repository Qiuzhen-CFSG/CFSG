module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.InnerSource
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.LocalAdjustment
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.LocalResidualFacts
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingMarksSource
public import Theory.GroupTheory.NormalizerInnerAutomorphisms

/-!
# Excluding the inner branch from a residual-normalizing original crossing

The actual local residual has center ⟨zK⟩. Thus a crossing normalizing that
residual fixes zK, so the original central-four action gives zK=z. A Sylow
adjustment centralizes the residual while preserving the outside crossing.
The earlier inner-branch normalizer contradiction now applies. All model,
center-line and adjustment claims are proved here; residual invariance is
the preceding 2.5.6/A.3.18 characteristic-centralizer producer's output.
Source: Aschbacher--Smith 2.5.15, pp.558--559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z x : G}

theorem small_component_inner_marked_false
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (hinner : (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G))
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hZ : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (zK : K) (hzK : orderOf zK = 2)
    (hzS : (zK : G) ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hxR : x ∈ normalizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G)) : False := by
  let R := (GLTwoThreeLocal.residual zK).map K.subtype
  have hzKo : orderOf (zK : G) = 2 := (Subgroup.orderOf_coe zK).trans hzK
  have hcent : centerIn R = zpowers (zK : G) := local_residual_ambient_center K hK zK hzK
  have hxZ : x ∈ normalizer (zpowers (zK : G) : Set G) := by
    rw [← hcent]
    exact normalizes_centerIn (le_rfl : normalizer (R : Set G) ≤ normalizer (R : Set G)) hxR
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ hzKo] at hxZ
  have hxfix : x⁻¹*(zK : G)*x=(zK : G) := by
    have hc := mem_centralizer_singleton_iff.mp hxZ
    calc x⁻¹*(zK : G)*x = x⁻¹*((zK : G)*x) := mul_assoc _ _ _
         _ = x⁻¹*(x*(zK : G)) := by rw [hc]
         _ = (zK : G) := inv_mul_cancel_left _ _
  have hez : (zK : G) = z := ComponentSelection.MathieuSourceSetup.source_fixed_projection
    c hgen t ht htC htZ hZ x hxT hxN hxS zK hzKo hzS hxfix
  obtain ⟨y,hyT,hyS,hyN,hyR⟩ := local_residual_crossing_adjustment c hK zK hzK hzS hxT hxS hxN hxR
  obtain ⟨hRK,hRz,hzR⟩ := local_residual_ambient_facts K hK zK hzK
  rw [hez] at hRz hzR
  exact small_component_inner_crossing_false c hG hempty hgen hb hp hUS hinner
    hRK hRz hzR hyT hyS hyN hyR
omit [Finite G] in
theorem mathieu_source_sylow_inner_cover
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (e : K ≃* Sporadic.Mathieu.M11) :
    (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G) := by
  have hKN := (normal_subgroupOf_iff_le_normalizer c.component_le).mp
    (inferInstance : (K.subgroupOf H).Normal)
  intro s hs
  let n : normalizer (K : Set G) := ⟨s,hKN (map_subtype_le _ hs)⟩
  obtain ⟨k,hk⟩ := Sporadic.Mathieu.automorphism_inner_of_equiv_m11 e (K.normalizerMonoidHom n)
  have hi : K.normalizerMonoidHom n ∈ (MulAut.conj : K →* MulAut K).range := ⟨k,hk.symm⟩
  have hm : n ∈ (MulAut.conj : K →* MulAut K).range.comap K.normalizerMonoidHom := hi
  rw [normalizerMonoidHom_comap_conj_range] at hm
  exact hm

end CFSG.Quasithin.Chapter2.Section05
