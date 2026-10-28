module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeQuotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeModelSieve
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.RepresentativeEnvelopeSource
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The source representative centralizer lies in the plane normalizer

Balance gives a normal ordinary component containing the selected central
four-cover. If the plane is central in that component it lies in the ambient
two-core. Otherwise its surviving quotient involution centralizes a full
Sylow subgroup, while its fixed group contains the rank-two component of
order divisible by 20160. The full known-simple model sieve excludes this.
The two-core bound then identifies it with the plane and gives the literal
centralizer inclusion required by the original reduction.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
open ChapterA.Section02
universe u
variable {H : Type u} [Group H] [Finite H]

private theorem quasisimple_quotient_theoremC (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (K : Subgroup H) [IsQuasisimple K] : IsTheoremCModel (K ⧸ center K) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsQuasisimple (K ⧸ center K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (⊤ : Subgroup (K ⧸ center K)) :=
    IsQuasisimple.of_mulEquiv topEquiv.symm
  have hsem : IsSemisimple (K ⧸ center K) := by
    apply top_unique
    exact le_sSup (show IsComponent (K ⧸ center K) ⊤ from ⟨.top, inferInstance⟩)
  have hK := hH.subgroup K
  have hsq := (theoremA_knownSimple (G := K)).stronglyQuasithin_section
    hK.stronglyQuasithin hK.isKGroup
    (IsSectionOf.of_surjective (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)) hsem
  exact theoremC_knownSimple (G := K ⧸ center K) inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hsq (hK.isKGroup.quotient _)

/-- The actual central four-plane is forced into the representative two-core. -/
theorem central_plane_le_twoCore (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (B K V : Subgroup H) [IsQuasisimple B] [IsQuasisimple K] [K.Normal]
    [IsKleinFour V] (hBK : B ≤ K) (hZ : (center B).map B.subtype = V)
    (hCB : centralizer (V : Set H) ≤ normalizer (B : Set H))
    (T : Sylow 2 H) (hTB : (T : Subgroup H) ≤ normalizer (B : Set H))
    (v : H) (hv : v ∈ V) (hv1 : v ≠ 1) (hvZ : v ∈ center H)
    (hrank : 2 ≤ primeRank 3 B) (hcard : Nat.card (B ⧸ center B) = 20160) :
    V ≤ pCore 2 H := by
  have hVB : V ≤ B := hZ ▸ map_subtype_le _
  have hVK : V ≤ K := hVB.trans hBK
  by_cases hV : V ≤ (center K).map K.subtype
  · have hp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by
      rw [IsKleinFour.card_four]; decide)
    have hc : K ≤ centralizer (V : Set H) := by
      intro k hk z hz
      obtain ⟨a,ha,rfl⟩ := hV hz
      exact (congrArg Subtype.val (mem_center_iff.mp ha (⟨k,hk⟩ : K))).symm
    exact (le_pCoreIn_of_normalizes hp hVK (hc.trans (Subgroup.centralizer_le_normalizer _))).trans
      (pCoreIn_le_of_subnormal 2 (inferInstance : K.Normal).isSubnormal)
  · obtain ⟨t,ht,P,hPC,D,hD,hcardD,hrD⟩ :=
      RepresentativeQuotient.exists_fixed_component B K V hBK hZ hCB T hTB v hv hv1 hvZ hrank hcard hV
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let data : RepresentativeModelSieve.Input (K ⧸ center K) := {
      simple := inferInstance
      nonabelian := Group.IsPerfect.not_isMulCommutative _
      involution := t
      order := ht
      sylow := P
      sylow_le := hPC
      component := D
      isComponent := hD
      card_dvd := hcardD
      rank := hrD }
    exact (data.not_theoremCModel (quasisimple_quotient_theoremC hH K)).elim

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal centralizer bound, with the original full Sylow seed retained. -/
theorem LocalResult.representative_centralizer_le_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L) (r : LocalResult d I L)
    (v : G) (hv : v ∈ r.cover.borel.W₁) (hv1 : v ≠ 1) (hv2 : orderOf v = 2)
    (hS : IsSylowIn 2 d.S (centralizer ({v} : Set G))) :
    centralizer ({v} : Set G) ≤ I := by
  let H := centralizer ({v} : Set G)
  let V₀ := r.cover.borel.W₁
  obtain ⟨K,hK,hKn,hLK⟩ := r.representative_envelope_knownSimple hG s h v hv hv2
  have hLH : L ≤ H := hLK.trans (map_subtype_le _)
  have hVL : V₀ ≤ L := by
    change r.cover.borel.W₁ ≤ L
    rw [← r.cover.center_plane]
    exact map_subtype_le _
  have hVH : V₀ ≤ H := hVL.trans hLH
  let B := L.subgroupOf H
  let V := V₀.subgroupOf H
  let eB : B ≃* L := subgroupOfEquivOfLe hLH
  let eV : V ≃* V₀ := subgroupOfEquivOfLe hVH
  let : K.Normal := hKn
  let : IsQuasisimple K := hK.2
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB.symm
  obtain ⟨i,hi⟩ := r.plane
  let : IsElementaryAbelian 2 V₀ := d.action.elementary_of_le
    (by simpa only [V₀,hi] using d.action.plane_le i)
  let : Nontrivial V₀ := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card r.cover.borel.W₁
    rw [hi,d.action.card_plane]; decide)
  let : IsKleinFour V₀ := ⟨by simpa only [V₀,hi] using d.action.card_plane i,
    IsElementaryAbelian.exponent_eq_prime⟩
  let : IsKleinFour V := ⟨(Nat.card_congr eV.toEquiv).trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv eV).trans IsKleinFour.exponent_two⟩
  have hBK : B ≤ K := by
    intro x hx
    obtain ⟨k,hk,he⟩ := hLK hx
    exact (Subtype.ext he : k = x) ▸ hk
  have hZ : (center B).map B.subtype = V := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      change (b : G) ∈ r.cover.borel.W₁
      rw [← r.cover.center_plane]
      exact ⟨eB b, (MulEquivClass.apply_mem_center_iff eB).mpr hb, rfl⟩
    · intro hx
      change (x : G) ∈ r.cover.borel.W₁ at hx
      obtain ⟨z,hz,he⟩ := mem_map.mp (r.cover.center_plane.symm ▸ hx)
      refine ⟨eB.symm z,(MulEquivClass.apply_mem_center_iff eB.symm).mpr hz,?_⟩
      exact Subtype.ext he
  have hHI : centralizer (V : Set H) ≤ I.subgroupOf H := by
    intro x hx
    rw [normalizer_eq_knownSimple hG s h r]
    apply Subgroup.centralizer_le_normalizer
    intro w hw
    exact congrArg Subtype.val (hx (⟨w,hVH hw⟩ : H) hw)
  have hCB : centralizer (V : Set H) ≤ normalizer (B : Set H) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp ((h.normalizes_component s.earlier) (hHI hx)) y
  obtain ⟨T,hT⟩ := hS
  have hSI : d.S ≤ I := le_sup_right.trans h.outside.1.2
  have hTB : (T : Subgroup H) ≤ normalizer (B : Set H) := by
    intro x hx
    have hxS : (x : G) ∈ d.S := hT ▸ mem_map_of_mem H.subtype hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp ((h.normalizes_component s.earlier) (hSI hxS)) y
  let vH : H := ⟨v,mem_centralizer_singleton_iff.mpr rfl⟩
  have hvZ : vH ∈ center H := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have hrank : 2 ≤ primeRank 3 B := by rw [primeRank_equiv 3 eB,h.component_rank]
  have hqcard : Nat.card (B ⧸ center B) = 20160 := by
    let ez := QuotientGroup.congr (center B) (center L) eB (by
      ext x
      constructor
      · rintro ⟨b,hb,rfl⟩
        exact (MulEquivClass.apply_mem_center_iff eB).mpr hb
      · intro hx
        exact ⟨eB.symm x,(MulEquivClass.apply_mem_center_iff eB.symm).mpr hx,eB.apply_symm_apply x⟩)
    rw [Nat.card_congr ez.toEquiv,r.cover.center_core]
    exact A312Specialization.marked_quotient_card L r.marking
  have hcore : V ≤ pCore 2 H := central_plane_le_twoCore
    (hG.involution_centralizer_sqtk hv2) B K V hBK hZ hCB T hTB vH hv
    (fun he => hv1 (congrArg Subtype.val he)) hvZ hrank hqcard
  have hVcore : V₀ ≤ H.pCoreIn 2 := by
    change V₀ ≤ (pCore 2 H).map H.subtype
    simpa only [V,map_subgroupOf_eq_of_le hVH] using map_mono (f := H.subtype) hcore
  exact r.representative_le_of_core_plane hG s h H
    (le_antisymm (r.representative_twoCore_le_plane hG s h H K hK hLK) hVcore)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
