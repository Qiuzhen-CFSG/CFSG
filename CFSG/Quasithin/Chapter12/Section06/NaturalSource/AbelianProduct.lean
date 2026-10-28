module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.IntersectingConjugates
public import CFSG.Quasithin.Chapter12.Section06.Terminal.AbelianPointSpan
public import Theory.SpecificGroups.SymmetricFiveThreeLocal

/-!
# Excluding the actual symmetric-product quotient in12.6

For any original H in Hz and any isomorphism H/O2(H) with S5 times S3,
the original E9 Sylow image of L1 puts the normal cubic factor in the
image of L1T. That same image contains an ambient Sylow two-subgroup.
The intrinsic product calculation puts its two-core in A5 times the
identity and bounds its order by four. The image of the original
R1=O2(L1T) lies in this very core, with the literal quotient map retained.

The preceding abelianness and fusion results now supply every hypothesis
of the terminal critical-pair argument. It applies for arbitrary H in Hz,
using the full point-centralizer span to separate critical point lines.
The same actor b, original U_H/V1 section, D_H and A1 give the incompatible
displacement bounds. No index-five, R1-image equality, module decomposition
or separate cubic-placement premise is required by the exclusion.

This closes the product alternative, retaining the earlier fixed-space,
point-invariance, TI, intersection bound and nonsingular-centralizer inputs.
The source local-alternative recognition, SL3(4) and wreath branches, weak
closure and universal NaturalReduction remain separate obligations.
Existing SymmetricProductConclusion interfaces and their full statements
are unchanged.

Source: Aschbacher--Smith12.6.31(3)--34, printed pp.835--838, and F.9.13--17.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Terminal
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (e : (H ⧸ pCore 2 H) ≃* Product)

include hz hTz hH in
private theorem product_image_nine_dvd (B : Subgroup G)
    (hB : (D.fullSetup hZ T z).L₁ ≤ B) :
    9 ∣ Nat.card ((B.subgroupOf H).map (productMap (D := (D.fullSetup hZ T z).f9 H) e)) := by
  let E := D.fullSetup hZ T z
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  let A := (P : Subgroup E.L₁).map E.L₁.subtype
  have hc := (S.original_point_sylow_star D hZ z hz hTz hH P).2.1
  have hAB : A ≤ B := (map_subtype_le _).trans hB
  have hm := map_mono (f := productMap (D := E.f9 H) e)
    (comap_mono (f := H.subtype) hAB)
  have hd := card_dvd_of_le hm
  change Nat.card ((A.subgroupOf H).map
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)))) ∣ _ at hd
  rw [←map_map,card_map_of_injective e.injective] at hd
  exact hc ▸ hd

include hz hTz hH in
/-- The original E9 Sylow image forces the cubic factor into the literal
L1T image, for every marking of the full product quotient. -/
theorem SourceHypothesis.original_product_cubic_placement :
    cubicFactor ≤ (((D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)).subgroupOf H).map
      (productMap (D := (D.fullSetup hZ T z).f9 H) e) := by
  have hc := SymmetricFiveThreeLocal.cubic_le_of_nine_dvd _
    (product_image_nine_dvd S D hZ z hz hTz hH e
      ((D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)) le_sup_left)
  rintro _ ⟨a,ha,rfl⟩
  exact hc ⟨rfl,ha⟩

include hz hTz hH in
/-- The original edge core maps into A5 times the identity and has order
at most four. No index-five or marked-core hypothesis is required. -/
theorem SourceHypothesis.original_product_edge_core_bounds :
    (((D.fullSetup hZ T z).R₁).subgroupOf H).map
      (productMap (D := (D.fullSetup hZ T z).f9 H) e) ≤ quinticComponent ∧
    Nat.card ((((D.fullSetup hZ T z).R₁).subgroupOf H).map
      (productMap (D := (D.fullSetup hZ T z).f9 H) e)) ≤ 4 := by
  let E := D.fullSetup hZ T z
  let f : H →* Product := productMap (D := E.f9 H) e
  let B := E.L₁ ⊔ (T : Subgroup G)
  let J := (B.subgroupOf H).map f
  have hBH : B ≤ H := sup_le (fun x hx => hH.1.2 (Or.inl hx))
    (fun x hx => hH.1.2 (Or.inr hx))
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hBH
  let P := (T.subtype hTH).mapSurjective
    (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 H)))
  have hPJ : (P : Subgroup Product) ≤ J :=
    map_mono (show (T.subtype hTH : Subgroup H) ≤ B.subgroupOf H from
      fun _ hx => mem_sup_right hx)
  have h9 : 9 ∣ Nat.card J := product_image_nine_dvd S D hZ z hz hTz hH e B le_sup_left
  have hcore := SymmetricFiveThreeLocal.core_le_quintic J h9 P hPJ
  have hcard := SymmetricFiveThreeLocal.core_card_le_four J h9 P hPJ
  have hR : E.R₁.subgroupOf H = (B.subgroupOf H).pCoreIn 2 := by
    apply map_injective H.subtype_injective
    change ((B.pCoreIn 2).subgroupOf H).map H.subtype = _
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBH),
      Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_subgroupOf_map hBH]
  have hm := Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le f (B.subgroupOf H)
  rw [←hR] at hm
  refine ⟨?_,(card_le_of_le hm).trans hcard⟩
  rw [quinticComponent_eq_product]
  exact hm.trans hcore

include hz hTz hH in
/-- The entire marked product branch is impossible for the source's actual
H in Hz, including proper subgroups of the full point centralizer. The
same original section and critical actor supply the two displacement bounds. -/
theorem SourceHypothesis.original_symmetric_product_impossible
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hproduct : Nonempty ((H ⧸ pCore 2 H) ≃* Product)) : False := by
  let E := D.fullSetup hZ T z
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  obtain ⟨e⟩ := hproduct
  have hV := (S.original_abelian_point_geometry D hZ z hz hTV hTz hbound hH hTI hns).2.2.1
  have hR := S.original_product_edge_core_bounds D hZ z hz hTz hH e
  exact marked_edge_contradiction_of_point_span h hV
    (S.original_full_point_span_abelian D hZ z hz hTV hTz hbound hTI hns)
    (S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound)
    (S.original_intersecting_conjugates_commute D hZ z hz hTV hTz hbound hTI hns) e
    (S.original_product_cubic_placement D hZ z hz hTz hH e) hR.2 hR.1
end CFSG.Quasithin.Chapter12.Section06
