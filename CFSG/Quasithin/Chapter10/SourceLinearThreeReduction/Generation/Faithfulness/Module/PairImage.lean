module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuotientFixation
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
public import Theory.GroupAction.InvariantPairImage

/-!
# The product image on the original two moved quotients

The original nonnormal pair generates the full module and hence its literal
central quotient. The section kernel normalizes each component, so its action
restricts to each moved-factor image. The joint restriction has the same
kernel as the whole action: its image order divides the product of the two
restriction-image orders, with no disjointness assumption. Consequently two
bounds by powers of the component-quotient order give the sum of the exponents.

The original orbit-action commutation descends to these exact restrictions.
Thus bounds for their actual commutants feed the literal Hall-kernel fixation
criterion. Those bounds must still be proved from the source FF rows; no
irreducibility or model marking of an arbitrary full module is assumed here.
Source: Aschbacher--Smith 10.1.3 and the proof of 10.2.3(2), printed
pp.742 and 745 (combined manuscript of 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE.Section06.FixedPointBounds.ParabolicCartan

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal image of a moved factor in the original full central quotient. -/
def sourceMovedQuotient (K : Subgroup G) : Subgroup D.fullCentralQuotient :=
  ((⁅D.fullModule,K⁆).subgroupOf D.fullModule).map (QuotientGroup.mk' D.fullCentralizer)

/-- The moved image uses the original full-module central quotient map. -/
theorem sourceMovedQuotient_eq (K : Subgroup G) :
    sourceMovedQuotient D K =
      ((⁅D.fullModule,K⁆).subgroupOf D.fullModule).map
        (QuotientGroup.mk' D.fullCentralizer) := by rfl

/-- The original nonnormal pair generates the full quotient as well. -/
theorem source_nonnormal_moved_quotient_pair
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      sourceMovedQuotient D L ⊔ sourceMovedQuotient D (L.map (MulAut.conj t).toMonoidHom) = ⊤ := by
  obtain ⟨t,ht,htn,_,he,_⟩ := source_nonnormal_fullModule_pair D hn
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hv : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule (hTM ht))
  rw [map_commutator,hv] at he
  have hW : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_sup_left.trans he.ge
  have hU : ⁅D.fullModule,L.map (MulAut.conj t).toMonoidHom⁆ ≤ D.fullModule := le_sup_right.trans he.ge
  refine ⟨t,ht,htn,?_⟩
  change Subgroup.map _ _ ⊔ Subgroup.map _ _ = _
  rw [← Subgroup.map_sup,← subgroupOf_sup hW hU,←he,subgroupOf_self,
    ← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]

/-- A kernel actor preserves each moved-factor image whenever it normalizes
 the original component. The calculation uses the literal quotient action. -/
theorem source_moved_quotient_invariant
    (B K : Subgroup G) (hBK : B ≤ normalizer (K : Set G))
    (b : B.subgroupOf D.maximalLocal) :
    (sourceMovedQuotient D K).map
      (sourceFullModuleQuotientAction D b.val).toMonoidHom = sourceMovedQuotient D K := by
  let W := ⁅D.fullModule,K⁆
  have hn : (b.val : G) ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hv : D.fullModule.map (MulAut.conj (b.val : G)).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule b.val.property)
    have hk : K.map (MulAut.conj (b.val : G)).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp (hBK b.property)
    change ⁅D.fullModule,K⁆.map (MulAut.conj (b.val : G)).toMonoidHom = ⁅D.fullModule,K⁆
    rw [map_commutator,hv,hk]
  apply eq_of_le_of_card_ge
  · rintro y ⟨x,⟨w,hw,rfl⟩,rfl⟩
    change sourceFullModuleQuotientAction D b.val (QuotientGroup.mk' D.fullCentralizer w) ∈
      sourceMovedQuotient D K
    rw [sourceFullModuleQuotientAction_apply]
    exact mem_map_of_mem (QuotientGroup.mk' D.fullCentralizer)
      ((mem_normalizer_iff.mp hn (w : G)).mp hw)
  · rw [card_map_of_injective (sourceFullModuleQuotientAction D b.val).injective]

/-- Restriction of the original quotient action to the image of a moved factor. -/
def sourceMovedQuotientAction
    (B K : Subgroup G) (hBK : B ≤ normalizer (K : Set G)) :
    B.subgroupOf D.maximalLocal →* MulAut (sourceMovedQuotient D K) :=
  invariantSubgroupAction
    ((sourceFullModuleQuotientAction D).comp (B.subgroupOf D.maximalLocal).subtype)
    (sourceMovedQuotient D K) (source_moved_quotient_invariant D B K hBK)

/-- The moved-factor restriction retains the original quotient coordinates. -/
theorem sourceMovedQuotientAction_apply
    (B K : Subgroup G) (hBK : B ≤ normalizer (K : Set G))
    (b : B.subgroupOf D.maximalLocal) (v : sourceMovedQuotient D K) :
    (sourceMovedQuotientAction D B K hBK b v : D.fullCentralQuotient) =
      sourceFullModuleQuotientAction D b.val v :=
  invariantSubgroupAction_apply _ _ _ b v

include D in
/-- The literal section kernel normalizes both original components, so no
 factor permutation is silently discarded in the product restriction. -/
theorem source_sectionKernel_normalizes_pair
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    sectionCentralizer (localOrbit T L) ≤ normalizer (L : Set G) ∧
    sectionCentralizer (localOrbit T L) ≤
      normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let C := sectionCentralizer (localOrbit T L)
  have hC : C ≤ normalizer (L : Set G) :=
    (source_orbit_sectionCentralizer_le_component D).trans
      ((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).1
  refine ⟨hC,?_⟩
  have hCM : C ≤ D.maximalLocal := ((le_sectionCentralizer_iff C _).mp le_rfl).1
  have hMC : D.maximalLocal ≤ normalizer (C : Set G) := by
    have hh := sectionCentralizerIn_normalized (M := D.maximalLocal)
      (X := localOrbit T L) le_rfl
    change D.maximalLocal ≤ normalizer ((D.maximalLocal ⊓ C : Subgroup G) : Set G) at hh
    rwa [inf_eq_right.mpr hCM] at hh
  have hCt : C.map (MulAut.conj t).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (hMC (le_normalizer_componentOrbit L T ht))
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hC
  rwa [hCt,map_normalizer_eq_of_bijective L (MulAut.conj t).bijective] at hh

/-- The whole quotient image has the prime support of both restriction
 images. Exponents add; a bound for a single factor is never used for the product. -/
theorem source_quotient_image_dvd_of_moved_pair
    (B : Subgroup G) (t : G)
    (hBL : B ≤ normalizer (L : Set G))
    (hBt : B ≤ normalizer (L.map (MulAut.conj t).toMonoidHom : Set G))
    (hpair : sourceMovedQuotient D L ⊔
      sourceMovedQuotient D (L.map (MulAut.conj t).toMonoidHom) = ⊤)
    (n m : ℕ)
    (hfirst : Nat.card (sourceMovedQuotientAction D B L hBL).range ∣
      Nat.card (L ⧸ pCore 2 L) ^ n)
    (hsecond : Nat.card (sourceMovedQuotientAction D B
      (L.map (MulAut.conj t).toMonoidHom) hBt).range ∣
      Nat.card (L ⧸ pCore 2 L) ^ m) :
    Nat.card ((B.subgroupOf D.maximalLocal).map (sourceFullModuleQuotientAction D)) ∣
      Nat.card (L ⧸ pCore 2 L) ^ (n+m) := by
  let f := (sourceFullModuleQuotientAction D).comp (B.subgroupOf D.maximalLocal).subtype
  have hd := action_image_card_dvd_product f
    (sourceMovedQuotient D L) (sourceMovedQuotient D (L.map (MulAut.conj t).toMonoidHom))
    (source_moved_quotient_invariant D B L hBL)
    (source_moved_quotient_invariant D B _ hBt) hpair
  have hf : f.range = (B.subgroupOf D.maximalLocal).map (sourceFullModuleQuotientAction D) := by
    rw [MonoidHom.range_comp,range_subtype]
  rw [hf] at hd
  apply hd.trans
  change Nat.card (sourceMovedQuotientAction D B L hBL).range *
    Nat.card (sourceMovedQuotientAction D B (L.map (MulAut.conj t).toMonoidHom) hBt).range ∣ _
  rw [pow_add]
  exact Nat.mul_dvd_mul hfirst hsecond

/-- The two actual moved-factor image bounds suffice for fixation of an odd
 subgroup of the literal section kernel. -/
theorem source_odd_sectionKernel_fixes_of_moved_images
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hodd : Odd (Nat.card B))
    (hB : B ≤ sectionCentralizer (localOrbit T L))
    (t : G) (ht : t ∈ (T : Subgroup G))
    (hpair : sourceMovedQuotient D L ⊔
      sourceMovedQuotient D (L.map (MulAut.conj t).toMonoidHom) = ⊤)
    (n m : ℕ)
    (hfirst : Nat.card (sourceMovedQuotientAction D B L
      (hB.trans (source_sectionKernel_normalizes_pair D t ht).1)).range ∣
        Nat.card (L ⧸ pCore 2 L) ^ n)
    (hsecond : Nat.card (sourceMovedQuotientAction D B
      (L.map (MulAut.conj t).toMonoidHom)
      (hB.trans (source_sectionKernel_normalizes_pair D t ht).2)).range ∣
        Nat.card (L ⧸ pCore 2 L) ^ m) :
    B ≤ centralizer (D.fullModule : Set G) := by
  exact source_odd_sectionKernel_fixes_of_quotient_image_dvd D hn B hodd hB (n+m)
    (source_quotient_image_dvd_of_moved_pair D B t _ _ hpair n m hfirst hsecond)

/-- The original section-kernel commutation descends to the actual moved
 quotient, where the FF row's endomorphism bound is to be applied. -/
theorem source_moved_quotient_image_commutes
    (B K : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hK : K ≤ localOrbit T L) (hBK : B ≤ normalizer (K : Set G)) :
    (sourceMovedQuotientAction D B K hBK).range ≤ centralizer
      ((sourceMovedQuotientAction D K K K.le_normalizer).range :
        Set (MulAut (sourceMovedQuotient D K))) := by
  rintro a ⟨b,rfl⟩ c ⟨k,rfl⟩
  have hb : b.val ∈ (sectionCentralizer (localOrbit T L)).subgroupOf D.maximalLocal :=
    hB b.property
  have hk : k.val ∈ (localOrbit T L).subgroupOf D.maximalLocal := hK k.property
  have hc := source_sectionKernel_quotient_action_commutes D
    (mem_map_of_mem (sourceFullModuleQuotientAction D) hb)
    (sourceFullModuleQuotientAction D k.val)
    (mem_map_of_mem (sourceFullModuleQuotientAction D) hk)
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change ((sourceMovedQuotientAction D K K K.le_normalizer k)
      ((sourceMovedQuotientAction D B K hBK b) v) : D.fullCentralQuotient) =
    ((sourceMovedQuotientAction D B K hBK b)
      ((sourceMovedQuotientAction D K K K.le_normalizer k) v) : D.fullCentralQuotient)
  simp only [sourceMovedQuotientAction_apply]
  exact congrArg (fun a : MulAut D.fullCentralQuotient => a v) hc

/-- A bound for the actual factor commutant bounds its restriction image. -/
theorem source_moved_quotient_image_card_dvd
    (B K : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hK : K ≤ localOrbit T L) (hBK : B ≤ normalizer (K : Set G))
    (n : ℕ) (hc : Nat.card (centralizer
      ((sourceMovedQuotientAction D K K K.le_normalizer).range :
        Set (MulAut (sourceMovedQuotient D K)))) ∣ Nat.card (L ⧸ pCore 2 L) ^ n) :
    Nat.card (sourceMovedQuotientAction D B K hBK).range ∣
      Nat.card (L ⧸ pCore 2 L) ^ n :=
  (card_dvd_of_le (source_moved_quotient_image_commutes D B K hB hK hBK)).trans hc

/-- Literal Hall-kernel application of the product-image calculation. The
 two actual row commutants are the only remaining module premises here. -/
theorem source_hall_kernel_fixes_of_moved_commutants
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H)))
    (t : G) (ht : t ∈ (T : Subgroup G))
    (hpair : sourceMovedQuotient D L ⊔
      sourceMovedQuotient D (L.map (MulAut.conj t).toMonoidHom) = ⊤)
    (n m : ℕ)
    (hfirst : Nat.card (centralizer
      ((sourceMovedQuotientAction D L L L.le_normalizer).range :
        Set (MulAut (sourceMovedQuotient D L)))) ∣ Nat.card (L ⧸ pCore 2 L) ^ n)
    (hsecond : Nat.card (centralizer
      ((sourceMovedQuotientAction D (L.map (MulAut.conj t).toMonoidHom)
        (L.map (MulAut.conj t).toMonoidHom) (L.map (MulAut.conj t).toMonoidHom).le_normalizer).range :
        Set (MulAut (sourceMovedQuotient D (L.map (MulAut.conj t).toMonoidHom))))) ∣
      Nat.card (L ⧸ pCore 2 L) ^ m) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  let B := Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L)
  have hB : B ≤ sectionCentralizer (localOrbit T L) := inf_le_right
  have hnorm := source_sectionKernel_normalizes_pair D t ht
  apply source_hall_kernel_fixes_of_quotient_image_dvd D hn Y hYM hY (n+m)
  apply source_quotient_image_dvd_of_moved_pair D B t
    (hB.trans hnorm.1) (hB.trans hnorm.2) hpair n m
  · exact source_moved_quotient_image_card_dvd D B L hB (le_componentOrbit L T) _ n hfirst
  · apply source_moved_quotient_image_card_dvd D B _ hB _ _ m hsecond
    exact le_iSup_of_le (⟨t,ht⟩ : T) le_rfl

end CFSG.Quasithin.Chapter10
