module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefFaithfulness

/-!
# The marked faithful partner chief quotient

The faithful action of L/O₂(L) constructed in ChiefFaithfulness retains
its literal chief section. The image of the original V is nontrivial and
elementary abelian. The bound [V,Qc] ≤ V and elementary commutativity give
quadraticity through the section's actual coordinate map. Mapping the
original V-normalizing Sylow T through the same quotient gives the marked
Sylow and its normalizer containment.

Thus all the faithful-chief-action and actor-marking inputs are supplied
on one quotient and one section, before the common-center transvection
exclusion and model recognition. The critical-pair owner still owns those
steps and the final partner-core containment; no classification premise is
introduced by this output predicate.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136).
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Output properties of the actual two-core quotient, retaining the original
quotient map for both the elementary actor and the Sylow marking. -/
@[expose] def PartnerChiefQuotientProperties
    (T : Sylow 2 G) (V L : Subgroup G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W) : Prop :=
  let q := QuotientGroup.mk' (pCore 2 L)
  let A := (V.subgroupOf L).map q
  Function.Injective σ ∧ IsIrreducible σ ∧
  IsElementaryAbelian 2 A ∧ A ≠ ⊥ ∧ BinaryOffender.IsQuadratic σ A ∧
  ∃ S : Sylow 2 (L ⧸ pCore 2 L),
    (S : Subgroup (L ⧸ pCore 2 L)) = ((T : Subgroup G).subgroupOf L).map q ∧
    A ≤ (S : Subgroup (L ⧸ pCore 2 L)) ∧
    (S : Subgroup (L ⧸ pCore 2 L)) ≤ normalizer (A : Set (L ⧸ pCore 2 L)) ∧
    ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
      1 ≤ Module.finrank (ZMod 2) (LinearMap.range (σ (q a) - 1)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (σ (q a) - 1)) ≤ 2 ∧
      BinaryOffender.quadraticRatio σ ≤ 2

/-- The faithful partner chief action, with the literal quotient images of
V and T and all their elementary, quadratic and normalizing properties. -/
theorem source_chosen_partner_faithful_marked_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
        σ.comp (QuotientGroup.mk' (pCore 2 L)) = binarySectionRepresentation B U ∧
        PartnerChiefQuotientProperties T V L σ := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ :=
    source_chosen_partner_faithful_chief_action h hg hMc hZ hquotient hres hs hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,hfaith,hi,he,a,ha,ho,hlo,hhi⟩ := hσ
  refine ⟨σ,he,?_⟩
  let := h.prepared.elementary
  let A := (V.subgroupOf L).map q
  have hTH : (T : Subgroup G) ≤ H := hg.outside.1.1.2
  have hQT : twoCoreIn H ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,pCoreIn,twoCoreIn] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hVT : V ≤ (T : Subgroup G) := (h.prepared.inside_core H hg.outside).trans hQT
  have hVL : V ≤ L := hVT.trans le_sup_right
  let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hAn : A ≠ ⊥ := by
    intro hh
    have hm : q a ∈ A := mem_map_of_mem q ha
    have he1 : q a = 1 := by simpa only [hh,mem_bot] using hm
    rw [he1,orderOf_one] at ho
    omega
  have d : BinaryConjugationSection L (U.val.map L.subtype) (B.val.map L.subtype)
      (σ.comp q) := by
    rw [show σ.comp q = binarySectionRepresentation B U from he]
    exact ambientBinarySection L B U hc.le
  have hcomm : ⁅V,U.val.map L.subtype⁆ ≤ V :=
    ((commutator_mono le_rfl hU).trans
      (source_chosen_partner_core_commutator_le h hg)).trans inf_le_left
  have hc2 : ⁅V,⁅V,U.val.map L.subtype⁆⁆ ≤ B.val.map L.subtype :=
    (commutator_mono le_rfl hcomm).trans
      ((commutator_eq_bot_iff_le_centralizer.mpr V.le_centralizer).le.trans bot_le)
  have hquad : BinaryOffender.IsQuadratic σ A :=
    BinaryConjugationSection.isQuadratic_of_triple_commutator_le L
      (U.val.map L.subtype) (B.val.map L.subtype) V σ q d hc2
  let S : Sylow 2 (L ⧸ pCore 2 L) :=
    (T.subtype (show (T : Subgroup G) ≤ L from le_sup_right)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 L))
  have hAS : A ≤ (S : Subgroup (L ⧸ pCore 2 L)) := map_mono (comap_mono hVT)
  have hnorm : (T : Subgroup G).subgroupOf L ≤ normalizer (V.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq hVL]
    exact comap_mono (h.maximal.1.2.trans h.prepared.normalized)
  have hSA : (S : Subgroup (L ⧸ pCore 2 L)) ≤ normalizer (A : Set (L ⧸ pCore 2 L)) :=
    (map_mono hnorm).trans ((V.subgroupOf L).le_normalizer_map q)
  refine ⟨hfaith,hi,hA,hAn,hquad,S,rfl,hAS,hSA,a,ha,ho,hlo,hhi,?_⟩
  obtain ⟨hE,hr,hq,_⟩ := BinaryOffender.involution_actor_rank_and_fixedCodim σ (q a) ho
  apply (BinaryOffender.quadraticRatio_le_two_iff σ).mpr
  refine ⟨zpowers (q a),hE,hq,?_⟩
  rw [hr,Nat.mul_one,BinaryOffender.fixedCodim_zpowers_eq_displacement_rank]
  exact hhi

end CFSG.Quasithin.Chapter15.Section02
