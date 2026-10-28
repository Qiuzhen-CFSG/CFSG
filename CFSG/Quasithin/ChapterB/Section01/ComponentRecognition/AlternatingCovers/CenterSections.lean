module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.Contracts
public import Theory.Representation.BinaryOffender.CubicCenterSections
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The center-faithful B.1.11 construction

For a quasisimple subgroup L with center of order three and [L,A] = L,
where A is a best offender on a faithful binary module, construct the
actual overgroup and faithful irreducible FF central section required by
the alternating-cover branch of B.1.13.

Inside LA, pass to C_V(O₂(LA)). The kernel on L is O₂(L), which is trivial
because it lies in the cubic center. Thus the L-image still has a cubic
center. Choose a center-detecting Irr⁺ section there, use a minimal best
offender and B.1.5(3) to stabilize it, and apply the section FF argument.
The literal quotient intertwiners preserve faithfulness when lifting the
section back through the fixed space and then to the original ambient group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.11
and the first paragraph of the proof of B.1.13 on printed p. 74
(PDF pp. 84–85), combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers
private theorem twoCore_eq_bot_of_cubic_center {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hc : Nat.card (center L) = 3) : pCore 2 L = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hcentral := IsQuasisimple.pCore_le_center (G := L) 2 hx
  have hz3 : (⟨x,hcentral⟩ : center L)^3 = 1 := hc ▸ pow_card_eq_one'
  have hx3 : (⟨x,hx⟩ : pCore 2 L)^3 = 1 := Subtype.ext (congrArg (fun a : center L => (a : L)) hz3)
  have hcop := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
    (by decide : Nat.Coprime 2 3) (⟨x,hx⟩ : pCore 2 L)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hx3)))

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
private theorem faithful_reduced (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hfit : generalizedFitting G = L) (hcore : pCore 2 G = ⊥)
    (hA : IsBestOffender ρ A) (hc : Nat.card (center L) = 3) :
    HasFaithfulIrreducibleFFSection ρ L := by
  let : L.Normal := hfit ▸ (generalizedFitting_normal (G := G))
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  obtain ⟨B, hB, _⟩ := hA.exists_minimal ρ
  let : IsElementaryAbelian 2 B := hB.1.1.2
  have hp : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  have hcomm : ⁅L, B⁆ = L := by
    have hq : IsQuasisimple (generalizedFitting G) := hfit.symm ▸ inferInstance
    simpa only [hfit] using QuasisimpleSections.commutator_fitting_eq hcore hq hB.1.1.1 hp
  have hr : pResidual 2 L = ⊤ := by
    apply (pResidual_eq_top_iff 2 L).mpr
    intro N hN hp
    let := hN
    have hsub : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply top_unique
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have hchief : HasCentralPChiefFactors 2 L :=
    hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup L) (by simp)
      (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  obtain ⟨I, hI, hIfaith⟩ := exists_faithful_isIrrPlus_of_cubic_center ρ L (hfaith.comp L.subtype_injective) hc
  have hBI := source_lemma_B_1_5_3 ρ hfaith hB hr hcomm hchief hI
  let H := L ⊔ B
  have hHI : H ≤ subspaceStabilizer ρ I := sup_le hI.choose hBI
  have hHN : H ≤ normalizer (L : Set G) := le_normalizer_of_normal
  have hdis : Disjoint B (centralizer (L : Set G)) := by
    rw [← hfit]
    exact QuasisimpleSections.disjoint_centralizer_fitting hcore B hp
  exact ⟨H, I, le_sup_left, hI, hHI, hHN,
    centralSection_isFFModule_of_offender ρ L B H hB.1 le_sup_left le_sup_right
      hdis I hI hHI hHN,
    hIfaith⟩


private theorem faithful_generated (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hLA : ⁅L,A⁆ = L) (hgen : L ⊔ A = ⊤) (hA : IsBestOffender ρ A)
    (hc : Nat.card (center L) = 3) : HasFaithfulIrreducibleFFSection ρ L := by
  let U := fixedSpace ρ (pCore 2 G)
  let σ := subspaceImageRepresentation ρ U
  let f := invariantActionHom ρ U (fixedSpace_stable_of_normal ρ (pCore 2 G))
  obtain ⟨hk, _, hcore, hquasi, hfit, _, hbest, _⟩ :=
    irreducibleReduction_generated ρ hfaith L A hLA hgen hA
  have hmap : L.map f = restrictedSubgroup ρ U L := invariantActionHom_map ρ U _ L
  have hfL : Function.Injective (f.subgroupMap L) := by
    apply (injective_iff_map_eq_one _).mpr
    intro l hl
    have hlker : (l : G) ∈ subspaceKernel ρ U L := by
      refine ⟨l.property, ?_⟩
      intro v hv
      have he : f l = 1 := congrArg Subtype.val hl
      exact congrArg Subtype.val (congrArg (fun g => σ g (⟨v,hv⟩ : U)) he)
    rw [irreducibleReduction_component_kernel ρ L hk, twoCore_eq_bot_of_cubic_center hc, Subgroup.map_bot] at hlker
    exact Subtype.ext hlker
  let eL : L ≃* L.map f := MulEquiv.ofBijective (f.subgroupMap L)
    ⟨hfL, f.subgroupMap_surjective L⟩
  have hc' : Nat.card (center (L.map f)) = 3 :=
    (Nat.card_congr (centerCongr eL).toEquiv).symm.trans hc
  let : IsQuasisimple (L.map f) := hmap.symm ▸ hquasi
  obtain ⟨D, I, hLD, hI, hDI, hDN, hFF, hIfaith⟩ :=
    faithful_reduced σ (subspaceImageRepresentation_injective ρ U)
      (L.map f) (restrictedSubgroup ρ U A) (hfit.trans hmap.symm) hcore hbest hc'
  obtain ⟨hDN', hHJ, hLH, hJ, _, _, hFFlift, _⟩ :=
    irreducibleReduction_lift ρ hfaith L A hLA hgen hA D I
      (hmap ▸ hLD) (hmap ▸ hI) hDI
  refine ⟨D.comap f, I.map U.subtype, hLH, hJ, hHJ,
    le_normalizer_of_normal, hFFlift hFF, ?_⟩
  exact centralQuotientRepresentation_injective_map_embedding ρ σ f U.subtype U.subtype_injective (fun _ _ => rfl)
    L hfL I hI.choose hIfaith

/-- The strengthening of B.1.11 used to exclude the triple cover of A₇
in B.1.13. The cubic-center hypothesis already suffices for this construction;
no ambient two-core or component assumption is needed. -/
theorem hasFaithfulIrreducibleFFSection_of_cubic_center (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hc : Nat.card (center L) = 3) (hLA : ⁅L,A⁆ = L) (hA : IsBestOffender ρ A) :
    HasFaithfulIrreducibleFFSection ρ L := by
  let K := L ⊔ A
  let L₀ := L.subgroupOf K
  let A₀ := A.subgroupOf K
  let : L₀.Normal := irreducibleReduction_normal L A hLA
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ K from le_sup_left)).symm
  have hcomm : ⁅L₀, A₀⁆ = L₀ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator]
    change ⁅(L.subgroupOf K).map K.subtype, (A.subgroupOf K).map K.subtype⁆ =
      (L.subgroupOf K).map K.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ K from le_sup_right), hLA]
  have hgen : L₀ ⊔ A₀ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup]
    change (L.subgroupOf K).map K.subtype ⊔ (A.subgroupOf K).map K.subtype =
      (⊤ : Subgroup K).map K.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ K from le_sup_right)]
    exact K.range_subtype.symm.trans K.subtype.range_eq_map
  have hc₀ : Nat.card (center L₀) = 3 :=
    (Nat.card_congr (centerCongr (subgroupOfEquivOfLe (show L ≤ K from le_sup_left))).toEquiv).trans hc
  obtain ⟨H, I, hLH, hI, hHI, hHN, hFF, hIfaith⟩ :=
    faithful_generated (ρ.comp K.subtype) (hfaith.comp K.subtype_injective)
      L₀ A₀ hcomm hgen (hA.subgroupOf ρ (show A ≤ K from le_sup_right)) hc₀
  refine ⟨H.map K.subtype, I, ?_,
    (IsIrrPlus.subgroupOf_iff ρ L K le_sup_left I).mp hI,
    map_stabilizes ρ K H I hHI, map_normalizes L K le_sup_left H hHN,
    section_image_isFFModule_to_ambient ρ L K le_sup_left H I hHI hHN hFF,
    centralQuotientRepresentation_injective_to_ambient ρ L K le_sup_left I hI hIfaith⟩
  have hm := Subgroup.map_mono (f := K.subtype) hLH
  rwa [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left)] at hm

end CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers
