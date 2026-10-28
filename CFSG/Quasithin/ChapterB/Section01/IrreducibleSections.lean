module

public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.Representation.BinaryOffender.Replacement
public import CFSG.Quasithin.ChapterB.Section01.Restriction
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleInvariance
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleReduction
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections
public import Theory.Representation.BinaryOffender.QuasisimpleCentralSection
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient

/-!
# Irreducible-section reduction for B.1

B.7.2(1) supplies invariance of the concrete Irr⁺ family from the residual
and central-chief-factor hypotheses. Thompson replacement gives its minimal
best-offender case, B.7.2(2) and B.1.5(3). The complete quasisimple invariant
section theorem B.1.5(8), including its quadratic-ratio-one conclusions, is
re-exported from `QuasisimpleSections`.

For B.1.11, pass inside K = L ⊔ A to the faithful action on C_V(O₂(K)).
The proved two-core reduction identifies its kernel, its quasisimple
generalized Fitting subgroup, and a best offender. Choose a minimal best
offender and an actual Irr⁺ section. B.1.5(3) makes their generated overgroup
stabilize that section. The central-section kernel centralizes L, so the
offender is faithful there and the section is an FF-module by the section
codimension comparison. Lift the section, action image and relative
centralizer inclusion through the fixed-space action and then through K ≤ G.
The resulting theorem assumes neither an Irr⁺ witness nor any FF or
centralizer conclusion. Irreducibility is part of the concrete `IsIrrPlus`
predicate on the literal quotient I/C_I(L).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed pp. 69–70, 72–73, and 119
(PDF pp. 80–81, 83–84, and 130).
-/

public section
namespace CFSG.Quasithin.ChapterB
open Subgroup Theory.GroupTheory Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- B.7.2(2): Thompson replacement lets every element of a minimal best
offender stabilize every member of the actual Irr⁺ family. -/
theorem source_lemma_B_7_2_2 (hfaith : Function.Injective ρ) {A X : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hne : X ≠ ⊥) (hres : pResidual 2 X = ⊤)
    (hXA : ⁅X, A⁆ = X) (hchief : HasCentralPChiefFactors 2 X)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    A ≤ subspaceStabilizer ρ I := by
  intro a ha
  exact source_lemma_B_7_2_1 ρ hfaith hA.1 hne hres hXA hchief ha
    (fun b hb v => hA.isQuadratic ρ b hb a ha v) hI

/-- B.1.5(3), including the vacuous case X = 1. Pointwise fixation refers to
members of Irr⁺, so the conclusion is setwise stabilization of each subspace. -/
theorem source_lemma_B_1_5_3 (hfaith : Function.Injective ρ) {A X : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hres : pResidual 2 X = ⊤)
    (hXA : ⁅X, A⁆ = X) (hchief : HasCentralPChiefFactors 2 X)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    A ≤ subspaceStabilizer ρ I := by
  have hne : X ≠ ⊥ := by
    intro hx
    apply hI.not_le_fixedSpace ρ
    rw [hx, fixedSpace_bot]
    exact le_top
  exact source_lemma_B_7_2_2 ρ hfaith hA hne hres hXA hchief hI

/-- The reduced B.1.11 construction. A minimal offender stabilizes an Irr⁺
section, and its generated overgroup acts on that section as an FF-module. -/
theorem irreducibleSections_of_trivial_twoCore (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hfit : generalizedFitting G = L) (hcore : pCore 2 G = ⊥)
    (hA : IsBestOffender ρ A) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ IsIrrPlus ρ L I ∧
      ∃ (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
        (centralSectionRepresentation ρ L H I hHI hHN).ker.map H.subtype ≤
          H ⊓ centralizer (L : Set G) := by
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
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_faithful ρ hfaith L
    ((nontrivial_iff_ne_bot L).mp inferInstance)
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
    centralSection_kernel_le_centralizer ρ L H le_sup_left I hI hHI hHN⟩


/-- Lift the complete reduced construction through C_V(O₂(G)) when G = LA.
The kernel and both section conclusions are supplied by proved source steps. -/
theorem irreducibleSections_in_generated_group (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hLA : ⁅L, A⁆ = L) (hgen : L ⊔ A = ⊤) (hA : IsBestOffender ρ A) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ IsIrrPlus ρ L I ∧
      ∃ (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
        (centralSectionRepresentation ρ L H I hHI hHN).ker.map H.subtype ≤
          H ⊓ centralizer (L : Set G) := by
  let U := fixedSpace ρ (pCore 2 G)
  let σ := subspaceImageRepresentation ρ U
  let f := invariantActionHom ρ U (fixedSpace_stable_of_normal ρ (pCore 2 G))
  obtain ⟨_, _, hcore, hquasi, hfit, _, hbest, _⟩ :=
    irreducibleReduction_generated ρ hfaith L A hLA hgen hA
  have hmap : L.map f = restrictedSubgroup ρ U L := invariantActionHom_map ρ U _ L
  let : IsQuasisimple (L.map f) := hmap.symm ▸ hquasi
  obtain ⟨D₀, I, hLD, hI, hDI, hDN, hFF, hcent⟩ :=
    irreducibleSections_of_trivial_twoCore σ (subspaceImageRepresentation_injective ρ U)
      (L.map f) (restrictedSubgroup ρ U A) (hfit.trans hmap.symm) hcore hbest
  obtain ⟨hDN', hHJ, hLH, hJ, _, _, hFFlift, hcentlift⟩ :=
    irreducibleReduction_lift ρ hfaith L A hLA hgen hA D₀ I
      (hmap ▸ hLD) (hmap ▸ hI) hDI
  exact ⟨D₀.comap f, I.map U.subtype, hLH, hJ, hHJ, le_normalizer_of_normal,
    hFFlift hFF, hcentlift hcent⟩

/-- B.1.11: a quasisimple subgroup generated by its commutators with a best
offender has an invariant irreducible central section that is an FF-module
for its actual action image. The action kernel in H centralizes L. Normality
is required only inside the constructed H, not in the original ambient G. -/
theorem source_lemma_B_1_11 (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ IsIrrPlus ρ L I ∧
      ∃ (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
        (centralSectionRepresentation ρ L H I hHI hHN).ker.map H.subtype ≤
          H ⊓ centralizer (L : Set G) := by
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
  obtain ⟨H, I, hLH, hI, hHI, hHN, hFF, hcent⟩ :=
    irreducibleSections_in_generated_group (ρ.comp K.subtype) (hfaith.comp K.subtype_injective) L₀ A₀
      hcomm hgen (hA.subgroupOf ρ (show A ≤ K from le_sup_right))
  refine ⟨H.map K.subtype, I, ?_,
    (IsIrrPlus.subgroupOf_iff ρ L K le_sup_left I).mp hI,
    map_stabilizes ρ K H I hHI, map_normalizes L K le_sup_left H hHN,
    section_image_isFFModule_to_ambient ρ L K le_sup_left H I hHI hHN hFF,
    section_centralizer_to_ambient ρ L K le_sup_left H I hHI hHN hcent⟩
  have hm := Subgroup.map_mono (f := K.subtype) hLH
  rwa [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left)] at hm

end CFSG.Quasithin.ChapterB
