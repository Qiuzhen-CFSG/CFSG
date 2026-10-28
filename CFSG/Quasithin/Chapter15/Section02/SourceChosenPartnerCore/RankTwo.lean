module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.MarkedDisplacement
public import CFSG.Quasithin.ChapterG.Section06.IrreducibleCentral
public import Theory.SpecificGroups.BinaryLinear.SylowCentralClosure
public import Theory.GroupTheory.CComponent.CentralClosure
public import Theory.SpecificGroups.PSL2.EvenOrder

/-!
# Rank two on the marked partner chief section

Assume that the chosen module is not contained in the partner two-core.
The faithful chief action constructed earlier has a Sylow-central involution
from the chosen module with displacement rank between one and two. G.6.4
would make a rank-one involution normally generate the faithful quotient.
In each of the two structural alternatives its normal closure is proper:
it lies in the inner automorphism group, or in a component normalizer.
Thus its displacement rank is two.

Saturation then places the source plane in this same chief section, gives a
nonzero image fixed by the actual H-image, and identifies the lower kernel
intersection and the index of the chosen module in the partner two-core.
No recognition of the chief module is assumed here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.2.27(2), printed p.1119. The earlier structural alternatives and quotient
identifications remain explicit; the Section 15.2 assembly discharges them.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The actual partner join inherits SQTK from its containing two-local group. -/
theorem source_chosen_partner_join_sqtk
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS) :
    IsSQTK KnownSimple.IsKnownSimple (partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton _
  have hLM : L ≤ Mc := sup_le
    (conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner))
    (hg.outside.1.1.2.trans hg.in_partner)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hLM)).mp
    ((h.ambient.twoLocal_sqtk hMc.1.1).subgroup (L.subgroupOf Mc))

/-- G.6.4 applied to the literal faithful quotient and the original Sylow marking. -/
theorem source_chosen_partner_rank_one_normalClosure
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      PartnerChiefQuotientProperties T V L ρ →
      ∀ a : L, (a : G) ∈ V → orderOf (q a) = 2 →
      (∀ t ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q t)) →
      Module.finrank (ZMod 2) (LinearMap.range (ρ (q a) - 1)) = 1 →
      normalClosure ({q a} : Set (L ⧸ pCore 2 L)) = ⊤ := by
  dsimp only
  intro ρ hp a ha ho hc hr
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨hf,hi,_,_,_,S,hS,hAS,_,_⟩ := hp
  let := hi
  change orderOf (q a) = 2 at ho
  apply ChapterG.Section06.normalClosure_eq_top_of_irreducible_central_rank_one
    ρ q (source_chosen_partner_join_sqtk h hg) (QuotientGroup.mk'_surjective _)
    (pCore_quotient_pCore_eq_bot 2) hf (q a)
    (by simpa only [ho] using pow_orderOf_eq_one (q a))
    (by intro he; rw [he,orderOf_one] at ho; omega) hr S
    (hAS (mem_map_of_mem q ha))
  intro s hs
  change s ∈ (S : Subgroup _) at hs
  rw [hS] at hs
  obtain ⟨t,ht,rfl⟩ := hs
  exact hc t ht

/-- The linear automorphism alternative excludes a rank-one central actor. -/
theorem source_chosen_partner_rank_two_of_linear_automorphisms
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hnoncore : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {U B : Subgroup G} :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
      (_d : BinaryConjugationSection L U B (ρ.comp q)),
      U ≤ twoCoreIn Mc → centralInvolutions T ≤ B →
      PartnerChiefQuotientProperties T V L ρ →
      ∀ n : ℕ, (n = 4 ∨ n = 5) →
      (L ⧸ pCore 2 L) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) →
      ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
        (∀ t ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q t)) ∧
        Module.finrank (ZMod 2) (LinearMap.range (ρ (q a) - 1)) = 2 := by
  dsimp only
  intro ρ d hU hB hp n hn e
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  obtain ⟨a,ha,ho,hc,hlo,hhi⟩ :=
    source_chosen_partner_marked_central_displacement h hg hMc hZ hnoncore ρ d hU hB hp
  refine ⟨a,ha,ho,hc,?_⟩
  by_contra hne
  change 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) at hlo
  change Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) ≤ 2 at hhi
  change Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) ≠ 2 at hne
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) = 1 := by omega
  have hgen := source_chosen_partner_rank_one_normalClosure h hg ρ hp a ha ho hc hr
  let f := e.trans (MulAut.congr (BinaryLinear.OuterCyclic.projectiveEquivLinear
    (n := n) (show 0 < n by omega)))
  obtain ⟨_,_,_,_,_,S,hS,_,_,_⟩ := hp
  let P := S.mapSurjective (f := f.toMonoidHom) f.surjective
  have hcomm : ∀ s ∈ P, Commute (f (q a)) s := by
    rintro s ⟨b,hb,rfl⟩
    rw [hS] at hb
    obtain ⟨t,ht,rfl⟩ := hb
    exact (hc t ht).map f.toMonoidHom
  apply BinaryLinear.OuterCyclic.central_sylow_normalClosure_ne_top hn P (f (q a)) hcomm
  have he := congrArg (Subgroup.map f.toMonoidHom) hgen
  rw [Subgroup.map_normalClosure _ f.toMonoidHom f.surjective,Set.image_singleton,
    map_top_of_surjective f.toMonoidHom f.surjective] at he
  exact he

private theorem psl2_simple_even {X : Type*} [Group X] [Group.IsPerfect X]
    {q : ℕ} (hm : ClassicalGroup.IsPSL X 2 q) :
    IsSimpleGroup X ∧ 2 ∣ Nat.card X := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  refine ⟨e.isSimpleGroup,?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact Theory.PSL2.two_dvd_card

/-- Both genuine partner alternatives force rank two on the same chief action. -/
theorem source_chosen_partner_rank_two
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hnoncore : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {U B : Subgroup G} :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
      (_d : BinaryConjugationSection L U B (ρ.comp q)),
      U ≤ twoCoreIn Mc → centralInvolutions T ≤ B →
      PartnerChiefQuotientProperties T V L ρ →
      ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
        (∀ t ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q t)) ∧
        Module.finrank (ZMod 2) (LinearMap.range (ρ (q a) - 1)) = 2 := by
  dsimp only
  intro ρ d hU hB hp
  rcases hs with he | ⟨_,_,n,hn,_,⟨e⟩⟩ | ⟨C,t,_,hC,ht,htn,he,_,hm⟩
  · exact ((source_chosen_noncore_residual_lt h hg hquotient hres hnoncore).ne he.symm).elim
  · exact source_chosen_partner_rank_two_of_linear_automorphisms h hg hMc hZ hnoncore
      ρ d hU hB hp n hn e
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  obtain ⟨a,ha,ho,hc,hlo,hhi⟩ :=
    source_chosen_partner_marked_central_displacement h hg hMc hZ hnoncore ρ d hU hB hp
  refine ⟨a,ha,ho,hc,?_⟩
  by_contra hne
  change 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) at hlo
  change Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) ≤ 2 at hhi
  change Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) ≠ 2 at hne
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ (q a)-1)) = 1 := by omega
  have hgen := source_chosen_partner_rank_one_normalClosure h hg ρ hp a ha ho hc hr
  have hTM := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  have hCL : C ≤ L := (show C ≤ partnerSpan H Mc from he ▸ le_sup_left).trans le_sup_left
  have hDL : C.conjBy t ≤ L :=
    (show C.conjBy t ≤ partnerSpan H Mc from he ▸ le_sup_right).trans le_sup_left
  let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
  have hconj : (C.conjBy t).subgroupOf L = (C.subgroupOf L).conjBy tL := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hDL,map_conjBy_hom,map_subgroupOf_eq_of_le hCL]
    rfl
  have hpair : (partnerSpan H Mc).subgroupOf L =
      C.subgroupOf L ⊔ (C.subgroupOf L).conjBy tL := by
    rw [he,subgroupOf_sup hCL hDL,hconj]
  let : ((partnerSpan H Mc).subgroupOf L).Normal :=
    normal_subgroupOf_of_le_normalizer (hLM.trans (le_normalizer_conjugateSpanBy _ _))
  let : (C.subgroupOf L ⊔ (C.subgroupOf L).conjBy tL).Normal := hpair ▸ inferInstance
  have hCc : (C.subgroupOf L).IsCComponent := hC.2.subgroupOf_of_le hCL hLM
  have hdistinct : C.subgroupOf L ≠ (C.subgroupOf L).conjBy tL := by
    intro hh
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hm := congrArg (Subgroup.map L.subtype) hh
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le hCL] at hm
    exact hm.symm
  let := hC.2.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hC.1).toMonoidHom) (subgroupOfEquivOfLe hC.1).surjective
  let : Group.IsPerfect (C ⧸ pCore 2 C) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hm' : IsSimpleGroup (C ⧸ pCore 2 C) ∧ 2 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rcases hm with ⟨_,_,hm⟩ | ⟨_,_,_,hm⟩ <;> exact psl2_simple_even hm
  let := hm'.1
  let eC := subgroupOfEquivOfLe hCL
  let eQ := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  let : IsSimpleGroup (C.subgroupOf L ⧸ pCore 2 (C.subgroupOf L)) := eQ.isSimpleGroup
  have hdiv : 2 ∣ Nat.card (C.subgroupOf L ⧸ pCore 2 (C.subgroupOf L)) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact hm'.2
  obtain ⟨_,_,_,_,_,S,hS,_,_,_⟩ := hp
  have hcomm : ∀ s ∈ S, Commute (q a) s := by
    intro s hs
    change s ∈ (S : Subgroup _) at hs
    rw [hS] at hs
    obtain ⟨b,hb,rfl⟩ := hs
    exact hc b hb
  exact (normalClosure_ne_top_of_central_sylow_simpleCore_pair
    (C.subgroupOf L) hCc tL hdistinct hdiv S (q a) hcomm) hgen

open NoncentralChiefRefinement

/-- Construct the faithful marked chief section with saturated displacement and
a nonzero source-plane image fixed by the actual H-image. -/
theorem source_chosen_partner_saturated_chief
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
    let q := QuotientGroup.mk' (pCore 2 L)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
        σ.comp q = binarySectionRepresentation B U ∧
        PartnerChiefQuotientProperties T V L σ ∧
        (∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
          (∀ t ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q t)) ∧
          Module.finrank (ZMod 2)
            (LinearMap.range (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) = 2) ∧
        Nat.card (centralInvolutions T) = 2 ∧
        (V ⊓ twoCoreIn Mc).relIndex V = 2 ∧
        V ⊓ twoCoreIn Mc ≤ U.val.map L.subtype ∧
        (V ⊓ twoCoreIn Mc) ⊓ B.val.map L.subtype = centralInvolutions T ∧
        ZS ≤ U.val.map L.subtype ∧ ¬ ZS ≤ B.val.map L.subtype ∧
        ∃ w : Additive (Section B U), w ≠ 0 ∧
          (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → σ (q g) w = w) ∧
          (∀ g ∈ (H.subgroupOf L).map q, σ g w = w) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ :=
    source_chosen_partner_faithful_marked_chief h hg hMc hZ hquotient hres hs hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,he,hpσ⟩ := hσ
  have d : BinaryConjugationSection L (U.val.map L.subtype) (B.val.map L.subtype)
      (σ.comp q) := by
    rw [show σ.comp q = binarySectionRepresentation B U from he]
    exact ambientBinarySection L B U hc.le
  obtain ⟨a,ha,ho,hc',hr⟩ := source_chosen_partner_rank_two
    h hg hMc hZ hquotient hres hs hn σ d hU hB hpσ
  obtain ⟨hZcard,hindex,hCU,hker,hPU,hPB⟩ := source_chosen_partner_rank_two_saturates
    h hg hMc hZ hn d hU hB a ha hr.ge
  exact ⟨σ,he,hpσ,⟨a,ha,ho,hc',hr⟩,hZcard,hindex,hCU,hker,hPU,hPB,
    source_chosen_partner_plane_projection h hg hMc hZ σ d hPU hB hPB⟩

end CFSG.Quasithin.Chapter15.Section02
