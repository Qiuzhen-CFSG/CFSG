module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.CoreReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentCenters
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The surviving component rows after reduction (g)

The selected component has quotient A₅. Its image in the actual reduced
centralizer quotient is a nontrivial quotient of that simple group, hence
is again A₅. This retains the exact image and its inclusion in the offender
subgroup. Order sixty rules out each reducible linear B.5.1 row, while the
outer A₆--C₃ shape has only an A₆ component and is impossible here.

Thus the quasisimple and solvable branches are settled. Only the two
product-module branches of B.5.6 remain; their local module extraction
belongs to qt-d-13314-ordinary-blocks. The Irr⁺ branch is transported back
to the original conjugation representation and used in ModuleSieve/Selected.
Source: Aschbacher--Smith B.5.1, B.5.6 and 13.3.14, pp.99,105,893.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction ChapterB.QuasisimpleSource

private theorem not_linearThree_card_sixty {D : Type*} [Group D]
    (hc : Nat.card D = 60) (F : BinaryField)
    (e : D ≃* SL(3,F.Carrier)) : False := by
  have hd := card_subgroup_dvd_card (Matrix.PSL3.LinearThree.unipotentSL F.Carrier)
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,←Nat.card_congr e.toEquiv,hc,F.card_eq] at hd
  have htwo : 2 ∣ 2 ^ F.degree := dvd_pow_self _ (Nat.ne_of_gt F.degree_pos)
  have hdiv : 8 ∣ 60 := (show 8 ∣ (2 ^ F.degree) ^ 3 from pow_dvd_pow_of_dvd htwo 3).trans hd
  norm_num at hdiv

private theorem not_binaryLarge_card_sixty {D : Type*} [Group D]
    (hc : Nat.card D = 60) (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : D ≃* SL(n,BinaryField.two.Carrier)) : False := by
  let e0 := (ExtensionConsequences.degreeOneNaturalEquiv BinaryField.two rfl n).groupEquiv
  let e1 := (BinaryLinear.OuterCyclic.slEquivLinear n).trans
    (BinaryLinear.OuterCyclic.matrixEquivLinear n).symm
  have he := Nat.card_congr ((e.trans e0).trans e1).toEquiv
  rw [hc,Matrix.card_GL_field] at he
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at he

/-- Order sixty excludes every reducible component-action row of B.5.1. -/
theorem quasisimple_moved_irrPlus_of_card_sixty
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D)
    (hc : Nat.card C = 60) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s) :
    IsIrrPlus ρ C (moved ρ C) := by
  rw [←s.space_eq]
  cases h with
  | irreducible hi _ _ _ _ => exact hi
  | doubleThree F _ e _ _ => exact (not_linearThree_card_sixty hc F e.groupEquiv).elim
  | naturalDual n hn _ hm =>
    obtain ⟨e⟩ := hm
    exact (not_binaryLarge_card_sixty hc n hn e.groupEquiv).elim
  | repeatedNatural n _ hn _ _ _ hm =>
    obtain ⟨e⟩ := hm
    exact (not_binaryLarge_card_sixty hc n hn e.groupEquiv).elim

/-- Only the two actual product-module branches remain for an A₅-sized component.
The outer A₆–C₃ shape is excluded without adding any action coordinates to it. -/
theorem component_card_sixty_irrPlus_or_products
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D)
    (hC : IsComponent D C) (hc : Nat.card C = 60)
    (h : NontrivialAdequateAlternative ρ) :
    IsIrrPlus ρ C (moved ρ C) ∨
      Nonempty (SourceTwoFactorCase ρ) ∨ Nonempty (HyperplaneCase ρ) := by
  cases h with
  | quasisimple hq q =>
    have hF : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
    have he : C = generalizedFitting D :=
      hC.eq_of_le hF (component_le_generalizedFitting D C hC)
    subst C
    exact Or.inl (quasisimple_moved_irrPlus_of_card_sixty ρ _ hc q.sectionData q.clause_one)
  | symmetricThree c =>
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    let : Group.IsSolvable D := Group.isSolvable_of_surjective
      (f := c.equiv.symm.toMonoidHom) c.equiv.symm.surjective
    let := hC.2
    let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | hyperplane c => exact Or.inr (Or.inr ⟨c⟩)
  | outerSixThree c =>
    let := hC.2
    let := c.first_normal
    let := c.quotient_first_solvable
    have hle : C ≤ c.first := le_of_isPerfect_of_solvable_quotient C c.first
    have he : C = c.first := hC.eq_of_le c.first_isComponent hle
    have hh := Nat.card_congr ((MulEquiv.subgroupCongr he).trans c.firstEquiv).toEquiv
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh


private theorem simple_core_image_equiv
    {D Q : Type*} [Group D] [Group Q] (B : Subgroup D) (q : D →* Q)
    (hs : IsSimpleGroup (B ⧸ pCore 2 B))
    (hk : B.pCoreIn 2 ≤ q.ker) (hne : B.map q ≠ ⊥) :
    Nonempty ((B ⧸ pCore 2 B) ≃* B.map q) := by
  let f := q.subgroupMap B
  have hker : pCore 2 B ≤ f.ker := by
    intro b hb
    apply Subtype.ext
    exact hk (mem_map_of_mem B.subtype hb)
  let φ := QuotientGroup.lift (pCore 2 B) f hker
  have hsurj : Function.Surjective φ :=
    QuotientGroup.lift_surjective_of_surjective _ _ (q.subgroupMap_surjective B) _
  let := hs
  have hinj : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    rcases φ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hφ : φ = 1 := φ.ker_eq_top_iff.mp ht
      apply False.elim
      apply hne
      apply (eq_bot_iff_forall _).mpr
      intro b hb
      obtain ⟨x,hx⟩ := hsurj ⟨b,hb⟩
      have he := congrArg Subtype.val hx
      simpa only [hφ,MonoidHom.one_apply,OneMemClass.coe_one] using he.symm
  exact ⟨MulEquiv.ofBijective φ ⟨hinj,hsurj⟩⟩

open Chapter12.Section02 Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- Reduction (g) identifies the literal component of the offender quotient with A₅. -/
theorem ordinary_selected_offender_component_five
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    Nonempty ((((B.subgroupOf J).map q).subgroupOf N) ≃* alternatingGroup (Fin 5)) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hJH : J ≤ H := sup_le
    (sup_le (map_subtype_le _) (ordinary_point_residual_le_point d)) hTH
  let : K.Normal := ordinary_component_normal d h1332 K hK hf
  have hBN : H ≤ normalizer (B : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer (hJH.trans hBN)
  obtain ⟨hBq,hcomp,_⟩ :=
    ordinary_selected_offender_entry_of_original_source d hmax eL escape h1332 K hK hqK hf
  obtain ⟨_,⟨eB⟩⟩ := ordinary_selected_five_quotient_of_fixed_module_source d hmax eL escape
    h1332 fixed hc K hK hqK hf hn hgen
  let eBJ : BJ ≃* B := subgroupOfEquivOfLe hBJ
  let eQ := (QuotientGroup.congr _ _ eBJ (pCore_map_iso 2 eBJ)).trans eB
  have hs : IsSimpleGroup (BJ ⧸ pCore 2 BJ) := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact eQ.isSimpleGroup
  have hne : BJ.map q ≠ ⊥ := by
    intro he
    apply hcomp.isCComponent.ne_bot
    change (BJ.map q).subgroupOf N = ⊥
    rw [he,bot_subgroupOf]
  have hk : BJ.pCoreIn 2 ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    exact normal_pCore_le_centralizer_reducedPSubgroup 2 BJ
  obtain ⟨ei⟩ := simple_core_image_equiv BJ q hs hk hne
  exact ⟨(subgroupOfEquivOfLe hBq).trans (ei.symm.trans eQ)⟩

/-- The ordinary source now retains only the two product-module rows in B.5.6.
The first alternative is Irr⁺ for the original conjugation representation. -/
theorem ordinary_selected_irrPlus_or_products
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    IsIrrPlus (reducedRepresentation J) (B.subgroupOf J)
        (moved (reducedRepresentation J) (B.subgroupOf J)) ∨
      Nonempty (SourceTwoFactorCase (ρ.comp N.subtype)) ∨
      Nonempty (HyperplaneCase (ρ.comp N.subtype)) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  obtain ⟨hBq,hcomp,hrows⟩ :=
    ordinary_selected_offender_entry_of_original_source d hmax eL escape h1332 K hK hqK hf
  obtain ⟨e⟩ := ordinary_selected_offender_component_five d hmax eL escape h1332 fixed hc
    K hK hqK hf hn hgen
  have hcard : Nat.card (Bq.subgroupOf N) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rcases component_card_sixty_irrPlus_or_products (ρ.comp N.subtype) (Bq.subgroupOf N)
      hcomp hcard hrows with hi | hr
  · left
    have hspace : moved (ρ.comp N.subtype) (Bq.subgroupOf N) = moved ρ Bq := by
      rw [moved_comp_map,map_subgroupOf_eq_of_le hBq]
    rw [hspace] at hi
    have hi' : IsIrrPlus ρ Bq (moved ρ Bq) :=
      (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp hi
    have ha : reducedRepresentation J = ρ.comp q := by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro w
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (NormalElementaryQuotient.representation_apply W q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) g w).symm
    have hi'' := IsIrrPlus.map_embedding (reducedRepresentation J) ρ q
      (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)
      Function.injective_id (fun g w => by rw [ha]; rfl) BJ (moved ρ Bq) hi'
    change IsIrrPlus (reducedRepresentation J) BJ (moved (reducedRepresentation J) BJ)
    simpa only [Submodule.map_id,ha,moved_comp_map] using hi''
  · exact Or.inr hr

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
