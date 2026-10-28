module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassicalCore
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.MovedAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Restriction
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Whole seven-letter blocks from the original seed normalizer action

The actual normalizer image is specified as A7. The original seed action,
its full centralizer kernel and its genuine B.5 source supply the entire
moved module. The original Baumann normalizer bound excludes the normal
characteristic alternative of C.1.24, reconstructing a block on the same L.
No whole-M generation or prior residual normalization is used. The star
image is not identified with this normalizer image by definition.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterB
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter14.Section06.Seven.Reconstruction
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G]

/-- Whole ordinary or exceptional seven-letter block on the original component,
from the literal original-seed normalizer image. -/
theorem PreparedChosenModule.raw_seven_blocks_of_normalizer_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    let H := L ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let q := QuotientGroup.mk' (centralizer (W : Set H))
    ∀ _e : (L.subgroupOf H).map q ≃* alternatingGroup (Fin 7),
      IsAlternatingBlock L 7 ∨ IsExceptionalA7Block L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let B := L.subgroupOf H
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let I := B.map q
  change ∀ e : I ≃* alternatingGroup (Fin 7),
    IsAlternatingBlock L 7 ∨ IsExceptionalA7Block L
  intro e
  obtain ⟨hr,_,hfitI,hqI,_,hIJ,_⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hL hq hf hout houtM
  let := h.elementary
  let := hr.elementary
  let := hq
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer inf_le_right)
  let : I.Normal := inferInstanceAs (B.map q).Normal
  let : IsQuasisimple I := hqI
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup I := e.isSimpleGroup
  let b : B ≃* L := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm
  have hzI : center I = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    exact e.injective (by simpa using hh)
  have hcI : centralizer (I : Set (H ⧸ C)) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxI : x ∈ I := by
      rw [show I = generalizedFitting _ from hfitI] at hx ⊢
      exact centralizer_generalizedFitting_le _ hx
    have hxz : (⟨x,hxI⟩ : I) ∈ center I := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hzI] at hxz
    exact congrArg Subtype.val hxz
  obtain ⟨f,ec,_,_,hfs,hec,_,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne hL hq hf hout houtM
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hsqL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hL.1)).mp
      (hsq.subgroup (L.subgroupOf (centralizer (Z1 : Set G))))
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hsqL
      (ChapterA.Section02.IsSectionOf.of_surjective f hfs)
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨m⟩ := AlternatingModels.nonempty_actionData ρ I e hcI hsqI
    (NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) hIJ
  have hn : S ≤ normalizer (L : Set G) := by
    apply h.raw_local_normalizes_of_oddRank hG T hZ hZne hL hq Nat.prime_three (by decide)
    by_contra hsmall
    let P : Sylow 3 (L ⧸ pCore 2 L) := Classical.choice inferInstance
    have hh := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega))
      (e.toMonoidHom.comp ec) (e.surjective.comp hec)
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3
      Nat.prime_three (by decide)] at hh
    omega
  obtain ⟨_,_,⟨P,hP⟩,_,_⟩ := h.raw_component_thompson hG T hM hJ hu hZ hL hq hf hout houtM
  have hB : B.IsCComponent := hL.2.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let : Group.IsPerfect B := hB.perfect
  have hfB : generalizedFitting B = pCore 2 B := by
    apply map_injective (f := b.toMonoidHom) b.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  have hfitH : generalizedFitting H = pCore 2 H :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (centralizer_pCore_sup_le 2 L R (hf ▸ centralizer_generalizedFitting_le L)
        (T.isPGroup'.to_le (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left)))
        inf_le_right)
  have hgen : B ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hres : pResidual 2 H = B :=
    (residuals_of_perfect_normal_sup_twoGroup B (P : Subgroup H) P.isPGroup' hgen).1
  have hprod : ∀ g : H, ∃ k ∈ B, ∃ t ∈ (P : Subgroup H), k*t=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
  have hcpu : (baumann (P : Subgroup H)).characteristicNormalizerClosure ≤ M.subgroupOf H := by
    have hBR : baumann S ≤ R := le_inf inf_le_left (inf_le_left.trans hn)
    have hBe : baumann R = baumann S := baumann_eq_of_intermediate S R hBR inf_le_left
    have hm : (baumann (P : Subgroup H)).map H.subtype = baumann S := by
      unfold baumann thompsonAlpha
      rw [baumann_map_injective H.subtype H.subtype_injective,hP]
      exact hBe
    have hb : baumann (P : Subgroup H) = (baumann S).subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [hm,map_subgroupOf_eq_of_le (hBR.trans le_sup_right)]
    rw [hb]
    exact characteristicNormalizerClosure_subgroupOf_le (hBR.trans le_sup_right)
      (h.caseI_marked_thompson_control hG T hM hJ hZ).2.2.1
  have hno : ∀ D : Subgroup (baumann (P : Subgroup H)),
      D.Characteristic → D ≠ ⊥ → ¬ (D.map (baumann (P : Subgroup H)).subtype).Normal := by
    intro D hD hne hnormal
    let := hD
    let := hnormal
    have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
      calc
        ⊤ = normalizer (D.map (baumann (P : Subgroup H)).subtype : Set H) := by rw [normalizer_eq_top]
        _ ≤ (baumann (P : Subgroup H)).characteristicNormalizerClosure :=
          normalizer_le_characteristicNormalizerClosure _ D hne
        _ ≤ M.subgroupOf H := hcpu
    exact houtM fun l hl => htop (show (⟨l,mem_sup_left hl⟩ : H) ∈ ⊤ from mem_top _)
  let : IsElementaryAbelian 2 (⁅W,B⁆ : Subgroup H) :=
    IsElementaryAbelian.of_le (commutator_le_left W B)
  have hw := moved_wholeModule W B q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) m e
  have hm : ⁅⁅W,B⁆,B⁆ = ⁅W,B⁆ := by
    rw [←hres]
    exact commutator_isPPerfect_idempotent _ W (isPPerfect_pResidual 2)
      (IsElementaryAbelian.isPGroup 2 W) le_normalizer_of_normal
  have hb := block_types_of_wholeModule B ⁅W,B⁆ hB hfitH hfB P hprod hno hm hw.1 hw.2
  exact hb.imp (RankOne.Solvable.isAlternatingBlock_of_equiv b)
    (RankOne.ExceptionalSevenControl.exceptional_of_equiv b)

end CFSG.Quasithin.Chapter15.Section01
