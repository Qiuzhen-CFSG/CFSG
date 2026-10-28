module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CoveredSelection

/-!
# The two remaining quotients of the actual second component

The exact action kernel on the second omega span is also the kernel on
R₂(Y). Since Y=K_Y T, a cubic-center detector in that reduced module
constructs a genuine chosen constituent. The fixed and fixed-free clauses
of original 13.3.2 exclude the triple-cover quotient. Original 13.3.16
excludes the unitary quotient. Thus the same component has an actual
SL₃(2) or A₆ quotient, retaining both original vertex residuals, the full
omega span, Thompson movement and both action-kernel identifications.

The earlier source premises remain explicit for the fixed-core assembly.
No model selection or chosen-constituent witness is supplied by the caller.
Source: Aschbacher--Smith 13.4.5(4), 13.4.7(3), printed pp.898,903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L C Y U : Subgroup G}

private theorem chosen_detects_cubic_reduced
    (hn : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hq : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : Nat.card (center (C ⧸ pCore 2 C)) = 3)
    (hk : (centralizer ((ReducedModule (C ⊔ (T : Subgroup G))).map
      (C ⊔ (T : Subgroup G)).subtype : Set G)).subgroupOf C = pCore 2 C) :
    ∃ U : Subgroup G, ∃ _D : ChosenModule T C U,
      (centralizer (U : Set G)).subgroupOf C = pCore 2 C := by
  let H := C ⊔ (T : Subgroup G)
  let A := C.subgroupOf H
  let ρ := reducedRepresentation H
  let j : A ≃* C := subgroupOfEquivOfLe le_sup_left
  have hcore : (pCore 2 C).comap j.toMonoidHom = pCore 2 A := by
    rw [←pCore_map_iso 2 j,comap_map_eq_self_of_injective j.injective]
  have hker : ((actionHom ρ).comp A.subtype).ker = pCore 2 A := by
    rw [←hcore]
    ext a
    change actionHom ρ a.val = 1 ↔ j a ∈ pCore 2 C
    rw [←hk,actionHom_eq_one_iff]
    constructor
    · intro ha v hv
      obtain ⟨w,hw,rfl⟩ := hv
      have hh := congrArg (fun u : Additive (ReducedModule H) => u.toMul.val.val)
        (ha (Additive.ofMul (⟨w,hw⟩ : ReducedModule H)))
      change a.val.val * w.val * a.val.val⁻¹ = w.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro ha v
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change a.val.val * v.toMul.val.val * a.val.val⁻¹ = v.toMul.val.val
      exact mul_inv_eq_iff_eq_mul.mpr ((ha _ (mem_map_of_mem H.subtype v.toMul.property)).symm)
  let jq := QuotientGroup.congr (pCore 2 A) (pCore 2 C) j (pCore_map_iso 2 j)
  let eq : (C ⧸ pCore 2 C) ≃* actionSubgroup ρ A := jq.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans (actionQuotientEquiv ρ A))
  let := hq
  let : IsQuasisimple (actionSubgroup ρ A) := IsQuasisimple.of_mulEquiv eq
  have hcent : Nat.card (center (actionSubgroup ρ A)) = 3 :=
    (Nat.card_congr (centerCongr eq).toEquiv).symm.trans hc
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hn)
  obtain ⟨J,hJ,hdetect⟩ := exists_homogeneous_detecting_cubic_image ρ A
    ((T : Subgroup G).subgroupOf H) le_normalizer_of_normal T.isPGroup'.comap_subtype hcent
  let D : ChosenModule T C (subspaceImage H J) := ⟨J,hJ,rfl⟩
  refine ⟨subspaceImage H J,D,le_antisymm ?_ (D.chosenAction_core.trans D.chosenAction_ker.le)⟩
  intro c hc
  have hcfix : D.chosenAction c = 1 := D.chosenAction_ker.ge hc
  have hfull : ρ (j.symm c).val = 1 := hdetect (j.symm c) (by
    intro v hv
    exact congrArg Subtype.val (LinearMap.congr_fun hcfix (⟨v,hv⟩ : D.space)))
  have hh : j.symm c ∈ ((actionHom ρ).comp A.subtype).ker :=
    (actionHom_eq_one_iff ρ _).mpr (fun v => LinearMap.congr_fun hfull v)
  rw [hker] at hh
  have him := mem_map_of_mem j.toMonoidHom hh
  rw [pCore_map_iso] at him
  exact him


/-- A normal component has its exact two-core kernel on the entire reduced
module whenever it has that kernel on a reduced submodule. -/
theorem reduced_kernel (hCY : C ≤ Y) (hUY : U ≤ Y)
    (hn : (C.subgroupOf Y).Normal) (hr : IsPReduced 2 (U.subgroupOf Y))
    (hk : C ⊓ centralizer (U : Set G) = C.pCoreIn 2) :
    (centralizer ((ReducedModule Y).map Y.subtype : Set G)).subgroupOf C = pCore 2 C := by
  let R := (ReducedModule Y).map Y.subtype
  have hUR : U ≤ R := by
    have hh := map_mono (f := Y.subtype) hr.le_reducedPSubgroup
    rwa [map_subgroupOf_eq_of_le hUY] at hh
  have hcore : C.pCoreIn 2 ≤ Y.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn C Y 2 hCY hn.isSubnormal
  have hcentral : Y.pCoreIn 2 ≤ centralizer (R : Set G) := le_centralizer_iff.mp
    ((map_mono (f := Y.subtype) (reducedPSubgroup_le_centralizer_pCore 2 Y)).trans
      (map_centralizer_le_centralizer_image _ _))
  apply map_injective C.subtype_injective
  rw [subgroupOf_map_subtype,inf_comm]
  exact le_antisymm ((inf_le_inf_left C (centralizer_le hUR)).trans_eq hk)
    (le_inf (pCoreIn_le 2 C) (hcore.trans hcentral))

/-- The cubic center of a covered component cannot act faithfully on this
reduced module under the original two module clauses of 13.3.2. -/
theorem not_covered_of_reduced_kernel
    (h₀ : Hypothesis1331 T L)
    (hf : C ∈ MainForward.faithfulLocalComponents T)
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (hk : (centralizer ((ReducedModule (C ⊔ (T : Subgroup G))).map
      (C ⊔ (T : Subgroup G)).subtype : Set G)).subgroupOf C = pCore 2 C) :
    ¬ IsAlternatingCover (C ⧸ pCore 2 C) 6 := by
  rintro ⟨hq,⟨ez⟩,⟨es⟩⟩
  have hc : Nat.card (center (C ⧸ pCore 2 C)) = 3 := by
    rw [Nat.card_congr ez.toEquiv]
    simp
  have hcard : Nat.card (C ⧸ pCore 2 C) = 1080 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
      Nat.card_congr es.toEquiv,hc,nat_card_alternatingGroup]
    norm_num
  obtain ⟨W,DW,hker⟩ := chosen_detects_cubic_reduced hTC hq hc hk
  let := DW.actionCentralizer_normal
  have he : Nonempty ((C ⧸ (centralizer (W : Set G)).subgroupOf C) ≃*
      alternatingGroup (Fin 6)) := by
    by_cases hfix : W ⊓ centralizer (C : Set G) = ⊥
    · obtain ⟨a⟩ := covered h₀ C hf ⟨hq,⟨ez⟩,⟨es⟩⟩ W DW hfix
      exact ⟨a.groupEquiv⟩
    · obtain ⟨a⟩ := fixed h₀ C hf W DW hfix
      exact ⟨a.groupEquiv⟩
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans he.some
  have hh := Nat.card_congr e.toEquiv
  rw [hcard,nat_card_alternatingGroup] at hh
  norm_num at hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

theorem exists_original_plane_second_models
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
    let U := conjugateSpanBy Z Y
    ∃ K : Subgroup Y, K.IsCComponent ∧ K.Normal ∧
      K.map Y.subtype ∈ MainForward.faithfulLocalComponents T ∧
      K.map Y.subtype ∈ Chapter1.LStar G T ∧
      (T : Subgroup G) ≤ normalizer (K.map Y.subtype : Set G) ∧
      ⁅U,K.map Y.subtype⁆ ≠ ⊥ ∧
      (Nonempty (((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) ≃*
        BinaryLinearThree.Group) ∨
        Nonempty (((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) ≃*
          alternatingGroup (Fin 6))) ∧
      K ⊓ centralizer (U.subgroupOf Y : Set Y) = K.pCoreIn 2 ∧
      pResidual 2 Y = K ∧ Y = K.map Y.subtype ⊔ (T : Subgroup G) ∧
      (pResidual 2 P).map P.subtype ≤ K.map Y.subtype ∧
      Y₂ ≤ K.map Y.subtype ∧
      ⁅K.map Y.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K.map Y.subtype ∧
      ⁅U,K.map Y.subtype⁆ = U ∧ 16 ≤ Nat.card U ∧
      U ⊓ centralizer (K.map Y.subtype : Set G) = ⊥ := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
  let U := conjugateSpanBy Z Y
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right.trans le_sup_right
  obtain ⟨K,hK,hn,hf,hstar,hTK,hm,hmodels,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩ :=
    exists_original_plane_second_generation h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM h1332
  refine ⟨K,hK,hn,hf,hstar,hTK,hm,?_,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩
  rcases hmodels with hl | ha | hc | hu
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hl
    let := Fintype.ofFinite F
    let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    exact Or.inl ⟨(e.trans (Atlas.fieldEquivPSL 3 a)).trans
      Matrix.PSL3Two.equiv.symm⟩
  · exact Or.inr ha
  · have hUY : U ≤ Y := conjugateSpanBy_le (fun z hz =>
      hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
    have hkG := congrArg (Subgroup.map Y.subtype) hker
    rw [←map_inf_centralizer_of_injective Y.subtype Y.subtype_injective,
      map_subgroupOf_eq_of_le hUY,map_pCoreIn_of_injective 2 _ _ Y.subtype_injective] at hkG
    have hnG : ((K.map Y.subtype).subgroupOf Y).Normal := by
      have hh : (K.map Y.subtype).subgroupOf Y = K :=
        comap_map_eq_self_of_injective Y.subtype_injective K
      exact hh.symm ▸ hn
    have hred := (original_plane_second_amalgam h₀ h structural D m
      hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
      Wplane hWplane hTplane hBplane).2.2.2.2.2.2.2.2.1
    have hkR := SecondGeneration.reduced_kernel (map_subtype_le K) hUY hnG hred hkG
    let C := K.map Y.subtype
    change (centralizer ((ReducedModule Y).map Y.subtype : Set G)).subgroupOf C = pCore 2 C at hkR
    have hY : Y = C ⊔ (T : Subgroup G) := hgen
    rw [hY] at hkR
    exact (SecondGeneration.not_covered_of_reduced_kernel h₀ hf hTK fixed covered hkR hc).elim
  · exact (Nonsolvable.selected_unitary_excluded h₀ h13316 hf hu).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
