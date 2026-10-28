module
public import Theory.Representation.BinaryOffender.CubicCenterHomogeneous
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FiveExclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRecognition

/-!
# Excluding the covered alternating component of the original amalgam

The component kernel on the omega span is O₂(C). Since that span lies in
R₂(CT), reducedness gives the same kernel on the entire reduced module.
If C/O₂(C) were the triple cover of A₆, cubic-center detection constructs
an actual chosen homogeneous module on which that quotient acts faithfully.
The fixed and fixed-free clauses of earlier 13.3.2 both identify its faithful
actor with ordinary A₆, contradicting the triple-cover order.

All component embeddings and relative centralizers are retained. The
original 13.3.2 module clauses remain explicit with producer qt-d-1332-source;
no module selection or action-kernel conclusion is assumed. ModelSelection
applies this exclusion to the actual nonsolvable pair.
Source: Aschbacher--Smith 13.4.5(4) and 13.4.7, printed pp.898,900,
using A.1.42 and original 13.3.2(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {C : Subgroup G}

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

open Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter1.Section02.LocalModels
variable {L V A B : Subgroup G}

/-- The original component has the same two-core kernel on the full reduced module. -/
theorem original_pair_component_reduced_kernel
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let C := K.map X.subtype
    (centralizer ((ReducedModule (C ⊔ (T : Subgroup G))).map
      (C ⊔ (T : Subgroup G)).subtype : Set G)).subgroupOf C = pCore 2 C := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let R := (ReducedModule X).map X.subtype
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  have hWR : W ≤ R := by
    have hh := map_mono (f := X.subtype) hred.le_reducedPSubgroup
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  obtain ⟨hn,_,_,_,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  have hCn : (C.subgroupOf X).Normal := by
    have hh : C.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
    exact hh.symm ▸ hn
  have hcore : C.pCoreIn 2 ≤ X.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn C X 2 (map_subtype_le K) hCn.isSubnormal
  have hcentral : X.pCoreIn 2 ≤ centralizer (R : Set G) := le_centralizer_iff.mp
    ((map_mono (f := X.subtype) (reducedPSubgroup_le_centralizer_pCore 2 X)).trans
      (map_centralizer_le_centralizer_image _ _))
  have hR : C ⊓ centralizer (R : Set G) = C.pCoreIn 2 := by
    apply le_antisymm
    · exact (inf_le_inf_left C (centralizer_le hWR)).trans_eq
        (original_pair_component_action_kernel h₀ D m h1332
          hTA hTB eA eB hne hindexA hindexB hres K hK)
    · exact le_inf (pCoreIn_le 2 C) (hcore.trans hcentral)
  have hgen := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  change X = C ⊔ (T : Subgroup G) at hgen
  have hk : (centralizer (R : Set G)).subgroupOf C = pCore 2 C := by
    apply map_injective C.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm]
    exact hR
  change (centralizer ((ReducedModule X).map X.subtype : Set G)).subgroupOf C = _ at hk
  rw [hgen] at hk
  exact hk

/-- A center-detecting chosen constituent excludes the actual triple-cover component. -/
theorem original_pair_component_not_covered
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    ¬ IsAlternatingCover ((K.map (A ⊔ B).subtype) ⧸
      pCore 2 (K.map (A ⊔ B).subtype)) 6 := by
  intro hcover
  let C := K.map (A ⊔ B).subtype
  obtain ⟨_,hf,_,hTC,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  obtain ⟨hq,⟨ez⟩,⟨es⟩⟩ := hcover
  have hc : Nat.card (center (C ⧸ pCore 2 C)) = 3 := by
    rw [Nat.card_congr ez.toEquiv]
    simp
  have hcard : Nat.card (C ⧸ pCore 2 C) = 1080 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
      Nat.card_congr es.toEquiv,hc,nat_card_alternatingGroup]
    norm_num
  obtain ⟨U,DU,hker⟩ := chosen_detects_cubic_reduced hTC hq hc
    (original_pair_component_reduced_kernel h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB hres K hK)
  let := DU.actionCentralizer_normal
  have he : Nonempty ((C ⧸ (centralizer (U : Set G)).subgroupOf C) ≃*
      alternatingGroup (Fin 6)) := by
    by_cases hfix : U ⊓ centralizer (C : Set G) = ⊥
    · obtain ⟨a⟩ := covered h₀ C hf ⟨hq,⟨ez⟩,⟨es⟩⟩ U DU hfix
      exact ⟨a.groupEquiv⟩
    · obtain ⟨a⟩ := fixed h₀ C hf U DU hfix
      exact ⟨a.groupEquiv⟩
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans he.some
  have hh := Nat.card_congr e.toEquiv
  rw [hcard,nat_card_alternatingGroup] at hh
  norm_num at hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
