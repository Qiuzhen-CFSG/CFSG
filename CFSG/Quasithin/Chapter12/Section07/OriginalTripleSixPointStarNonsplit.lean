module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPushingUpAt
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedPlacement
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The original fixed point forces the constrained star cover to be nonsplit

The unchanged Lt lies in the selected constrained component. Consequently
U=[U,Lt] embeds in the actual component-moved star module. The original
point t is nonzero in that embedding and fixed by the full component,
since the component lies in C_G(t). The genuine B.5.1 conclusion therefore
has nontrivial moved-fixed intersection and its nonsplit-natural clause
applies to the same moved section, preserving all of U and the point.

Source: Aschbacher--Smith, B.5.1(2) and the constrained branch of12.7.5,
printed pp.99--103,840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

set_option maxHeartbeats 400000 in
/-- The whole original module and its original point lie in a nonsplit
classified star cover on the actual selected constrained component. -/
theorem original_tripleSix_point_star_nonsplit_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G))) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬ J ≤ (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)).subgroupOf
      (centralizer ({(t : G)} : Set G)))
    (hf : generalizedFitting J = pCore 2 J) :
    let H := centralizer ({(t : G)} : Set G)
    let Jg := J.map H.subtype
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    let ρ := starRepresentation Jg Q
    let O := offenderSubgroup ρ
    let C := starImage Jg Q Jg
    ∃ _hCO : C ≤ O,
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp O.subtype) (C.subgroupOf O),
      ∃ f : U →* starV Jg Q,
        Function.Injective f ∧
        (∀ u, (((f u) : (Jg ⊔ Q : Subgroup G)) : G) = u) ∧
        (∀ u, Additive.ofMul (f u) ∈ c.sectionData.space.toSubmodule) ∧
        Additive.ofMul (f t) ∈ fixedSpace (ρ.comp O.subtype) (C.subgroupOf O) ∧
        IsIrrPlus (ρ.comp O.subtype) (C.subgroupOf O) c.sectionData.space.toSubmodule ∧
        NonsplitNatural (c.sectionData.action.comp (C.subgroupOf O).subtype) := by
  let H := centralizer ({(t : G)} : Set G)
  let M := normalizer (K : Set G) ⊓ H
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let Jg := J.map H.subtype
  let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let ρ := starRepresentation Jg Q
  let O := offenderSubgroup ρ
  let C := starImage Jg Q Jg
  let S := Jg ⊔ Q
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hn := (tripleSixPointResidual_component D a t ht heven).1
  have hLJ := h28.constrained_normal_seed_le hn J hJ hq hout hf
  have hLH : Lt ≤ H := (map_subtype_le _).trans inf_le_right
  have hLJg : Lt ≤ Jg := by
    have hm := map_mono (f := H.subtype) hLJ
    rwa [map_subgroupOf_eq_of_le hLH] at hm
  have hUstar : U ≤ (starV Jg Q).map S.subtype :=
    h28.constrained_module_le_starV J hJ hq hout hf
  let e := (starV Jg Q).equivMapOfInjective S.subtype S.subtype_injective
  let f : U →* starV Jg Q := e.symm.toMonoidHom.comp (inclusion hUstar)
  have hamb (u : U) : (((f u) : S) : G) = u := by
    exact congrArg Subtype.val (e.apply_symm_apply (inclusion hUstar u))
  have hinj : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    exact (hamb u).symm.trans ((congrArg (fun x : starV Jg Q =>
      ((x : S) : G)) he).trans (hamb v))
  have hUmoved : U ≤ (⁅starV Jg Q,Jg.subgroupOf S⁆).map S.subtype := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show Jg ≤ S from le_sup_left)]
    conv_lhs => rw [(tripleSixPointCentralizerResidual_commutator D a t ht heven).1]
    exact commutator_mono hUstar hLJg
  obtain ⟨hCO,⟨c⟩⟩ := ChapterC.C27Source.star_moved_section_from_source
    (h28.constrained_source_input J hJ hq hout hf)
  have hspace : c.sectionData.space.toSubmodule =
      NormalElementaryQuotient.commutatorSpace (starV Jg Q) (Jg.subgroupOf S) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (starV Jg Q)
      (QuotientGroup.mk' (starKernel Jg Q)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _),c.sectionData.space_eq]
    change subspaceCommutator _ ⊤ _ = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCO]
    rfl
  have hm (u : U) : Additive.ofMul (f u) ∈ c.sectionData.space.toSubmodule := by
    rw [hspace]
    obtain ⟨w,hw,he⟩ := hUmoved u.property
    have he' : w = (f u).val := Subtype.ext (he.trans (hamb u).symm)
    change (f u).val ∈ ⁅starV Jg Q,Jg.subgroupOf S⁆
    exact he' ▸ hw
  have hfix : Additive.ofMul (f t) ∈ fixedSpace (ρ.comp O.subtype) (C.subgroupOf O) := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hCO]
    rintro ⟨x,hx⟩
    obtain ⟨j,hj,rfl⟩ := hx
    change ρ (QuotientGroup.mk' (starKernel Jg Q) j) (Additive.ofMul (f t)) = _
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [starRepresentation_apply]
    simp only [toMul_ofMul]
    change (j : G) * (((f t) : S) : G) * (j : G)⁻¹ = (((f t) : S) : G)
    rw [hamb t]
    have hjH : (j : G) ∈ H := (map_subtype_le J) hj
    exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hjH)
  have hne : Additive.ofMul (f t) ≠ 0 := by
    intro hz
    exact ht (hinj ((congrArg Additive.toMul hz).trans f.map_one.symm))
  have hnonsplit : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace (ρ.comp O.subtype) (C.subgroupOf O)) := by
    intro hc
    exact hne (Submodule.disjoint_def.mp hc.disjoint _ (hm t) hfix)
  exact ⟨hCO,c,f,hinj,hamb,hm,hfix,c.clause_two hnonsplit⟩

end CFSG.Quasithin.Chapter12.Section07
