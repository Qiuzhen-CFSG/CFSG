module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CentralModule
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin

/-!
# Movement of the actual omega-center

The normal component source in C.2.7 uses the literal omega-center of O₂(KR).
Characteristic-normalizer control forces nontrivial action; quasisimple kernel
structure and maximum elementary subgroups give the actual source clauses.

Source: Aschbacher--Smith, C.2.7(1–2), printed pp.145–146.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

theorem joinCore_le_radical (K R : Subgroup G) [K.Normal]
    (hr : IsPRadical 2 R) : (K ⊔ R : Subgroup G).pCoreIn 2 ≤ R := by
  apply le_of_normalizer_le_normalizer_of_pCore_normalizer_le R _
    hr.isPGroup (isPGroup_pCoreIn 2 _) hr.2.le
  exact ((le_inf le_normalizer_of_normal le_rfl).trans
    (normalizer_inf_normalizer_le_normalizer_sup K R)).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem omega_radical_le_starV (K R : Subgroup G) [K.Normal]
    (hr : IsPRadical 2 R)
    (hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K) :
    omegaOneCenterAmbient R ≤ (starV K R).map (K ⊔ R : Subgroup G).subtype := by
  let J := K ⊔ R
  have hQ := joinCore_le_radical K R hr
  have hJc := centralizer_pCore_sup_le 2 K R hc hr.isPGroup le_normalizer_of_normal
  intro x hx
  obtain ⟨hxR,hx2,hcent⟩ := (mem_omegaOneCenterAmbient_iff R x).mp hx
  let xJ : J := ⟨x,mem_sup_right hxR⟩
  have hxC : xJ ∈ centralizer (pCore 2 J : Set J) := by
    intro a ha
    exact Subtype.ext (hcent a (hQ (mem_map_of_mem J.subtype ha)))
  have hxQ : xJ ∈ pCore 2 J := hJc hxC
  refine ⟨xJ,?_,rfl⟩
  change xJ ∈ omegaOneCenterAmbient (pCore 2 J)
  exact (mem_omegaOneCenterAmbient_iff _ xJ).mpr
    ⟨hxQ,Subtype.ext hx2,fun a ha => hxC a ha⟩

theorem outside_moves_starV (K R M : Subgroup G) [K.Normal]
    (hr : IsPRadical 2 R)
    (hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬ K ≤ M) :
    ¬ K.subgroupOf (K ⊔ R) ≤ starKernel K R := by
  intro hfix
  let C : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
  let : C.Characteristic := inferInstance
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hr.1
  have hCne : C ≠ ⊥ := omega_center_ne_bot hr.isPGroup
  have hKfix : K ≤ centralizer ((starV K R).map (K ⊔ R : Subgroup G).subtype : Set G) := by
    intro k hk v hv
    obtain ⟨a,ha,rfl⟩ := hv
    exact congrArg Subtype.val ((hfix (show (⟨k,mem_sup_left hk⟩ : (K ⊔ R : Subgroup G)) ∈
      K.subgroupOf (K ⊔ R) from hk)) a ha)
  have hLC : K ≤ centralizer (C.map R.subtype : Set G) :=
    hKfix.trans (centralizer_le (omega_radical_le_starV K R hr hc))
  exact hout ((hLC.trans (Subgroup.centralizer_le_normalizer _)).trans
    ((normalizer_le_characteristicNormalizerClosure R C hCne).trans hcontrol))
end CFSG.Quasithin.ChapterC.C27Source
