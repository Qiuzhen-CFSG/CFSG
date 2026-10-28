module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableMarkedCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction

/-!
# The original marked core inside the actual star module

Restrict the original C.2.7 input to KR. Radical saturation puts O₂(KR)
inside R, so Ω₁Z(R) centralizes O₂(KR). Characteristic two then places that
same omega-center in O₂(KR), hence in the literal star module Ω₁Z(O₂(KR)).
No normality of K in the larger local group is assumed.

For the actual decomposable marking M_Z = C_G(E), the previously proved
E ≤ Ω₁Z(Q₁) therefore places E and its L-conjugate span in the star module.
The same selected component moves E because it escapes M_Z. This does not
identify that elementary span with the entire intrinsic block core.

Source: Aschbacher--Smith C.2.7, displayed (*), p.146, and 15.1.19--20,
printed pp.1093--1095.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

/-- The original radical omega-center lies in the literal star module after
restriction to KR; ambient component normality is unnecessary. -/
theorem omega_radical_le_starV_from_source (h : Input κ H R M K) :
    omegaOneCenterAmbient R ≤ (starV K R).map (K ⊔ R : Subgroup G).subtype := by
  let J := K ⊔ R
  let : (K.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  have hQR : J.pCoreIn 2 ≤ R := source_joinCore_le_radical (source_join_input h)
  have hself : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    rw [←source_join_fitting h]
    exact centralizer_generalizedFitting_le J
  intro x hx
  obtain ⟨hxR,hx2,hcent⟩ := (mem_omegaOneCenterAmbient_iff R x).mp hx
  let xJ : J := ⟨x,mem_sup_right hxR⟩
  have hxC : xJ ∈ centralizer (pCore 2 J : Set J) := by
    intro q hq
    exact Subtype.ext (hcent q (hQR (mem_map_of_mem J.subtype hq)))
  refine ⟨xJ,?_,rfl⟩
  change xJ ∈ omegaOneCenterAmbient (pCore 2 J)
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hself hxC,Subtype.ext hx2,fun q hq => hxC q hq⟩

end CFSG.Quasithin.ChapterC.C27Source

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The same actual marking and its component-conjugate span lie in the
star module, and the selected component acts nontrivially on that marking. -/
theorem marked_core_star_geometry (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hMZ : d.MZ = centralizer (E : Set G)) :
    E ≤ (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype ∧
      conjugateSpanBy E d.L ≤
        (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype ∧
      ⁅E,d.L⁆ ≠ ⊥ := by
  have hE := (d.le_omegaCenter_radical_of_marked_centralizer E hMZ).trans
    (omega_radical_le_starV_from_source hi)
  have hn : d.L ⊔ d.Q1 ≤ normalizer
      ((starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype : Set G) := by
    have hh := (starV d.L d.Q1).le_normalizer_map (d.L ⊔ d.Q1 : Subgroup G).subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨hE,conjugateSpanBy_le hE (le_sup_left.trans hn),?_⟩
  intro hc
  exact d.L_not_le_MZ ((le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hc)).trans_eq hMZ.symm)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
