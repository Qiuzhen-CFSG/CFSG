module
public import CFSG.Quasithin.Chapter10.SourceA5PointConstrainedInspection
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimpleDispatch
public import CFSG.Quasithin.Chapter10.SourceA5ModuleAlternatives

/-!
# Original point control after the constrained component inspection

The constrained component branch is proved from the original point data.
Splitting on quasisimplicity therefore leaves only the independent marked
quasisimple embedding input. The original minimal-setup consumer applies
this inspection to point centralizers and weak closure after excluding the
tensor branch. No constrained action, quotient or module input remains.

Source: Aschbacher–Smith10.2.9–12, pp.750–754. The quasisimple marking,
local cubic bound and tensor exclusion retain their independent producers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The completed constrained branch leaves exactly the quasisimple marking input. -/
theorem source_a5_point_inspection_of_quasisimple_markings
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hmarks : SourceA5PointQuasisimpleMarkingInput D v) :
    SourceA5PointComponentInspection D e t v := by
  intro I hLI hIX hI hNI hout hgen _
  by_cases hquasi : IsQuasisimple I
  · exact source_a5_point_quasisimple_alternative_of_source_markings D e t
      hv hcross hmarks I hLI hIX hI hNI hout hgen hquasi
  · exact source_a5_point_constrained_alternative D e hi ht htn hcross
      hv hvne I hLI.le hIX hI hNI hquasi hout hs

/-- Original point control and weak closure with every constrained inspection
premise removed, retaining the independent quasisimple source markings. -/
theorem source_a5_point_control_of_quasisimple_markings
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hlocal : SourceLocalModuleCubicBound D)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ¬ Nonempty (SourceA5TensorModel D e))
    (hmarks : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointQuasisimpleMarkingInput D v) :
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  have hproper := source_a5_seed_ne_local_of_no_tensor D e hn hD hmany hnot
  obtain ⟨_,hi,hcross,_⟩ :=
    source_a5_original_proper_seed_control D e hn ht htn hD hproper hlocal hmany
  apply source_a5_point_control_of_no_tensor D e hn ht htn hD hlocal hmany hnot
  intro v hv hvne hs
  exact source_a5_point_inspection_of_quasisimple_markings D e hi ht htn hcross
    hv hvne hs (hmarks v hv hvne hs)

end CFSG.Quasithin.Chapter10
