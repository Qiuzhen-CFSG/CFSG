module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerReduced
public import CFSG.Quasithin.Chapter10.SourceA5OffenderFixedGeometry
public import CFSG.Quasithin.Chapter10.SourceKernelControl
public import CFSG.Quasithin.ChapterB.InternalThompsonAction

/-!
# Thompson movement in the constrained point component

If the original Thompson subgroup fixes the promoted module, it fixes W
and its T-conjugate, hence the full original module. The kernel-normalizer
bound from 10.1.2 then places its normalizer in M. Intrinsic Thompson
Frattini factorization forces the point component into M, a contradiction.
The fixed-span inclusion and J(C_T(v))=J(T) remain genuine earlier inputs.
Source: Aschbacher–Smith10.2.9, printed p.751.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The Thompson subgroup of the source point Sylow moves the literal promoted
module. The fixed-span and point Thompson equalities are the two earlier-source
inputs; the contradiction uses the original full-module kernel normalizer. -/
theorem source_a5_point_thompson_not_centralizes
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (I : Subgroup G) (hLI : L ≤ I)
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))
    (hJP : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G))
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    ¬ elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ≤
      centralizer (conjugateSpanBy
        (⁅D.fullModule,L⁆ ⊓ centralizer
          ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I : Set G) := by
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let W := ⁅D.fullModule,L⁆
  let U := conjugateSpanBy (W ⊓ centralizer (S : Set G)) I
  have hUI : U ≤ I := conjugateSpanBy_le_self
    (inf_le_left.trans ((source_full_moved_le_component D).trans hLI))
  have hUH : U ≤ H := hUI.trans le_sup_left
  intro hc
  have hcW : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    hJP ▸ hc.trans (centralizer_le hspan)
  have htJ : t ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    normalizer_le_normalizer_elementaryAbelianMaxJ _ ((T : Subgroup G).le_normalizer ht)
  have hconj : (elementaryAbelianMaxJ (T : Subgroup G)).map
      (MulAut.conj t).toMonoidHom = elementaryAbelianMaxJ (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp htJ
  have hcWt : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (W.map (MulAut.conj t).toMonoidHom : Set G) := by
    rw [←hconj]
    exact (map_mono hcW).trans (map_centralizer_le_centralizer_image _ _)
  have hcV : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
    rw [source_nonnormal_fullModule_eq_moved_pair D hn ht hcross]
    exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hcW) (le_centralizer_iff.mp hcWt))
  have he := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G)
    ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G))
    (le_inf (sSup_le fun _ hA => hA.1) hcV) inf_le_left
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    D.simpleQTKE T D.maximal
  have hN : normalizer (elementaryAbelianMaxJ S : Set G) ≤ D.maximalLocal := by
    rw [show elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) from hJP, ←he]
    exact source_kernel_thompson_normalizer_le D hu
  obtain ⟨P,hP⟩ := hs
  have hjmap : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ S := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hP]
  let : (U.subgroupOf H).Normal := hr.normal
  have hc' : elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (U.subgroupOf H : Set H) := by
    intro a ha u hu
    apply Subtype.ext
    exact hc (hjmap ▸ mem_map_of_mem H.subtype ha) u hu
  have hf := congrArg (map H.subtype) (thompson_frattini P (U.subgroupOf H) hc')
  rw [Subgroup.map_sup, ←MonoidHom.range_eq_map, range_subtype] at hf
  apply hout
  apply (show I ≤ H from le_sup_left).trans
  rw [←hf]
  refine sup_le ?_ ?_
  · exact ((le_normalizer_map H.subtype).trans (by rw [hjmap]; exact hN))
  · rintro _ ⟨a,ha,rfl⟩
    apply hCW
    intro w hw
    have hwU : w ∈ U := hspan hw
    exact congrArg H.subtype (ha ⟨w,hUH hwU⟩ hwU)
end CFSG.Quasithin.Chapter10
