module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalComplete
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.ReselectionApplication

/-!
# Faithfulness of the original non-A₅ Hall action

In the moving-Thompson branch the established full-module fixation argument
already kills the kernel. In the quiet branch the literal kernel fixes the
nonzero Sylow-fixed orbit, which is fully moved by L₀. The local normalizer
bound contradicts the escaping elementary actor supplied by 4.4.13.
Hall conjugacy in the original solvable overlap then proves the exact
arbitrary-Hall contract. No module-generation or model callback remains.

Source: Aschbacher--Smith 10.2.3(2), p.745, using 10.1.3 and 4.4.3,13--14.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The intrinsic Cartan Hall subgroup has trivial kernel on the literal L₀/O₂(L₀). -/
theorem source_nonnormal_intrinsic_hall_kernel_eq_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n) :
    d.witness.abelianGroup ⊓ (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥ := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · by_contra hk
    have hfix := source_hall_kernel_fixes_fixed_span_of_local_thompson_centralizes D hJ hH
      d.witness.abelianGroup (he ▸ d.hall_le) (he ▸ d.hall)
    obtain ⟨p,A,hp,ho,_,hne,hAe,hAY,hAC,hAT,hout⟩ :=
      source_hstar_hall_kernel_escaping_coprime D hn hH hlarge hP d hk
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    exact hout (source_local_oddPrimeActor_normalizer D hn (sourceQuietFixedSpan D)
      (sourceQuietFixedSpan_le D) (sourceQuietFixedSpan_ne_bot D)
      (sourceQuietFixedSpan_commutator D hmany hJ).symm (sourceQuietFixedSpan_normalized D)
      ho A hne (IsElementaryAbelian.isPGroup p A) hAC ((le_inf hAY hAC).trans hfix) hAT)
  · exact source_hstar_hall_kernel_eq_bot_of_full_fixation D hn hH hlarge hP d
      (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ
        d.witness.abelianGroup (he ▸ d.hall_le) (he ▸ d.hall))

omit D in
/-- The exact nonnormal non-A₅ Hall-faithfulness contract, without extra premises. -/
theorem source_nonnormalHallFaithful : SourceNonnormalHallFaithfulAt T := by
  intro hmany L D hmin hn hna H hH hlarge B hBM hB _ _
  obtain ⟨hP,_,_,_,d,he,_,_⟩ := source_hstar_cartan_data_of_generation_gt_one D hH hlarge
  exact source_hall_sectionKernel_faithful_of_hall_conjugacy
    (M := D.maximalLocal) (X := localOrbit T L) le_rfl
    (he ▸ d.maximal_solvable) hBM hB (he ▸ d.hall)
    (source_nonnormal_intrinsic_hall_kernel_eq_bot D hmany hmin hn hna hH hlarge hP d)

omit D in
/-- The absorbed module-fixation contract follows with the original setup unchanged. -/
theorem source_nonnormalHallKernelModule : SourceNonnormalHallKernelModuleAt T := by
  intro hmany L D hmin hn hna H hH hlarge B hBM hB hcomm hperm
  refine ⟨D,?_⟩
  rw [source_nonnormalHallFaithful hmany L D hmin hn hna H hH hlarge B hBM hB hcomm hperm]
  exact bot_le

end CFSG.Quasithin.Chapter10
