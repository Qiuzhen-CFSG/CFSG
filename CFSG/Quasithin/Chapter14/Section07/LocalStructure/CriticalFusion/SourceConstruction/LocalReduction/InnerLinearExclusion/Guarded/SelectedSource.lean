module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.InnerSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Sieve

/-!
# Guarded small and inner linear exclusions on the original components

Apply the source exclusions at the same original G,T, using 14.7.47 for
relative component normality and the explicit 14.7.48 point inclusion and
Sylow supplement. The relative version uses the intrinsic C/O₂(C) and the
canonical image C.map I.subtype, exactly as the 14.7.52 sieve does.
The final leaf applies these results to the original selected component
under the multiple-overgroup guard; no universal record is constructed.
Original 14.7.47/48, 14.5.21(2), faithful classification and the graph/A₇
branches retain their independent producers and final assembly owner.
Source: Aschbacher–Smith 14.7.49–52, pp.1064–1065, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem local_component_small_inner_rows
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (source47 : WholeResidualAssembly.Earlier14747 F L)
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hLK : F.Li L 1 ≤ K) (hgen : I = K ⊔ (T : Subgroup G)) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (K : Set G),
        ∀ n : ℕ, (n = 4 ∨ n = 5) →
          Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
          ¬ (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
              MulAut.innerSubgroup (K ⧸ pCore 2 K)) := by
  have hKn := WholeResidualAssembly.local_component_normal_at h structural source47 I hI (K.subgroupOf I) hK
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.sylow_le_of_mem_Hz hI).trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hKn)
  have hm := plane_moved_of_core_commutator h core_commutator
  refine ⟨?_,?_,hn,?_⟩
  · rintro ⟨e⟩
    exact small_local_linearThree_impossible h hab structural previous faithful hm I hI
      (linearThree_full_quotient_at h structural I K hI hKI hKn hgen
        (e.trans Matrix.PSL3Two.equiv))
  · rintro ⟨e⟩
    exact small_local_alternatingSix_impossible h hab structural previous faithful hm I hI
      (alternatingSix_full_quotient_at h structural I K hI hKI hKn hgen e)
  · rintro n hn' ⟨e⟩ hi
    have hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2 := by
      refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
      exact ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n)).symm⟩
    rcases hn' with rfl | rfl
    · exact local_inner_linear_impossible h hab structural previous faithful hm
        I K hI hn hgen hLK (m := 3) (Or.inl rfl) hmodel hi
    · exact local_inner_linear_impossible h hab structural previous faithful hm
        I K hI hn hgen hLK (m := 4) (Or.inr rfl) hmodel hi

/-- Literal relative-component application for the original 14.7.52 row
sieve. The quotient is C/O₂(C), where C is a subgroup of the actual I;
the ambient inner action is on its canonical image under I.subtype.
The graph and A₇ rows remain with the independent exclusion owner. -/
theorem local_relative_component_small_inner_rows
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (source47 : WholeResidualAssembly.Earlier14747 F L)
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hLC : F.Li L 1 ≤ C.map I.subtype) (hgen : I = C.map I.subtype ⊔ (T : Subgroup G)) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6)) ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (C.map I.subtype : Set G),
        ∀ n : ℕ, (n = 4 ∨ n = 5) →
          Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
          ¬ (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 (C.map I.subtype)).quotientAut
              ((C.map I.subtype).normalizerMonoidHom ⟨t,hn ht⟩) ∈
                MulAut.innerSubgroup (C.map I.subtype ⧸ pCore 2 (C.map I.subtype))) := by
  have hK : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  obtain ⟨h3,h6,hn,hlin⟩ := local_component_small_inner_rows h hab structural previous
    faithful source47 core_commutator I (C.map I.subtype) hI (map_subtype_le _) hK hLC hgen
  let e := C.equivMapOfInjective I.subtype I.subtype_injective
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine ⟨?_,?_,hn,?_⟩
  · rintro ⟨c⟩
    exact h3 ⟨q.symm.trans c⟩
  · rintro ⟨c⟩
    exact h6 ⟨q.symm.trans c⟩
  · rintro n hn' ⟨c⟩
    exact hlin n hn' ⟨q.symm.trans c⟩


/-- The actual original selected component receives both small exclusions
and the inner linear exclusions from guarded same-G,T inputs. The earlier
14.7.48 outputs remain attached to that same component. -/
theorem original_component_small_inner_exclusions_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (source47 : WholeResidualAssembly.Earlier14747 F L)
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (source48 : F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧
      F.UH F.H = ⁅F.UH F.H,K⁆) :
    F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧
      F.UH F.H = ⁅F.UH F.H,K⁆ ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (K : Set G),
        ∀ n : ℕ, (n = 4 ∨ n = 5) →
          Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
          ¬ (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
              MulAut.innerSubgroup (K ⧸ pCore 2 K)) := by
  have hH := h.point_mem_Hz_at F (previous hmany)
  exact ⟨source48.1,source48.2.1,source48.2.2,
    local_component_small_inner_rows h hab (structural hmany) (previous hmany)
      faithful source47 core_commutator F.H K hH hKH hK source48.1 source48.2.1⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
