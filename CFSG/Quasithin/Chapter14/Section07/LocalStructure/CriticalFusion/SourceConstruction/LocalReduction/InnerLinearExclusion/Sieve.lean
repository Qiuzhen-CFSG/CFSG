module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.C3Source

/-!
# Small and inner linear rows for the actual 14.7.52 sieve

Apply the completed 14.7.49 and inner 14.7.51 arguments to every actual
local component, retaining the original 14.7.48 point-residual inclusion
and Sylow supplement. The original 14.7.32 proof supplies relative
normality. The final theorem carries the intrinsic quotient of C ≤ I
through the canonical image under I.subtype; the inner action is on that
same ambient image. These are the literal component and quotient
conventions of WholeResidualAssembly.RowExclusions.

The graph and A₇ branches remain independent. These exports retain the
universal earlier-source inputs; `Guarded.SelectedSource` supplies the
same-G,T guarded successor for final source assembly. Source: Aschbacher–Smith,
refs/quasithin.pdf, 14.7.49–52, printed pp.1064–1065.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The two small rows and the nongraph linear rows, on every actual
local component used by the 14.7.52 sieve. Normality is obtained from
14.7.32; the point-residual and Sylow supplement are the original 14.7.48
outputs. The commuting-span output is not needed by these exclusions. -/
theorem local_component_small_inner_rows
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
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
  have hKn := local_cComponent_normal d h hab structural previous faithful earlier I K hI hKI hK
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.sylow_le_of_mem_Hz hI).trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hKn)
  have hm := plane_moved_of_core_commutator h core_commutator
  refine ⟨?_,?_,hn,?_⟩
  · rintro ⟨e⟩
    exact small_local_linearThree_impossible h hab structural previous faithful hm I hI
      (linearThree_full_quotient_at h (structural G T) I K hI hKI hKn hgen
        (e.trans Matrix.PSL3Two.equiv))
  · rintro ⟨e⟩
    exact small_local_alternatingSix_impossible h hab structural previous faithful hm I hI
      (alternatingSix_full_quotient_at h (structural G T) I K hI hKI hKn hgen e)
  · rintro n hn' ⟨e⟩ hi
    have hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2 := by
      refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
      exact ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n)).symm⟩
    rcases hn' with rfl | rfl
    · exact local_inner_linear_impossible d h hab structural previous faithful earlier hm
        I K hI hn hgen hLK (m := 3) (Or.inl rfl) hmodel hi
    · exact local_inner_linear_impossible d h hab structural previous faithful earlier hm
        I K hI hn hgen hLK (m := 4) (Or.inr rfl) hmodel hi

/-- Literal relative-component application for the original 14.7.52 row
sieve. The quotient is C/O₂(C), where C is a subgroup of the actual I;
the ambient inner action is on its canonical image under I.subtype.
The graph and A₇ rows remain with the independent exclusion owner. -/
theorem local_relative_component_small_inner_rows
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
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
  obtain ⟨h3,h6,hn,hlin⟩ := local_component_small_inner_rows d h hab structural previous
    faithful earlier core_commutator I (C.map I.subtype) hI (map_subtype_le _) hK hLC hgen
  let e := C.equivMapOfInjective I.subtype I.subtype_injective
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine ⟨?_,?_,hn,?_⟩
  · rintro ⟨c⟩
    exact h3 ⟨q.symm.trans c⟩
  · rintro ⟨c⟩
    exact h6 ⟨q.symm.trans c⟩
  · rintro n hn' ⟨c⟩
    exact hlin n hn' ⟨q.symm.trans c⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
