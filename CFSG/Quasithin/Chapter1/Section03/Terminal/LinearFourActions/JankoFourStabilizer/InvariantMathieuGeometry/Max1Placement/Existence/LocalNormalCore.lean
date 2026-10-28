module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.SeedFusion
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PairRanks
public import Mathlib.Tactic.FinCases

/-!
# Mathieu placement from the core of the actual J₄ local join

A full-Sylow overgroup with nontrivial two-core has an elementary central
closure. Minimality of that closure gives irreducibility under its ambient
normalizer, without maximality of the overgroup. The proved Sylow catalogues
put an irreducible closure in the Mathieu kernel. A 2B element forces its
normalizer into max1; the pure kernel catalogue otherwise leaves order at
most eight, since the order-sixteen candidate preserves a proper plane.

The final theorem transports this alternative back through the actual Sylow
conjugation. Its consumer is the normalized local A₈ section in15.3.32(3):
the small-order branch is excluded by its action, leaving an actual max1
candidate. No arbitrary maximal-overgroup two-core assertion is used.

Source: Aschbacher–Smith A.3.12(17) and15.3.32(3), printed pp.47–48,1133;
the matrix provenance is retained in the imported literal Sylow catalogues.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4 Janko4.OuterReduction.OddIndex Janko4.LocalStructure
open Janko4.LocalStructure.SylowNormalEights
attribute [local irreducible] modelGroup matrixA matrixB

/-- Irreducibility of the elementary central closure does not require maximality. -/
theorem centralClosure_normalizer_irreducible_of_elementary
    (S : Sylow 2 Model) (M : Subgroup Model) (hSM : S.toSubgroup ≤ M)
    [IsElementaryAbelian 2 (centralClosure S M hSM)] :
    ClosureNormalizerIrreducible ((centralClosure S M hSM).map M.subtype) := by
  intro B hBE hBN
  have hBM : B ≤ M := hBE.trans (map_subtype_le _)
  have hMN : M ≤ normalizer
      ((centralClosure S M hSM).map M.subtype : Set Model) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (centralClosure S M hSM).le_normalizer_map M.subtype
  have hBn : (B.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBM).mpr (hMN.trans hBN)
  let := hBn
  have hle : B.subgroupOf M ≤ centralClosure S M hSM := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hBM]
    exact hBE
  rcases centralClosure_minimal S M hSM (B.subgroupOf M) hle with h | h
  · left
    rw [← map_subgroupOf_eq_of_le hBM, h, Subgroup.map_bot]
  · right
    rw [← map_subgroupOf_eq_of_le hBM, h]

/-- An irreducible normal elementary Sylow subgroup either has small order,
or its full normalizer lies in literal max1. No maximality is assumed. -/
theorem irreducible_normal_elementary_small_or_mathieu
    (A : Subgroup Model) (hAS : A ≤ twoSubgroup)
    (hn : twoSubgroup ≤ normalizer (A : Set Model))
    (he : IsElementaryAbelian 2 A) (hi : ClosureNormalizerIrreducible A) :
    Nat.card A ≤ 8 ∨ normalizer (A : Set Model) ≤ certifiedMathieuSubgroup := by
  have hAK : A ≤ orderSpectrumKernel :=
    elementary_sylow_le_kernel_of_outside_certificates
      MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure
      (OutsideKernelOrders.outsideCatalogue_of_card
        (presentation_card_of_equiv
          (matrixEquivOfWords MatrixWords.pcGenerator_relations
            MatrixWords.pcGenerator_closure)))
      OutsideKernelOrders.matrixKernel_eq_orderSpectrumKernel
      OutsideKernelOrders.rankCertificates A hAS hn he hi
  by_cases hseed : ∃ u ∈ A, IsConj u KernelOrders.classSeed
  · obtain ⟨u, hu, hc⟩ := hseed
    exact Or.inr (KernelOrders.normalizer_le_max1_of_seed_conjugate A hAK u hu hc)
  · have hpure : ∀ u ∈ A, ¬ IsConj u KernelOrders.classSeed := by
      intro u hu hc
      exact hseed ⟨u, hu, hc⟩
    obtain ⟨i, rfl⟩ := KernelOrders.pureKernelCatalogue.1 A hAK hn hpure
    by_cases h5 : i = 5
    · subst i
      obtain ⟨B, hB, hne, hN⟩ := KernelOrders.PureNormalizers.candidate_five_obstruction
      rcases hi B hB.le hN with hb | hb
      · exact (hne hb).elim
      · exact (hB.ne hb).elim
    · left
      rw [KernelOrders.pureKernelCatalogue.2]
      fin_cases i <;> first | exact (h5 rfl).elim | decide


private theorem irreducible_map (A : Subgroup Model)
    (hA : ClosureNormalizerIrreducible A) (e : MulAut Model) :
    ClosureNormalizerIrreducible (A.map e.toMonoidHom) := by
  intro B hB hN
  have hle : B.map e.symm.toMonoidHom ≤ A := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hB
  have hn : normalizer (A : Set Model) ≤ normalizer (B.map e.symm.toMonoidHom : Set Model) := by
    have hm := map_mono (f := e.symm.toMonoidHom) hN
    rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq] at hm
    simpa [map_map] using hm
  rcases hA _ hle hn with h | h
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) h
    simpa [map_map] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) h
    simpa [map_map] using hm

/-- A full-Sylow overgroup with nontrivial core has a small canonical elementary
closure or lies in a genuine conjugate of the certified Mathieu overgroup. -/
theorem local_overgroup_of_twoCore_ne_bot
    (S : Sylow 2 Model) (M : Subgroup Model) (hSM : S.toSubgroup ≤ M)
    (hcore : pCore 2 M ≠ ⊥) :
    Nat.card (centralClosure S M hSM) ≤ 8 ∨
      ∃ H : Subgroup Model, M ≤ H ∧ Nonempty (H ≃* certifiedMathieuSubgroup) := by
  let := centralClosure_elementary_of_twoCore_ne_bot S M hSM hcore
  let T : Sylow 2 Model := twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup, index_map_subtype, localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S T
  let e := MulAut.conj g
  have hS : S.toSubgroup.map e.toMonoidHom = twoSubgroup := congrArg Sylow.toSubgroup hg
  let E := (centralClosure S M hSM).map M.subtype
  let A := E.map e.toMonoidHom
  have hES : E ≤ S.toSubgroup := by
    rintro x ⟨m, hm, rfl⟩
    exact centralClosure_le_restrictedSylow S M hSM hm
  have hMN : M ≤ normalizer (E : Set Model) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (centralClosure S M hSM).le_normalizer_map M.subtype
  have hEelem : IsElementaryAbelian 2 E := IsElementaryAbelian.map M.subtype
  let := hEelem
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.toMonoidHom
  have hAS : A ≤ twoSubgroup := hS ▸ map_mono hES
  have hAN : twoSubgroup ≤ normalizer (A : Set Model) := by
    rw [← hS, ← map_equiv_normalizer_eq]
    exact map_mono (hSM.trans hMN)
  have hAi := irreducible_map E (centralClosure_normalizer_irreducible_of_elementary S M hSM) e
  have hc : Nat.card A = Nat.card (centralClosure S M hSM) :=
    (card_map_of_injective e.injective).trans (card_map_of_injective M.subtype_injective)
  rcases irreducible_normal_elementary_small_or_mathieu A hAS hAN hAelem hAi with hs | hn
  · exact Or.inl (hc ▸ hs)
  · right
    let H := certifiedMathieuSubgroup.map e.symm.toMonoidHom
    refine ⟨H, ?_, ⟨(e.symm.subgroupMap certifiedMathieuSubgroup).symm⟩⟩
    have hmap : M.map e.toMonoidHom ≤ normalizer (A : Set Model) := by
      simpa only [map_equiv_normalizer_eq] using map_mono (f := e.toMonoidHom) hMN
    have hback := map_mono (f := e.symm.toMonoidHom) (hmap.trans hn)
    simpa [H, map_map] using hback

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
