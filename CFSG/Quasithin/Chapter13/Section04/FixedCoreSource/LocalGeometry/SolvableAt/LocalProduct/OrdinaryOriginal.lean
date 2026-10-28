module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstParabolicAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.LargerRow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.LargerSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.SourceProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OrdinaryOriginal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagCore
/-!
# The ordinary solvable branch on the original R₁: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/OrdinaryOriginal` proof for the local step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- Both action-kernel cases under the source Baumann-normalizer bound. -/
theorem centralizer_pair_quotient_of_ordinary_baumann_original_R1_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hB : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  obtain ⟨e⟩ := ordinary
  have ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := ⟨e⟩
  refine ⟨ordinary,?_⟩
  have hR := firstFlagCore_eq_firstParabolicCore_at h structural D m e z hz hzL
  generalize hRa : firstFlagCore_at h structural D m = R at hB ⊢
  have hRc : R = firstParabolicCore T L z.val := hRa.symm.trans hR
  clear hRa hR
  subst R
  obtain ⟨hRT,hnR,hAN,hQR⟩ := firstParabolicCore_local_data (L := L) hz
  have h1339' : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3 := by
    intro Y hYH hn hYM hp
    exact (h1339 Y hYH hn hYM hp).imp_right (fun hh => hh.2)
  by_cases hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G))
  · let f := (firstParabolicAction_at h structural D m z.val).rangeRestrict.comp
      (inclusion (show (T : Subgroup G) ≤ firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
        from le_sup_right))
    have hRf : firstParabolicCore T L z.val =
        ((pCore 2 (firstParabolicAction_at h structural D m z.val).range).comap f).map
          (T : Subgroup G).subtype :=
      (firstActionCore_eq_firstParabolicCore_at h structural D m e hz).symm
    have hcore : IsPGroup 2 (centralCore L) := by
      rw [centralCore_eq_twoCore_of_ordinary e]
      exact pCore_isPGroup
    obtain ⟨horder,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hcore z hzL
    obtain ⟨_,_,hI,hr,hprod,hinter,_,hset⟩ :=
      centralizer_single_factor_source_product_of_baumann_bound_at h₀ h structural hz hzL
        f (firstParabolicCore T L z.val) hRf hQR hsolv hkernel hB hout hindex
        horder hthree hAN h1339' h1342
    have hq := centralizer_pair_quotient_of_source_product D m hcore z hzL hz
      (firstParabolicCore T L z.val) hRT hI hprod hinter hout
    have hu := centralizer_thompson_unique_of_source_product D m hcore z hzL hz
      (firstParabolicCore T L z.val) hRT hI hprod hinter hout
    exact ⟨hq,hI,hr,hprod,hinter,hset,hu⟩
  · have hsel : selectedFirstResidual T L V z.val = firstCentralizerResidual L z.val := by
      simp only [selectedFirstResidual,if_pos ordinary]
    have hres := (centralizer_kernel_residual_of_source1339_at h₀ h structural D m z hz hzL
      hkernel (selectedFirstResidual T L V z.val) h1339).1.trans hsel
    obtain ⟨S,hS⟩ := firstParabolicCore_residual_sylow h₀ hz
      (fun he => hzL (he ▸ one_mem _)) hres
    exact centralizer_pair_quotient_of_ordinary_larger_kernel_at h₀ h structural D m ordinary
      z hz hzL (firstParabolicCore T L z.val) hRT S hS hres hB hsolv hout hindex h1339' h1342

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
