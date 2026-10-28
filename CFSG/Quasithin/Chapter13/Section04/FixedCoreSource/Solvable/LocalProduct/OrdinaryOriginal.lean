module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagCore
/-!
# The ordinary solvable branch on the original R₁

Use the original first-flag action core, now identified with O₂(L₁T).
When the Baumann normalizer lies in M, the checked source arguments
supply Thompson noncentrality in both kernel cases. In the larger case,
13.3.9 identifies the literal kernel residual with L₁ and the
residual-section Sylow witness is constructed on the original T.

The final theorem combines this with the short-block branch. It proves
the S₃×S₃ centralizer quotient, S₃ Thompson quotient, rank-two moved
plane, literal product H=L₁IT, intersection H∩M=L₁T and IT uniqueness.
The only case split is the genuine earlier13.2.2(7) alternative; its
13.2.2(5–6), 13.3.9 and13.4.2–3 inputs remain explicit for the earlier
source assembly. No action-kernel, residual-section or R₁-placement
premise remains. The initial ordinary row is still required here.

Covered-row placement and exclusion, C₃ geometry and ambient fusion
remain with qt-d-1341-solvable-source. The earlier-source producers and
qt-d-1341-fixed-core-source retain their final discharge.
Source: Aschbacher–Smith13.4.8, printed pp.904–905.
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
theorem centralizer_pair_quotient_of_ordinary_baumann_original_R1
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hB : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
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
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
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
  have hR := firstFlagCore_eq_firstParabolicCore h structural D m e z hz hzL
  generalize hRa : firstFlagCore h structural D m = R at hB ⊢
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
  · let f := (firstParabolicAction h structural D m z.val).rangeRestrict.comp
      (inclusion (show (T : Subgroup G) ≤ firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
        from le_sup_right))
    have hRf : firstParabolicCore T L z.val =
        ((pCore 2 (firstParabolicAction h structural D m z.val).range).comap f).map
          (T : Subgroup G).subtype :=
      (firstActionCore_eq_firstParabolicCore h structural D m e hz).symm
    have hcore : IsPGroup 2 (centralCore L) := by
      rw [centralCore_eq_twoCore_of_ordinary e]
      exact pCore_isPGroup
    obtain ⟨horder,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hcore z hzL
    obtain ⟨_,_,hI,hr,hprod,hinter,_,hset⟩ :=
      centralizer_single_factor_source_product_of_baumann_bound h₀ h structural hz hzL
        f (firstParabolicCore T L z.val) hRf hQR hsolv hkernel hB hout hindex
        horder hthree hAN h1339' h1342
    have hq := centralizer_pair_quotient_of_source_product D m hcore z hzL hz
      (firstParabolicCore T L z.val) hRT hI hprod hinter hout
    have hu := centralizer_thompson_unique_of_source_product D m hcore z hzL hz
      (firstParabolicCore T L z.val) hRT hI hprod hinter hout
    exact ⟨hq,hI,hr,hprod,hinter,hset,hu⟩
  · have hsel : selectedFirstResidual T L V z.val = firstCentralizerResidual L z.val := by
      simp only [selectedFirstResidual,if_pos ordinary]
    have hres := (centralizer_kernel_residual_of_source1339 h₀ h structural D m z hz hzL
      hkernel (selectedFirstResidual T L V z.val) h1339).1.trans hsel
    obtain ⟨S,hS⟩ := firstParabolicCore_residual_sylow h₀ hz
      (fun he => hzL (he ▸ one_mem _)) hres
    exact centralizer_pair_quotient_of_ordinary_larger_kernel h₀ h structural D m ordinary
      z hz hzL (firstParabolicCore T L z.val) hRT S hS hres hB hsolv hout hindex h1339' h1342

/-- The ordinary source local product, combining both alternatives of13.2.2(7). -/
theorem centralizer_pair_quotient_of_ordinary_original_R1
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
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
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
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
  rcases hcase with hB | hb
  · exact centralizer_pair_quotient_of_ordinary_baumann_original_R1
      h₀ h structural D m ordinary z hz hzL hB hout h1339 hsolv hindex h1342
  · exact centralizer_pair_quotient_of_short_block_original_R1
      h₀ h structural D m hb z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
