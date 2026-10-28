module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.LargerShortBlock
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.ShortBlock
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.ShortConjugates
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstParabolicCore
public import Theory.GroupTheory.PResidual.SectionSylow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerShortBlock

/-!
# The first parabolic core in both short-block kernel cases: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/FirstParabolicCore` proof for the local step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Both short-block kernel cases for the fixed first-parabolic core. -/
theorem centralizer_pair_quotient_of_short_block_firstParabolicCore_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstParabolicCore T L z.val))
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
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstParabolicCore T L z.val)) H
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
  let R := firstParabolicCore T L z.val
  obtain ⟨hRT,hnR,hAN,hQR⟩ := firstParabolicCore_local_data (L := L) hz
  by_cases hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G))
  · have h1339' : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
        centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
        Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
        Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3 := by
      intro Y hYH hn hYM hp
      exact (h1339 Y hYH hn hYM hp).imp_right (fun hh => hh.2)
    obtain ⟨hq,hI,hr,hprod,hinter,hset⟩ := centralizer_pair_quotient_of_short_block_at
      h₀ h structural D m hb z hz hzL R hRT hnR hQR hVJ hsolv hkernel hout hindex
      hAN h1339' h1342
    have hcore : IsPGroup 2 (centralCore L) := by
      rw [centralCore_eq_twoCore_of_short_core_marking D m hb]
      exact pCore_isPGroup
    have hu := centralizer_thompson_unique_of_source_product D m hcore z hzL hz R hRT
      hI hprod hinter hout
    exact ⟨ordinary_of_short_core_marking D m hb,hq,hI,hr,hprod,hinter,hset,hu⟩
  · have hres := (centralizer_short_block_residual_normal_of_source1339_at
      h₀ h structural D m hb z hz hzL hkernel h1339).1
    obtain ⟨S,hS⟩ := firstParabolicCore_residual_sylow h₀ hz
      (fun he => hzL (he ▸ one_mem _)) hres
    exact centralizer_pair_quotient_of_larger_short_block_at h₀ h structural D m hb z hz hzL
      hkernel R hRT S hS hVJ hout hfusion h1339 hsolv hindex h1342

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
