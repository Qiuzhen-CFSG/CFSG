module

public import Theory.GroupTheory.ConjugateSpanKernel
public import Theory.GroupTheory.PResidual.PerfectCover
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.ReducedSource.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.SeedCommutator
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Quotient

public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The genuine Lᵥ restriction kernel

Put U = [W_K,K] and C = C_{Lᵥ}(U). The invariant component conclusions
make C normal in Lᵥ and normalized by Tᵥ. Source 13.6.11 makes C proper;
since Lᵥ is two-perfect and Lᵥ/O₂(Lᵥ) has order three, C is a two-group.
Sylow maximality in Gᵥ puts C in Tᵥ, so C fixes z. Normality in Lᵥ
propagates this to ⟨z^{Lᵥ}⟩, and W_K = ⟨z^{Lᵥ}⟩ ⊔ U completes
the kernel comparison.

The marked application derives both the cubic quotient and 13.6.11 movement
from the actual A₅ action. The final theorem supplies this comparison to
Basic.local_reduced_of_Lv_kernel for the literal restricted plus map.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the local
setup on p.926, 13.6.11–14 on pp.928–930, and 13.6.18 on p.931.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.ReducedSource
variable {G : Type*} [Group G] [Finite G]

/-- The cubic quotient and nontrivial U_K action give the restriction-kernel
comparison, before any Borel placement or containment Lᵥ ≤ K. -/
theorem Lv_kernel_comparison_of_moving (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ⁅⁅WK K L T z v, K⁆, Lv L v⁆ ≠ ⊥) :
    Lv L v ⊓ centralizer (⁅WK K L T z v, K⁆ : Subgroup G) ≤
      centralizer (WK K L T z v : Set G) := by
  let U := ⁅WK K L T z v, K⁆
  let C := Lv L v ⊓ centralizer (U : Set G)
  have hAU := plusActor_normalizes_moving K L T z v hL hz hK hnorm
  have hLU : Lv L v ≤ normalizer (U : Set G) :=
    (le_sup_right.trans le_sup_left).trans hAU
  have hTU : Tv T v ≤ normalizer (U : Set G) := le_sup_right.trans hAU
  have hLC : Lv L v ≤ normalizer (C : Set G) :=
    (le_inf (Lv L v).le_normalizer
      (hLU.trans (normalizer_le_normalizer_centralizer U))).trans
        inf_normalizer_le_normalizer_inf
  have hTC : Tv T v ≤ normalizer (C : Set G) :=
    (le_inf hL (hTU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hC : IsPGroup 2 C :=
    isPGroup_inf_centralizer_of_prime_core_quotient (Lv L v) U
      (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v))
      (by rw [hcard]; exact Nat.prime_three) hLU (by
        intro hc
        exact hmove (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)))
  obtain ⟨hpT, hTG, hmax⟩ := Chapter1.isSylowIn_iff.mp hSylow
  have hCT : C ≤ Tv T v := by
    have he := hmax (C ⊔ Tv T v) (hC.to_sup_of_normal_left' hpT hTC) le_sup_right
      (sup_le (inf_le_left.trans (Lv_le_Gv L v)) hTG)
    exact le_sup_left.trans he.le
  have hCz : C ≤ centralizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using hCT.trans hz
  have hWK : WK K L T z v = conjugateSpanBy (zpowers z) (K ⊔ Lv L v) := by
    rw [WK, Kminus_eq_of_invariant K T v hnorm]
  have hLU' : Lv L v ≤ normalizer
      (⁅conjugateSpanBy (zpowers z) (K ⊔ Lv L v), K⁆ : Subgroup G) := by
    rw [← hWK]
    exact hLU
  have h := le_centralizer_span_sup_of_kernel (zpowers z) K (Lv L v) C hLU' hLC hCz
    (by rw [← hWK]; exact inf_le_right)
  rwa [← hWK] at h

open A5Module

/-- Source application: the marked action supplies the cubic quotient,
and genuine 13.6.11 supplies movement on the literal U_K. -/
theorem Lv_kernel_comparison {L V : Subgroup G} (m : Marking L V) (K T : Subgroup G)
    (hk : m.action.ker = pCore 2 L)
    (hL : Tv T (markedV m) ≤ normalizer (Lv L (markedV m) : Set G))
    (hz : Tv T (markedV m) ≤ centralizer ({markedZ m} : Set G))
    (hK : K ∈ Yz L T (markedZ m) (markedV m))
    (hnorm : Tv T (markedV m) ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (markedV m)) (Gv (markedV m)))
    (hzOmega : markedZ m ∈ omegaOneCenterAmbient (Tv T (markedV m)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV m)) = pCore 2 (Gv (markedV m))) :
    Lv L (markedV m) ⊓ centralizer (⁅WK K L T (markedZ m) (markedV m), K⁆ : Subgroup G) ≤
      centralizer (WK K L T (markedZ m) (markedV m) : Set G) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv (markedV m))) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Uv (markedZ m) (markedV m)) :=
    IsElementaryAbelian.of_le (Uv_le_coreOmega T _ _ hSylow hzOmega hf)
  obtain ⟨hX, hUX⟩ := invariant_component_consequences K L T _ _ hK hnorm
  obtain ⟨S, hS⟩ := hSylow
  have hmove := (marked_Xz_commutators_ne_bot m T S hS hz hX).2
  rw [hUX] at hmove
  exact Lv_kernel_comparison_of_moving K L T _ _ hL hz hK hnorm ⟨S, hS⟩
    (residualQuotient_card m hk) hmove

open ComponentElimination.SourceTransferFields.RankOneBorel

/-- The actual KTᵥ action is reduced. The Lᵥ kernel premise of the earlier
adapter is discharged by the marked source action. -/
theorem local_reduced {L V : Subgroup G} (m : Marking L V) (K T : Subgroup G)
    (hk : m.action.ker = pCore 2 L)
    (hL : Tv T (markedV m) ≤ normalizer (Lv L (markedV m) : Set G))
    (hz : Tv T (markedV m) ≤ centralizer ({markedZ m} : Set G))
    (hK : K ∈ Yz L T (markedZ m) (markedV m))
    (hnorm : Tv T (markedV m) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T (markedZ m) (markedV m))]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T (markedZ m) (markedV m) hL hz)
      (movingSpace K L T (markedZ m) (markedV m)))
    (hzOmega : markedZ m ∈ omegaOneCenterAmbient (Tv T (markedV m)))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (markedV m)) (Gv (markedV m)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV m)) = pCore 2 (Gv (markedV m))) :
    pCore 2 (localMap K L T (markedZ m) (markedV m) hL hz).range = ⊥ :=
  local_reduced_of_Lv_kernel K L T _ _ hL hz hK hnorm hF hb s hzOmega hSylow hf
    (Lv_kernel_comparison m K T hk hL hz hK hnorm hSylow hzOmega hf)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.ReducedSource

end
