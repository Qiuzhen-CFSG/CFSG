module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OrdinaryRow

/-!
# Row selection and the pair quotient in the Baumann-bound branch

The core marking first supplies the order premises for the literal L₁
in either covering row. Its proved three-rank-one bound then selects
L/O₂(L) ≅ A₆. Only afterwards do the ordinary earlier-source inputs
identify the residual in M and give the product H=L₁IT and the actual
quotient H/O₂(H) ≅ S₃ × S₃. The row is a conclusion of this endpoint.

This remains the two-core-kernel, Baumann-bound branch with L₁ normalizing
the specified R₁. The source covered-row argument initially supplies only
L₁,+ normalization, and is still needed for the unrestricted case.
R₁ placement, A₆-block noncentrality, the larger action kernel, IT uniqueness,
the chamber and the remaining involution-orbit conclusions stay with
qt-d-1341-solvable-source. The explicit earlier Chapter12/13.3 and
13.4.2–7 inputs retain discharge with qt-d-1341-fixed-core-source and its
earlier-source producers. This does not establish full 13.4.8–9.

Source: Aschbacher–Smith, 13.4.8 and the opening of 13.4.9,
printed pp.904–906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 BinaryNaturalDual.VectorStabilizers Stellmacher
open Chapter14.Section03.FaithfulSource Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the two-core-kernel and Baumann-bound branch, rank selects the ordinary row
before the literal local product and pair quotient are constructed. -/
theorem centralizer_ordinary_pair_quotient_of_baumann_bound
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (v : V) (hz : v.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : v.val ∉ centralizer (L : Set G))
    {K : Type*} [Group K] (f : T →* K) (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hQR : (centralizer ({v.val} : Set G)).pCoreIn 2 ≤ R)
    (hsolv : Group.IsSolvable (centralizer ({v.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T v.val).subgroupOf
      (centralizer ({v.val} : Set G)) : Set (centralizer ({v.val} : Set G))) =
      pCore 2 (centralizer ({v.val} : Set G)))
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hAN : firstCentralizerResidual L v.val ≤ normalizer (R : Set G))
    (h1339 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      ∀ Y : Subgroup G, Y ≤ centralizer ({v.val} : Set G) →
      centralizer ({v.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({v.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      primeRank 3 (firstCentralizerResidual L v.val) = 1 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T v.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L v.val ⊔ I ⊔ (T : Subgroup G) := by
  let := h.quasisimple
  obtain ⟨horder,hthree⟩ := firstCentralizerResidual_order_of_marking D m v hzL
  have hr := centralizer_firstResidual_threeRank_of_baumann_bound h₀ hz
    (fun he => hzL (he ▸ one_mem _)) f R hR hQR hsolv hkernel hB hout horder hthree hAN
  have ordinary := ordinary_of_firstCentralizerResidual_threeRank D m v hzL hr.le
  exact ⟨ordinary,hr,centralizer_pair_quotient_of_baumann_bound h₀ h structural D m ordinary v
    hz hzL f R hR hQR hsolv hkernel hB hout hindex hAN (h1339 ordinary) (h1342 ordinary)⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
