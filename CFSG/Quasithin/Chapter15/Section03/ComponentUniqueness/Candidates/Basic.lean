module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Components

/-!
# Intermediate groups in the component argument

Every subgroup between the common Sylow subgroup `S` and an outside
member `I` contains `O₂(I)` in its own two-core. In particular the group
`L₁Y₊S` in 15.3.33(1) has nontrivial two-core. Establishing its
characteristic-two property is a separate obligation before 15.3.25 can
be applied.

`componentPart` and `centralizingPart` retain the actual two-residuals
in 15.3.37. The section-centralizer version in 15.3.12 is named
separately; identifying it with the ordinary centralizer requires proof.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
printed pp.1134--1135 and 1124--1125.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G]

/-- `Y_L = O²(Y₊ ∩ L)`. -/
noncomputable abbrev componentPart (Yplus L : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Yplus ⊓ L)

/-- The ordinary-centralizer residual used in 15.3.37. -/
noncomputable abbrev centralizingPart (Yplus L : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Yplus ⊓ centralizer (L : Set G))

/-- The section-centralizer residual used in 15.3.12. -/
noncomputable abbrev sectionCentralizingPart (Yplus L : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Chapter4.sectionCentralizerIn Yplus L)

/-- Intermediate overgroups of the common Sylow subgroup have nontrivial two-core. -/
theorem outside_intermediate_twoCore_ne_bot
    {Yplus S M I J : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hSJ : S ≤ J) (hJI : J ≤ I) : J.pCoreIn 2 ≠ ⊥ := by
  obtain ⟨P, hP⟩ := hSylow I hI
  have hcoreJ : I.pCoreIn 2 ≤ J :=
    (pCoreIn_le_sylow I P).trans (hP.symm ▸ hSJ)
  have hJN : J ≤ normalizer (I.pCoreIn 2 : Set G) :=
    hJI.trans (I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hcore : I.pCoreIn 2 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) hcoreJ hJN
  intro hJ
  exact hI.1.1 (le_bot_iff.mp (hJ ▸ hcore))

/-- The generated group used in 15.3.33(1) belongs to H if it is outside M. -/
theorem component_extension_mem_outsideFamily
    {Yplus S M I L₁ : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hL : L₁ ≤ I) (hLM : ¬ L₁ ≤ M) :
    L₁ ⊔ (Yplus ⊔ S) ∈ outsideFamily Yplus S M := by
  refine ⟨⟨outside_intermediate_twoCore_ne_bot hI hSylow
    (le_sup_right.trans le_sup_right) (sup_le hL hI.1.2), (show Yplus ⊔ S ≤ L₁ ⊔ (Yplus ⊔ S) from le_sup_right)⟩, ?_⟩
  exact fun h => hLM (le_sup_left.trans h)

end CFSG.Quasithin.Chapter15.Section03
