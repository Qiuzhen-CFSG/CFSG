module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Inputs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# The original component quotient is simple and even

Apply the actual nonnormal C-component theorem inside M, and transport its
four-model list along the literal subgroup-of equivalence. Each model is
centerless, so the quasisimple quotient is simple, including the Suzuki row.
The odd-order theorem supplies evenness. This discharges the group-theoretic
premises of point generation; the remaining source action obligations concern
only the kernel and the nonfixed involution-fixed vector.
Source: Aschbacher--Smith 1.2.1(3), 10.1.1 and 10.2.12, pp.504,741,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem simple_of_linear {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] {q : ℕ} (h : ClassicalGroup.IsPSL Q 2 q) : IsSimpleGroup Q := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  have hz : center Q = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem simple_of_nonnormal_model {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] (h : NonnormalCComponentModel Q) : IsSimpleGroup Q := by
  cases h with
  | linear_even _ _ he => exact simple_of_linear he
  | linear_prime _ _ _ he => exact simple_of_linear he
  | janko he => exact he.some.isSimpleGroup
  | suzuki m hm he =>
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    exact he.some.isSimpleGroup

/-- Simplicity of the literal quotient, without a divisibility-by-three premise. -/
theorem quotient_simple
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsSimpleGroup (L ⧸ pCore 2 L) := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := fun ha =>
    hn ((le_normalizer_componentOrbit L T).trans
      ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨_,hm⟩ := (proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let e := subgroupOfEquivOfLe hLM
  let eqt := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eqt.symm
  let := simple_of_nonnormal_model hm
  exact eqt.symm.isSimpleGroup

/-- The original quasisimple quotient has even order. -/
theorem quotient_even (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    2 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let := D.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  exact IndexTwo.two_dvd_card_of_not_isSolvable
    (Group.IsPerfect.not_isSolvable (L ⧸ pCore 2 L))

/-- Only the two literal action facts remain after the source group theorem. -/
theorem actionInputs_of_kernel_and_nonfixed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (hkernel : commutatorPreimage L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) = L.pCoreIn 2)
    (hfixed : ∀ b ∈ D.maximalLocal,
      b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) → b ^ 2 = 1 →
      ¬ ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G)) :
    ActionInputs D :=
  ⟨quotient_simple D c.nonnormal,quotient_even D,hkernel,hfixed⟩

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
