module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical
public import CFSG.Quasithin.ChapterA.Section01.Coprime
public import CFSG.Quasithin.ChapterA.Section01.RankActions.IrreducibleActions

/-!
# Source inputs for the Ξ supercritical reduction

The proved A.1.21 supplies supercritical existence, coprime automorphism
detection and rank detection. Pointwise fixation of a supercritical subgroup
induces the identity on its Frattini quotient; faithful restriction of the
cyclic coprime actor therefore makes the original automorphism trivial.
A.1.32 supplies the two rank-two action implications on the same literal
Frattini quotient and normalizer action used by the Ξ reduction.

The final application discharges all four universal earlier-result premises
of `LocalInput.quotient_normal_or_fitting`. Its normal-or-Fitting alternative
concerns the actual image of the complement in H/O₂(H), retaining the original
local input and strong quasithinness hypotheses. It does not use A.1.17's
invalid general direct-sum assertion or assert the later component-containment
alternatives of Proposition 1.3.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.1.21 on
printed pp.24–25, A.1.32 on pp.28–29, and the proof of Proposition 1.3.4
on pp.509–510.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u

/-- A.1.21(1) supplies the universal supercritical existence input. -/
theorem source_supercriticalExistence : SupercriticalExistence.{u} := by
  intro r _ hr Y _ _ hY
  exact ChapterA.lemma_A_1_21_1 hY hr

/-- A.1.21(3) detects an automorphism fixing the supercritical subgroup
pointwise by its faithful cyclic action on the Frattini quotient. -/
theorem source_supercriticalCoprimeDetection : SupercriticalCoprimeDetection.{u} := by
  intro r _ hr Y _ _ hY D hD a hcop hfix
  let : D.Characteristic := hD.characteristic
  have hrestrict : MulAut.characteristic D a = 1 := by
    ext d
    exact hfix d
  have hinj := ChapterA.lemma_A_1_21_3 hD hY hr a hcop.symm
  have he : (⟨a, mem_zpowers a⟩ : zpowers a) = 1 := by
    apply hinj
    change Subgroup.quotientAut (frattini D) (MulAut.characteristic D a) =
      Subgroup.quotientAut (frattini D) (MulAut.characteristic D 1)
    simp only [hrestrict, map_one]
  exact congrArg Subtype.val he

/-- A.1.21(4) supplies the universal supercritical rank input. -/
theorem source_supercriticalRankDetection : SupercriticalRankDetection.{u} := by
  intro r _ hr Y _ _ hY D hD hrank
  exact ChapterA.lemma_A_1_21_4 hD hY hr hrank

/-- The proved A.1.32 consequences match the actual normalizer action in
the Ξ input, including the required nontriviality premise in the equal-prime case. -/
theorem source_rankTwoActionImplications : RankTwoActionImplications.{u} := by
  intro r p _ _ hr hp Y _ _ R P hnormal hR hoR hcR hmR hP hoP hcP hmP hirr
  let : R.Normal := hnormal
  exact ChapterA.IrreducibleActions.action_implications hr hp R P
    hR hoR hcR hmR hP hoP hcP hmP hirr

/-- The three supercritical inputs are discharged while retaining A.1.32
as an explicit earlier-result interface. -/
theorem LocalInput.quotient_normal_or_fitting_of_rankTwoAction
    {G : Type u} [Group G] [Finite G]
    (hA132 : RankTwoActionImplications.{u})
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) :
    (quotientImage H P).Normal ∨ FittingConditions p P H :=
  h.quotient_normal_or_fitting source_supercriticalExistence
    source_supercriticalCoprimeDetection source_supercriticalRankDetection hA132 hH

/-- The actual Ξ supercritical/Fitting alternative follows from the proved
A.1.21 and A.1.32, with no universal earlier-result premises remaining. -/
theorem LocalInput.quotient_normal_or_fitting_of_source
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) :
    (quotientImage H P).Normal ∨ FittingConditions p P H :=
  h.quotient_normal_or_fitting_of_rankTwoAction source_rankTwoActionImplications hH

end CFSG.Quasithin.Chapter1.XiEmbedding
