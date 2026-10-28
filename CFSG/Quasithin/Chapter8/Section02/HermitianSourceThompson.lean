module
public import CFSG.Quasithin.ChapterE.Section05.RankCover
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import CFSG.Quasithin.ChapterE.Section06.Basic
public import Theory.Representation.HermitianTensorThree.NearOffenders

/-!
# Higher Thompson control for the Hermitian source

If an elementary generator A of J₁(X) moves V, compare the elementary
subgroup C_A(V)V with the largest elementary subgroups of X. The resulting
rank inequality makes Aut_A(V) an (F-1)-offender. The checked Hermitian
calculation forces half-degree one, image rank four and codimension five.
Thus J₁(X) fixes V for larger half-degrees, and J₁(C_M(U)) fixes V whenever
U has corank below 4n, including at half-degree one. Normality of V here is
only in the actual local centralizer, supplied by the E.6.1 TI hypothesis.

This discharges the higher Thompson premise in the source E.6.27 application.
The Chapter 12 extension applies it to the original chosen orbit and tensor
marking. The odd-element codimension bound and ambient odd-normalizer control
needed for r >= 4n remain with qt-d-1222-nonmathieu-hermitian-exclusion, as do
selection, the weak-closure bounds and the field-four exclusion. None of those
conclusions is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.2–7,
H.4.4–5 and the following alpha calculation, E.6.27 and 7.4.1,
printed pp.74–76,381–382,257,699–700 (refs/quasithin.pdf).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]
  (V X : Subgroup G) [IsElementaryAbelian 2 V]

private theorem corank_antitone {B C : Subgroup G} (hBC : B ≤ C) (hCV : C ≤ V) :
    subgroupCorank V C ≤ subgroupCorank V B := by
  have h := offender_corank_add hBC hCV
  omega

private theorem thompson_family_codim (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G))
    (A : Subgroup G) (hA : A ∈ thompsonFamily X 1) :
    fixedCodim (automizerRepresentation V) (inducedAutomizer V A) ≤
      rank (inducedAutomizer V A) + 1 := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let C := A ⊓ centralizer (V : Set G)
  have hbound := elementary_relativeIndex_le_of_thompsonFamily X A C V
    (i := 1) (j := rank (inducedAutomizer V A)) hA inf_le_left
    (by rw [rank_inducedAutomizer V A (hA.1.trans hXN)]; exact le_rfl)
    hVX inf_le_right
  have hVA : V ⊓ C ≤ V ⊓ centralizer (A : Set G) :=
    le_inf inf_le_left ((inf_le_right.trans inf_le_left).trans A.le_centralizer)
  have hsmall := corank_antitone V hVA inf_le_left
  rw [fixedCodim_inducedAutomizer V A (hA.1.trans hXN)]
  change subgroupCorank V (V ⊓ C) ≤ _ at hbound
  omega

variable (n : ℕ) [NeZero n]
  (e : Additive V ≃ₗ[ZMod 2] Space n)
  (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
  (he : ∀ a v, e (automizerRepresentation V a v) =
    overgroupAction n (binaryNormalizer n) (j a) (e v))

include hj he in
/-- Every moving elementary generator of J₁ has the exceptional field-four image. -/
theorem thompson_family_moving_image (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G))
    (A : Subgroup G) (hA : A ∈ thompsonFamily X 1)
    (hmove : ¬ A ≤ centralizer (V : Set G)) :
    n = 1 ∧ rank (inducedAutomizer V A) = 4 ∧
      fixedCodim (automizerRepresentation V) (inducedAutomizer V A) = 5 := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hAN := hA.1.trans hXN
  have hAI : IsElementaryTwo (inducedAutomizer V A) :=
    ⟨fun h => hmove ((inducedAutomizer_eq_bot_iff hAN).mp h),
      inducedAutomizer_elementary V A hAN⟩
  obtain ⟨hn,hr,hc,_⟩ := NearOffenders.of_equivariant n (automizerRepresentation V)
    j hj e he (inducedAutomizer V A) hAI (thompson_family_codim V X hVX hXN A hA)
  exact ⟨hn,hr,hc⟩

include hj he in
/-- Above half-degree one, no elementary generator of J₁ can move V. -/
theorem thompson_one_centralizes_of_one_lt (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G)) (hn : 1 < n) :
    thompsonJ X 1 ≤ centralizer (V : Set G) := by
  apply sSup_le
  intro A hA
  by_contra hmove
  have h := (thompson_family_moving_image V X n e j hj he hVX hXN A hA hmove).1
  omega

include hj he in
/-- A subgroup fixing a subspace of corank below five has no moving
J₁ generator, including in the field-four case. -/
theorem thompson_one_centralizes_of_small_corank (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hXU : X ≤ centralizer (U : Set G))
    (hc : subgroupCorank V U < 5) :
    thompsonJ X 1 ≤ centralizer (V : Set G) := by
  apply sSup_le
  intro A hA
  by_contra hmove
  have hcod := (thompson_family_moving_image V X n e j hj he hVX hXN A hA hmove).2.2
  rw [fixedCodim_inducedAutomizer V A (hA.1.trans hXN)] at hcod
  have hUA : U ≤ V ⊓ centralizer (A : Set G) :=
    le_inf hUV (le_centralizer_iff.mp (hA.1.trans hXU))
  have hsmall := corank_antitone V hUA inf_le_left
  omega

include hj he in
/-- The literal local-centralizer Thompson hypothesis of E.6.27 holds
for all subspaces of corank below 4n, without an odd-element assumption. -/
theorem localCentralizer_thompson_one
    {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hc : subgroupCorank V U < 4*n) :
    thompsonJ (M ⊓ centralizer (U : Set G)) 1 ≤ M ⊓ centralizer (V : Set G) := by
  have hVX := (h.normal_in_localCentralizer hU hUV).1
  have hXN := h.localCentralizer_le_normalizer hU hUV
  refine le_inf ((thompsonJ_le _ _).trans inf_le_left) ?_
  by_cases hn : 1 < n
  · exact thompson_one_centralizes_of_one_lt V _ n e j hj he hVX hXN hn
  · have hn1 : n = 1 := by have := NeZero.pos n; omega
    apply thompson_one_centralizes_of_small_corank V _ n e j hj he hVX hXN hUV inf_le_right
    omega

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
