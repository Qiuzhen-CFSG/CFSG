module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The unique-offender Thompson and Baumann images

If every nontrivial image of a maximum elementary subgroup of R is A,
then J(R) has image A. The fixed subgroup C_V(A) lies in Ω₁(Z(J(R))):
it is elementary, lies in R, and centralizes J(R). Consequently Baum(R)
centralizes C_V(A). The pointwise-centralizer hypothesis of B.2.20 bounds
its image by A; the reverse inclusion follows from J(R) ≤ Baum(R).

The final theorem obtains the maximum-elementary image condition from
the genuine best-offender theorem. Its quotient map has exactly C_G(V)
as kernel. Only V ≤ R is needed from the stronger source containments
V ≤ O₂(G) ≤ R ≤ T; no replacement of the action kernel is made.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma B.2.20, printed p.82.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterB

variable {G H : Type*} [Group G] [Group H] [Finite G]

omit [Finite G] in
/-- The elementary Thompson subgroup centralizes its own omega-center. -/
theorem elementaryAbelianMaxJ_le_baumann (R : Subgroup G) :
    elementaryAbelianMaxJ R ≤ baumann R := by
  apply le_inf (sSup_le fun _ hB => hB.1)
  apply le_centralizer_iff.mpr
  intro x hx
  exact mem_centralizer_iff.mpr
    ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2

omit [Finite G] in
/-- Uniqueness in the actual maximum-elementary image family identifies J(R).
Nontriviality is needed: otherwise that family may be empty. -/
theorem thompson_image_of_unique_maximum_image (R : Subgroup G)
    (q : G →* H) (A : Subgroup H)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (hunique : ∀ B ∈ elementaryAbelianMaxSubgroups R,
      B.map q ≠ ⊥ → B.map q = A) :
    (elementaryAbelianMaxJ R).map q = A := by
  have hupper : elementaryAbelianMaxJ R ≤ A.comap q := by
    refine sSup_le fun B hB => map_le_iff_le_comap.mp ?_
    by_cases hbot : B.map q = ⊥
    · exact hbot ▸ bot_le
    · exact (hunique B hB hbot).le
  apply le_antisymm (map_le_iff_le_comap.mpr hupper)
  have hex : ∃ B ∈ elementaryAbelianMaxSubgroups R, B.map q ≠ ⊥ := by
    by_contra! hn
    exact hJ (sSup_le fun B hB => (map_eq_bot_iff B).mp (hn B hB))
  obtain ⟨B, hB, hne⟩ := hex
  rw [← hunique B hB hne]
  exact map_mono (le_sSup hB)

/-- B.2.20's group-theoretic argument, with the image-family condition
separated from the representation-theoretic offender calculation. -/
theorem thompson_baumann_image_of_unique_maximum_image
    (V R : Subgroup G) [IsElementaryAbelian 2 V]
    (q : G →* H) (A : Subgroup H) (hVR : V ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (hunique : ∀ B ∈ elementaryAbelianMaxSubgroups R,
      B.map q ≠ ⊥ → B.map q = A)
    (hfix : (R ⊓ centralizer
      (V ⊓ centralizer (A.comap q : Set G) : Set G)).map q ≤ A) :
    (elementaryAbelianMaxJ R).map q = A ∧ (baumann R).map q = A := by
  have hJA := thompson_image_of_unique_maximum_image R q A hJ hunique
  have hJA' : elementaryAbelianMaxJ R ≤ A.comap q :=
    map_le_iff_le_comap.mp hJA.le
  let E := V ⊓ centralizer (A.comap q : Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ V from inf_le_left)
  have hEalpha : E ≤ thompsonAlpha R :=
    elementary_centralizer_maxJ_le_omegaCenter R E (inf_le_left.trans hVR)
      (inf_le_right.trans (centralizer_le hJA'))
  refine ⟨hJA, le_antisymm ?_ ?_⟩
  · exact (map_mono (inf_le_inf_left R (centralizer_le hEalpha))).trans hfix
  · rw [← hJA]
    exact map_mono (elementaryAbelianMaxJ_le_baumann R)

variable [Finite H]

/-- Lemma B.2.20 for the literal faithful action quotient. The hypothesis
on the unique FF*-offender is tested on every elementary image in R*.
The centralizer expression is the image of the actual pointwise fixer,
so it retains the source's fixed-space convention. -/
theorem lemma_B_2_20 (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (A : Subgroup H) (hVR : V ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (hunique : ∀ E : Subgroup H, E ≤ R.map q →
      IsBestOffender (NormalElementaryQuotient.representation V q hq hker) E → E = A)
    (hfix : (R ⊓ centralizer
      (V ⊓ centralizer (A.comap q : Set G) : Set G)).map q = A) :
    (elementaryAbelianMaxJ R).map q = A ∧ (baumann R).map q = A := by
  apply thompson_baumann_image_of_unique_maximum_image V R q A hVR hJ _ hfix.le
  intro B hB hne
  exact hunique (B.map q) (map_mono hB.1)
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      V q hq hker R B hVR hB hne)

end CFSG.Quasithin.ChapterB
