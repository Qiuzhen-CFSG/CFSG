module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.CoreObstruction
public import Theory.GroupTheory.IndexTwoIntersectionLine

/-!
# The common-core containment also fails

Write `D = T_E`, `A = O₂(G₁)`, `B = O₂(G₂)` and `R = C_T(V)`.
The source local indices are `[D:A]=[D:B]=2` and `[D:R]=4`, with
`R ≤ A`. The earlier cubic quotient and Thompson commutator give
`R ≰ B`, as proved in `LocalRelations.CoreObstruction`.

Then `[A:A ∩ B]=[A:R]=2`. If `A ∩ B ≤ R`, multiplication of relative
indices forces `R = A ∩ B`, contradicting `R ≰ B`. Since `A ≤ T`,
this also refutes `A ∩ B ≤ C_G(V)`. All cores are the intrinsic cores
of the published amalgam constructions; no ambient normality is assumed.

This is a diagnostic for the proof on printed p.1154, not a refutation
of Lemma 15.3.68(2). Its two-core `O₂(G₀)` is a smaller subgroup with
additional normality, and still requires a separate centrality argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66–68, printed pp.1152–1154, PDF pp.1169–1171.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality
variable {G : Type*} [Group G]

private theorem crossing_common_not_le (D A B R : Subgroup G)
    (hAD : A ≤ D) (hRA : R ≤ A) (hRB : ¬ R ≤ B)
    (hAi : A.relIndex D = 2) (hBi : B.relIndex D = 2) (hRi : R.relIndex D = 4) :
    ¬ A ⊓ B ≤ R := by
  have hBA : B.relIndex A = 2 := by
    have hi := intersection_relIndex_eq_two_of_not_le D A B A hAD le_rfl
      (fun h => hRB (hRA.trans h)) hBi
    simpa only [inf_eq_right.mpr hAD, inf_relIndex_left] using hi
  have hRAi : R.relIndex A = 2 := by
    have hm := relIndex_mul_relIndex R A D hRA hAD
    rw [hAi,hRi] at hm
    omega
  intro hle
  have hKi : (A ⊓ B).relIndex A = 2 := by simpa only [inf_relIndex_left] using hBA
  have hm := relIndex_mul_relIndex (A ⊓ B) R A hle hRA
  rw [hRAi,hKi] at hm
  have hRK : R ≤ A ⊓ B := relIndex_eq_one.mp (by omega)
  exact hRB (hRK.trans inf_le_right)

/-- With the genuine local indices, even containment of the common core
in the module centralizer contradicts 15.3.67(3),(4). -/
theorem commonCore_not_le_centralizer (Y T V E F : Subgroup G)
    (hT₁ : IsSylowSubgroupIn (lineT T E) (firstAmalgamGroup Y T E F))
    (hR₁ : T ⊓ centralizer (V : Set G) ≤ twoCoreAmbient (firstAmalgamGroup Y T E F))
    (hRindex : (T ⊓ centralizer (V : Set G)).relIndex (lineT T E) = 4)
    (hQ₁index : (twoCoreAmbient (firstAmalgamGroup Y T E F)).relIndex (lineT T E) = 2)
    (hQ₂index : (twoCoreAmbient (secondAmalgamGroup T E)).relIndex (lineT T E) = 2)
    (hquot : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)))
    (hcomm : lineX E = ⁅lineX E, elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))⁆) :
    ¬ twoCoreAmbient (firstAmalgamGroup Y T E F) ⊓
      twoCoreAmbient (secondAmalgamGroup T E) ≤ centralizer (V : Set G) := by
  obtain ⟨S,hS⟩ := hT₁
  have hQ₁T : twoCoreAmbient (firstAmalgamGroup Y T E F) ≤ lineT T E := by
    rw [← hS]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S)
  have hn := crossing_common_not_le (lineT T E)
    (twoCoreAmbient (firstAmalgamGroup Y T E F))
    (twoCoreAmbient (secondAmalgamGroup T E)) (T ⊓ centralizer (V : Set G))
    hQ₁T hR₁ (LocalRelations.centralizer_not_le_secondCore T V E hquot hcomm)
    hQ₁index hQ₂index hRindex
  intro hC
  exact hn (le_inf (inf_le_left.trans (hQ₁T.trans inf_le_left)) hC)


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality
