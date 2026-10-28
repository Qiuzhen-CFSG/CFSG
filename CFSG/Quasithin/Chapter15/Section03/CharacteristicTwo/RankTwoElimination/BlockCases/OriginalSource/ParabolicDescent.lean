module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Reduction
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The proper-overgroup induction step of 15.3.20

Two invariant proper parabolics containing the supplement intersection give
proper intermediate overgroups. Original-source characteristic-two inheritance
and induction put both parabolics in M, contradicting their generation of L.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G]

/-- A normalized product introduces no new component elements when its
supplement's component intersection already lies in the first factor. -/
theorem parabolic_product_intersection {L P A : Subgroup G}
    (hP : P ≤ L) (hn : A ≤ normalizer (P : Set G)) (hi : A ⊓ L ≤ P) :
    (P ⊔ A) ⊓ L = P := by
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (P : Set G) * (A : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left P A hn]
      exact hx.1
    obtain ⟨p,hp,a,ha,rfl⟩ := hxprod
    have haL : a ∈ L := by
      simpa only [inv_mul_cancel_left] using L.mul_mem (L.inv_mem (hP hp)) hx.2
    exact P.mul_mem hp (hi ⟨ha,haL⟩)
  · exact le_inf le_sup_left hP

variable [Finite G]

/-- The two-parabolic step of 15.3.20 under proper-overgroup induction.
The candidates are the literal joins P(Y₊S); strictness follows from their
actual intersection with L, without a numerical index hypothesis. -/
theorem source_15_3_20_of_generating_parabolics
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    (P Q : Subgroup G) (hP : P < c.L) (hQ : Q < c.L)
    (hgen : P ⊔ Q = c.L)
    (hnP : d.Yplus ⊔ d.S ≤ normalizer (P : Set G))
    (hnQ : d.Yplus ⊔ d.S ≤ normalizer (Q : Set G))
    (hbase : (d.Yplus ⊔ d.S) ⊓ c.L ≤ P ⊓ Q) : False := by
  have hcontrol (D : Subgroup G) (hD : D < c.L)
      (hn : d.Yplus ⊔ d.S ≤ normalizer (D : Set G))
      (hi : (d.Yplus ⊔ d.S) ⊓ c.L ≤ D) : D ≤ d.M := by
    by_contra hDM
    let J := D ⊔ (d.Yplus ⊔ d.S)
    have hJI : J ≤ I := sup_le (hD.le.trans (component_le c)) hI.1.2
    have hJL : J ⊓ c.L = D := parabolic_product_intersection hD.le hn hi
    have hJlt : J < I := lt_of_le_of_ne hJI (by
      intro he
      have hLJ : c.L ≤ J := he ▸ component_le c
      have hLD : c.L ≤ D := hJL ▸ le_inf hLJ le_rfl
      exact hD.not_ge hLD)
    obtain ⟨hJ,_,hfJ⟩ := LinearFourFive.intermediate_outside d hI hS hf hJI
      le_sup_right (fun h => hDM (le_sup_left.trans h))
    exact hproper J hJlt hJ hfJ
  exact c.outside (hgen ▸ sup_le (hcontrol P hP hnP (hbase.trans inf_le_left))
    (hcontrol Q hQ hnQ (hbase.trans inf_le_right)))
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
