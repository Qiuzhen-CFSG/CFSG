module
public import Theory.GroupTheory.RankOneInnerSplitting
public import Theory.GroupTheory.RankOneInnerCentralizer
/-!
# Cubics in the component intersection of an inner supplement

An inner-acting elementary-plane supplement to a centerless normal group
of three-rank one splits into its component and centralizing intersections.
When the ambient three-rank is at most two, its nontrivial normal
centralizing intersection has order three. The original elementary nine
therefore forces three to divide the component intersection's order.
The intrinsic two-core quotient and original plane are retained.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
The odd-degree PSL₃ application is in
Theory.SpecificGroups.PSL3.OddDegreeInnerSupplement.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {J : Type*} [Group J] [Finite J]

/-- An inner elementary-plane supplement has a cubic contribution inside
its centerless rank-one normal component. -/
theorem three_dvd_inner_supplement_intersection
    (A B T P : Subgroup J) [B.Normal]
    [IsElementaryAbelian 3 (A ⧸ pCore 2 A)] [IsElementaryAbelian 3 P]
    [(A ⊓ centralizer (B : Set J) : Subgroup J).Normal]
    (hzero : pCore 2 J = ⊥) (hz : center B = ⊥)
    (hr : primeRank 3 B = 1) (hJ : primeRank 3 J ≤ 2)
    (hinner : A ≤ B ⊔ centralizer (B : Set J))
    (hnA : T ≤ normalizer (A : Set J)) (hgen : B ⊔ A ⊔ T = ⊤)
    (hPA : P ≤ A) (hP : Nat.card P = 9) :
    3 ∣ Nat.card (A ⊓ B : Subgroup J) := by
  let C := A ⊓ centralizer (B : Set J)
  have hne : C ≠ ⊥ := by
    have hh := elementary_plane_inner_centralizer_ne_bot P B hP hz hr.le
      (hPA.trans hinner)
    intro hC
    exact hh (bot_unique ((inf_le_inf_right _ hPA).trans hC.le))
  let : IsElementaryAbelian 3 C := normal_elementary_of_core_quotient A C hzero inf_le_left
  have hC : Nat.card C = 3 := centralizing_elementary_card_prime B C hz hr hJ inf_le_right hne
  have hs : A = (A ⊓ B) ⊔ C := split_inner_supplement_of_elementary_core_quotient
    A B T hzero hz hr hJ hinner hnA hgen hne
  have hd : Disjoint (A ⊓ B) C := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hc : (⟨x,hx.1.2⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro b
      exact Subtype.ext (hx.2.2 b b.property)
    exact mem_bot.mpr (congrArg (fun b : B => b.val)
      (show (⟨x,hx.1.2⟩ : B) = 1 from mem_bot.mp (hz ▸ hc)))
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (A ⊓ B) C hd
    (inf_le_right.trans (le_centralizer_iff.mp
      (show C ≤ centralizer (B : Set J) from inf_le_right)))
  have h9 : 9 ∣ Nat.card A := hP ▸ card_dvd_of_le hPA
  rw [hs,←Nat.card_congr e.toEquiv,Nat.card_prod,hC] at h9
  exact (mul_dvd_mul_iff_right (by decide : (3:ℕ) ≠ 0)).mp h9
end Theory.GroupTheory
