module
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# An involution normal through two steps in SD16 is central

An order-two subgroup E normal in N is central in N, hence lies in
Omega_1(Z(N)). If N is normal in the semidihedral group of order sixteen,
that omega-center is normal and elementary. The presentation calculation
identifying every nontrivial normal elementary subgroup therefore places
E in the center. The ambient-subgroup version retains both original
normalizer relations and the marked semidihedral generators.

Source: the semidihedral presentation in Alperin--Brauer--Gorenstein,
Chapter II, section 1. Applied to the literal terminal quotient tower in
DGS 8.1(g) by `CommutingNontrivial.PredecessorNormality`.
-/

public noncomputable section
open Subgroup
namespace Semidihedral
variable {G : Type*} [Group G]

/-- An order-two subgroup normal in a normal subgroup of SD16 is central. -/
theorem two_step_normal_order_two_le_center_sixteen (a b : G)
    (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hc : b*a*b⁻¹ = a^3) (hg : closure ({a,b} : Set G) = ⊤)
    (N E : Subgroup G) [N.Normal] (hEN : E ≤ N)
    [(E.subgroupOf N).Normal] (hE : Nat.card E = 2) : E ≤ center G := by
  let C := omegaCenterIn N
  have hsubcard : Nat.card (E.subgroupOf N) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hE
  have hcentral := central_of_normal_card_two (E.subgroupOf N) hsubcard
  have hEC : E ≤ C := by
    intro x hx
    apply (mem_omegaCenterIn_iff N x).mpr
    refine ⟨hEN hx,?_,?_⟩
    · intro n hn
      exact congrArg Subtype.val (mem_center_iff.mp (hcentral (show (⟨x,hEN hx⟩ : N) ∈ E.subgroupOf N from hx)) ⟨n,hn⟩)
    · have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : E))
      rw [hE] at hh
      exact congrArg Subtype.val hh
  let : C.Normal := ⟨by
    intro x hx g
    exact le_normalizer_iff.mp (normalizer_le_normalizer_omegaCenterIn N) g
      (by rw [N.normalizer_eq_top]; trivial) x hx⟩
  have hC : C ≠ ⊥ := by
    intro he
    have he' : E = ⊥ := bot_unique (hEC.trans he.le)
    rw [he',card_bot] at hE
    omega
  have he := normal_elementary_eq_of_order_sixteen a b ha hb hc hg C hC
  have hz : center G = zpowers (a^4) := center_eq (n := 4) (by decide) a b ha hb hc hg
  rw [hz,←he]
  exact hEC

/-- The same centrality criterion inside a marked ambient subgroup. -/
theorem two_step_normal_order_two_centralizes_sixteen (S A E : Subgroup G)
    (hEA : E ≤ A) (hAS : A ≤ S)
    (hAE : A ≤ normalizer (E : Set G)) (hSA : S ≤ normalizer (A : Set G))
    (a b : S) (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hc : b*a*b⁻¹ = a^3) (hg : closure ({a,b} : Set S) = ⊤)
    (hE : Nat.card E = 2) : E ≤ centralizer (S : Set G) := by
  let N := A.subgroupOf S
  let T := E.subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer hSA
  have hTN : T ≤ N := comap_mono hEA
  have hNT : N ≤ normalizer (T : Set S) := by
    apply le_normalizer_iff.mpr
    intro n hn t ht
    exact le_normalizer_iff.mp hAE n hn t ht
  let : (T.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNT
  have hcard : Nat.card T = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hEA.trans hAS)).toEquiv).trans hE
  have hz := two_step_normal_order_two_le_center_sixteen a b ha hb hc hg N T hTN hcard
  intro x hx s hs
  exact congrArg Subtype.val (mem_center_iff.mp
    (hz (show (⟨x,hAS (hEA hx)⟩ : S) ∈ T from hx)) ⟨s,hs⟩)

end Semidihedral
