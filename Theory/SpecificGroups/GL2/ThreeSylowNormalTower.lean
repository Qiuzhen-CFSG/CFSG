module
public import Theory.SpecificGroups.GL2.ThreeSylowNormalElementary
public import Theory.GroupTheory.SemidihedralNormalTower

/-!
# A two-step normal involution in the affine-nine Sylow

In a two-core-free group of order 144 with a normal elementary nine-group,
an order-two subgroup normal in a normal subgroup of a Sylow two-subgroup
lies in the Sylow Frattini subgroup. It lies in the omega-center of the
intermediate subgroup, which is normal elementary in the Sylow; the existing
GL₂(3) calculation then puts it in Frattini. The ambient version preserves
the literal subgroup inclusions used by DGS 8.1(g), printed p.133.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

/-- A two-step normal subgroup of order two lies in the Sylow Frattini subgroup. -/
theorem two_step_normal_order_two_le_frattini_of_normal_nine
    {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 144)
    (N : Subgroup K) [N.Normal] [IsElementaryAbelian 3 N]
    (hN : Nat.card N = 9) (hcore : pCore 2 K = ⊥)
    (S : Sylow 2 K) (A E : Subgroup S) [A.Normal]
    (hEA : E ≤ A) [(E.subgroupOf A).Normal] (hE : Nat.card E = 2) :
    E ≤ frattini S := by
  let C := omegaCenterIn A
  have hsubcard : Nat.card (E.subgroupOf A) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv).trans hE
  have hcentral := central_of_normal_card_two (E.subgroupOf A) hsubcard
  have hEC : E ≤ C := by
    intro x hx
    apply (mem_omegaCenterIn_iff A x).mpr
    refine ⟨hEA hx,?_,?_⟩
    · intro a ha
      exact congrArg Subtype.val (mem_center_iff.mp (hcentral
        (show (⟨x,hEA hx⟩ : A) ∈ E.subgroupOf A from hx)) ⟨a,ha⟩)
    · have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : E))
      rw [hE] at hh
      exact congrArg Subtype.val hh
  let : C.Normal := ⟨by
    intro x hx g
    exact le_normalizer_iff.mp (normalizer_le_normalizer_omegaCenterIn A) g
      (by rw [A.normalizer_eq_top]; trivial) x hx⟩
  exact hEC.trans (normal_elementary_le_frattini_of_normal_nine hK N hN hcore S C)
/-- The same result for the original ambient subgroups and their normality tower. -/
theorem ambient_two_step_normal_order_two_le_frattini_of_normal_nine
    {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 144)
    (N : Subgroup K) [N.Normal] [IsElementaryAbelian 3 N]
    (hN : Nat.card N = 9) (hcore : pCore 2 K = ⊥)
    (S : Sylow 2 K) (A E : Subgroup K)
    (hEA : E ≤ A) (hAS : A ≤ S)
    [(E.subgroupOf A).Normal] [(A.subgroupOf (S : Subgroup K)).Normal]
    (hE : Nat.card E = 2) :
    E.subgroupOf (S : Subgroup K) ≤ frattini S := by
  let A' := A.subgroupOf (S : Subgroup K)
  let E' := E.subgroupOf (S : Subgroup K)
  have hAE : A ≤ normalizer (E : Set K) :=
    (normal_subgroupOf_iff_le_normalizer hEA).mp inferInstance
  have hAE' : A' ≤ normalizer (E' : Set S) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    exact le_normalizer_iff.mp hAE a ha x hx
  let : (E'.subgroupOf A').Normal := normal_subgroupOf_of_le_normalizer hAE'
  exact two_step_normal_order_two_le_frattini_of_normal_nine hK N hN hcore S A' E'
    (comap_mono hEA) ((Nat.card_congr (subgroupOfEquivOfLe (hEA.trans hAS)).toEquiv).trans hE)

end Theory.GroupTheory
