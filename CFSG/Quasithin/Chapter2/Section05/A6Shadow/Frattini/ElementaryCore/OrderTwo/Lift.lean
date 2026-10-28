module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Geometry
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Actual involution witnesses for the contrary order-two branch

Source: Aschbacher–Smith, proof of Lemma 2.5.24, printed p.568.
A centralizing involution outside K S_C yields actual elementary groups of
order sixteen, contained in the indicated relative centralizers. The inner
four-group conjugator also conjugates the genuine local cores when their
relative-centralizer identities are supplied.

The witness is an explicit intermediate input. This module does not assert
its existence, equality of the constructed groups with the local cores, or
exhaustion of the largest elementary family. Those are the remaining fusion
and extension calculations in the contrary branch.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The actual centralizing involution required in the contrary branch.
Its construction from fusion is separate from the elementary-family calculation. -/
structure CentralizingInvolution (d : EarlierSetup κ G) where
  element : G
  mem_s : element ∈ d.S
  order_two : orderOf element = 2
  outside : element ∉ d.K ⊔ d.SC
  centralizes : element ∈ centralizer ((d.S ⊓ d.K : Subgroup G) : Set G)

/-- The candidate sixteen-group, retaining its actual generating involution. -/
def liftedFour (d : EarlierSetup κ G) (v : CentralizingInvolution d)
    (E : Subgroup G) : Subgroup G := d.SC ⊔ (E ⊔ zpowers v.element)

variable (d : EarlierSetup κ G)

theorem liftedFour_le_s (v : CentralizingInvolution d)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) : liftedFour d v E ≤ d.S :=
  sup_le d.sc_le_s (sup_le (hE.trans inf_le_left) (zpowers_le.mpr v.mem_s))

private theorem lift_centralizes_join (hcard : Nat.card d.SC = 2)
    (v : CentralizingInvolution d) (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) :
    v.element ∈ centralizer ((d.SC ⊔ E : Subgroup G) : Set G) := by
  have hC : d.SC ≤ centralizer ({v.element} : Set G) := by
    intro c hc
    exact mem_centralizer_singleton_iff.mpr
      (((core_le_center d hcard hc).2 v.element v.mem_s).symm)
  have hEC : E ≤ centralizer ({v.element} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (v.centralizes e (hE he))
  intro a ha
  exact mem_centralizer_singleton_iff.mp (sup_le hC hEC ha)

/-- A genuine centralizing involution outside K S_C gives elementary sixteen-groups. -/
theorem liftedFour_elementary_card (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 2) (v : CentralizingInvolution d)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    IsElementaryAbelian 2 (liftedFour d v E) ∧ Nat.card (liftedFour d v E) = 16 := by
  let : IsElementaryAbelian 2 (d.SC ⊔ E : Subgroup G) :=
    four_join_elementary d hEA E (hE.trans inf_le_right)
  let : IsElementaryAbelian 2 (zpowers v.element) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (v.order_two ▸ pow_orderOf_eq_one v.element)
  have hc := lift_centralizes_join d hcard v E hE
  have hn : zpowers v.element ≤ normalizer ((d.SC ⊔ E : Subgroup G) : Set G) :=
    (zpowers_le.mpr hc).trans (centralizer_le_normalizer _)
  have hout : v.element ∉ d.SC ⊔ E := by
    intro hv
    exact v.outside (sup_le le_sup_right ((hE.trans inf_le_right).trans le_sup_left) hv)
  have hd := (d.SC ⊔ E).disjoint_zpowers_of_prime_order_not_mem v.element v.order_two hout
  change IsElementaryAbelian 2 (d.SC ⊔ (E ⊔ zpowers v.element) : Subgroup G) ∧ _
  rw [← sup_assoc]
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hc), ?_⟩
  change Nat.card (d.SC ⊔ (E ⊔ zpowers v.element) : Subgroup G) = 16
  rw [← sup_assoc, card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,
    four_join_card d hcard E (hE.trans inf_le_right), Nat.card_zpowers, v.order_two]

/-- Each constructed sixteen-group lies in the relative centralizer used by the source. -/
theorem liftedFour_le_relativeCentralizer (v : CentralizingInvolution d)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    liftedFour d v E ≤ d.S ⊓ centralizer (E : Set G) := by
  refine le_inf (liftedFour_le_s d v E hE) ?_
  have hCC : d.SC ≤ centralizer (E : Set G) :=
    (d.centralizer_K ▸ inf_le_right).trans (centralizer_le (hE.trans inf_le_right))
  have hEC : E ≤ centralizer (E : Set G) := by
    let : IsMulCommutative E := IsKleinFour.isMulCommutative
    intro a ha b hb
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨b, hb⟩ : E) ⟨a, ha⟩)
  exact sup_le hCC (sup_le hEC
    (zpowers_le.mpr ((centralizer_le hE) v.centralizes)))

/-- The original S-conjugator of the inner four-groups also conjugates their genuine cores. -/
theorem localCore_conjugate
    (hcore : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      localCore d E = d.S ⊓ centralizer (E : Set G)) :
    ∃ s ∈ d.S, rightConjugate s (localCore d (fourZero d)) = localCore d (fourOne d) := by
  obtain ⟨s, hs, he⟩ := four_conjugate d
  have hsS : rightConjugate s d.S = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (d.S.le_normalizer (d.S.inv_mem hs))
  refine ⟨s, hs, ?_⟩
  rw [hcore _ (fourZero_le d) inferInstance, hcore _ (fourOne_le d) inferInstance,
    rightConjugate_relativeCentralizer, hsS, he]

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
