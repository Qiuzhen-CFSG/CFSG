module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.UnitaryThree.SylowOrders
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.UnitaryThree.HallComplement
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# The PSU₃ Borel witness in E.6.11

Put q = 2^n. The model's matrix field has order q² and its stored
Hermitian conjugation is x ↦ x^q. The displacement [V,L ∩ M] is contained
in the actual Sylow center and both groups have order q, so they coincide.

For the complement, perfectness and the given nontrivial cyclic action
first show L ∩ M is proper. The rank-one overgroup theorem then places
it in the actual Sylow normalizer, whose order divides q³(q² − 1).
The action kernel has index q − 1. Cancelling this factor shows its order
divides q³(q + 1), coprime to q − 1. Schur–Zassenhaus constructs an
actual complement, and the supplied action isomorphism identifies that
complement with the cyclic group of order q − 1.

This constructs the model witness without additional local hypotheses.
Regularity remains the independent binary Singer argument in the parent.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
E.6.8(1) and E.6.11, printed pp.247,249–250; Huppert II.10.12.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
open UnitaryThree
open CFSG.Quasithin.ChapterF.Source
open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}

/-- In the PSU₃ case the displacement is the whole actual Sylow center. -/
theorem unitaryThree_center_eq_displacement
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype = ⁅V, L ⊓ M⁆ := by
  let e : S ≃* ↥(L ⊓ Q) :=
    ((S : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hS)
  have hc : Nat.card (center ↥(L ⊓ Q)) = 2 ^ n :=
    (Nat.card_congr (centerCongr e.symm).toEquiv).trans
      (sylow_center_card hmodel (by omega) S)
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (displacement_le_center h hU hL hVL hQ)
  rw [Subgroup.card_map_of_injective (L ⊓ Q).subtype_injective,
    hc, displacement_card h b hn]

/-- The actual Borel intersection satisfies the model normalizer order bound. -/
theorem unitaryThree_intersection_card_dvd
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n) (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    Nat.card (L ⊓ M : Subgroup G) ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
  have hQM : Q ≤ M := by rw [hQ]; exact inf_le_left.trans h.sylow_le
  have hSB : (S : Subgroup L) ≤ (L ⊓ M).subgroupOf L := by
    intro x hx
    have hh : (x : G) ∈ L ⊓ Q := hS ▸ Subgroup.mem_map_of_mem L.subtype hx
    exact ⟨x.property, hQM hh.2⟩
  have hBproper : (L ⊓ M).subgroupOf L < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hLM : L ≤ M := by
      intro x hx
      have hh : (⟨x, hx⟩ : L) ∈ (L ⊓ M).subgroupOf L := he ▸ Subgroup.mem_top _
      exact hh.2
    have hB : L ⊓ M = L := inf_eq_left.mpr hLM
    have hnorm : L ≤ normalizer (V : Set G) :=
      hB ▸ component_intersection_normalizes h hU hL.1
    let _ := component_quasisimple hL
    let e := (subgroupOfEquivOfLe hnorm).symm
    let _ : Group.IsPerfect (L.subgroupOf (normalizer (V : Set G))) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let _ : Group.IsPerfect (inducedAutomizer V L) := Group.IsPerfect.map _
    obtain ⟨a⟩ : Nonempty (inducedAutomizer V L ≃* Multiplicative (ZMod (2 ^ n - 1))) :=
      hB ▸ b.action
    let _ : Group.IsPerfect (Multiplicative (ZMod (2 ^ n - 1))) :=
      Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
    have hp : 4 ≤ 2 ^ n := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    let : NeZero (2 ^ n - 1) := ⟨by omega⟩
    have hc : Nat.card (Multiplicative (ZMod (2 ^ n - 1))) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hc
    omega
  have hs : RankOneSylowFacts S := by
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
    exact rankOneSylowFacts_of_equiv S e
      (rankOneSylowFacts_psu3 J n (by omega) hcard hconj _)
  have hd := Subgroup.card_dvd_of_le (hs.unique_maximal _ hSB hBproper)
  rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : L ⊓ M ≤ L)).toEquiv] at hd
  exact hd.trans (sylow_normalizer_card_dvd hmodel (by omega) S)

/-- The PSU₃ model supplies the complement and Sylow-center witness required by E.6.11. -/
theorem modelWitness_unitary_three
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ n)) : ModelWitness M V Q L n := by
  refine ⟨complement_of_order_bound h hU hL b (by omega)
    (unitaryThree_intersection_card_dvd h hU hL b hn hQ S hS hmodel), ?_⟩
  rw [unitaryThree_center_eq_displacement h hU hL b hn hVL hQ S hS hmodel]
  exact le_sup_right

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
