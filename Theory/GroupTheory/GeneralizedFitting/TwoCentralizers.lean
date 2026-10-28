module
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import FeitThompson.FinalTheorem

/-!
# Simple generalized Fitting groups from involution centralizers

When the two-core and odd core vanish, the Fitting subgroup vanishes.
Self-centralization of the generalized Fitting subgroup then supplies a
component. The odd-order theorem gives an involution in each component;
two distinct commuting components would put a perfect nontrivial subgroup
inside a two-group centralizer. Thus there is a unique component, and its
center lies in the trivial Fitting subgroup. It is the simple F*(G).

Source: the simple-socle reduction in Aschbacher--Smith E.2.7, printed p.220.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] [Nontrivial G]

/-- Trivial two-core and odd core, together with two-group involution
centralizers, force the actual generalized Fitting subgroup to be simple. -/
theorem simple_generalizedFitting_of_two_involution_centralizers
    (h2 : pCore 2 G = ⊥) (ho : pPrimeCore 2 G = ⊥)
    (hC : ∀ t : G, orderOf t = 2 → IsPGroup 2 (centralizer ({t} : Set G))) :
    IsSimpleGroup (generalizedFitting G) := by
  have hfit : fittingSubgroup G = ⊥ :=
    le_bot_iff.mp (ho ▸ fitting_le_pPrimeCore_of_pCore_eq_bot 2 h2)
  have hex : ∃ K : Subgroup G, IsComponent G K := by
    by_contra hn
    push Not at hn
    have hc := centralizer_core_product_le_of_no_components 2 hn
    rw [h2, ho, bot_sup_eq] at hc
    obtain ⟨g,hg⟩ := exists_ne (1 : G)
    apply hg
    apply hc
    intro x hx
    have hx1 : x = 1 := hx
    simp [hx1]
  obtain ⟨K,hK⟩ := hex
  have heven (D : Subgroup G) (hD : IsComponent G D) : Even (Nat.card D) := by
    apply Nat.not_odd_iff_even.mp
    intro hod
    let : IsQuasisimple D := hD.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact Group.IsPerfect.not_isSolvable D (_root_.odd_order_theorem D hod)
  have hu (D : Subgroup G) (hD : IsComponent G D) : D = K := by
    by_contra hne
    have hDK : D ≤ centralizer (K : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hK hne)
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
      (even_iff_two_dvd.mp (heven K hK))
    have hDt : D ≤ centralizer ({(t : G)} : Set G) :=
      hDK.trans (centralizer_le (Set.singleton_subset_iff.mpr t.property))
    have hpD : IsPGroup 2 D := (hC t ((orderOf_coe t).trans ht)).to_le hDt
    let : Group.IsNilpotent D := hpD.isNilpotent
    let : IsQuasisimple D := hD.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact Group.IsPerfect.not_isSolvable D inferInstance
  have hF : generalizedFitting G = K := by
    apply le_antisymm _ (component_le_generalizedFitting G K hK)
    rw [generalizedFitting, hfit, bot_sup_eq]
    exact sSup_le (fun D hD => (hu D hD).le)
  have hz : center K = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
    exact le_bot_iff.mp (hfit ▸ hK.center_map_le_fitting)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hs : IsSimpleGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  exact hF.symm ▸ hs
end Theory.GroupTheory
