module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.Geometry
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The local centralizer has order forty-eight

The action of C = C_{⟨Q,Qᵍ⟩}(t) on V has kernel E: C centralizes t,
E = V⟨t⟩, and C_G(E) = E. Hence |C| divides 8·|Aut(V)| = 48.
Both C_Q(t) and C_{Qᵍ}(t) have order at least sixteen and their intersection
is E. The first therefore has order sixteen, forcing |C| to be 16 or 48.
The second rules out 16, since it cannot fit into E of order eight.
This proves the local order directly, without the general amalgam theorem
cited as 8.15 in the source and without an ambient order assumption.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.1(2), pp.38–39.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {z : G}

public theorem four_elementary (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) : IsElementaryAbelian 2 (four z t a.g) := by
  let : IsElementaryAbelian 2 (eight z t a.g) := eight_elementary h a htE
  exact {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun q : eight z t a.g => (q : localCentralizer z t a.g))
      (mul_comm (⟨x, four_le_eight z t a.g x.property⟩ : eight z t a.g)
        ⟨y, four_le_eight z t a.g y.property⟩))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := eight z t a.g) x
        (four_le_eight z t a.g x.property))) }

public theorem four_centralizer (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    centralizer (four z t a.g : Set (localCentralizer z t a.g)) = eight z t a.g := by
  let : IsElementaryAbelian 2 (eight z t a.g) := eight_elementary h a htE
  apply le_antisymm ?_ ((eight z t a.g).le_centralizer.trans
    (centralizer_le (by exact four_le_eight z t a.g)))
  intro x hx
  rw [← eight_self_centralizing h a htE]
  have hj : eight z t a.g ≤ centralizer ({x} : Set (localCentralizer z t a.g)) := by
    rw [eight_eq_four_sup_central h d a htE ht hnt]
    apply sup_le
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (hx v hv)
    · exact zpowers_le.mpr (center_le_centralizer _ (centralElement_mem_center h a htE))
  intro e he
  exact mem_centralizer_singleton_iff.mp (hj he)

@[expose] public def fourAction (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (t : G) : localCentralizer z t a.g →* MulAut (four z t a.g) := by
  let : (four z t a.g).Normal := four_normal h d a t
  exact MulAut.conjNormal

public theorem fourAction_ker (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    (fourAction h d a t).ker = eight z t a.g :=
by
  rw [← four_centralizer h d a htE ht hnt]
  ext x
  constructor
  · intro hx v hv
    have he := congrArg (fun k : MulAut (four z t a.g) => (k ⟨v, hv⟩ : localCentralizer z t a.g)) hx
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx v v.property).symm

public theorem local_card_dvd (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) : Nat.card (localCentralizer z t a.g) ∣ 48 := by
  let : IsElementaryAbelian 2 (four z t a.g) := four_elementary h a htE
  let : Nontrivial (four z t a.g) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [four_card h d a htE]; decide)
  let : IsKleinFour (four z t a.g) :=
    ⟨four_card h d a htE, IsElementaryAbelian.exponent_eq_prime⟩
  let f := fourAction h d a t
  have hd : Nat.card f.range ∣ 6 := IsKleinFour.card_mulAut (four z t a.g) ▸ f.range.card_subgroup_dvd_card
  have hc := f.ker.card_mul_index
  rw [index_ker, fourAction_ker h d a htE ht hnt, eight_card h a htE] at hc
  rw [← hc]
  exact Nat.mul_dvd_mul_left 8 hd

private def corePartEquiv (z t g : G) (Q : Subgroup G)
    (hQ : Q ≤ coreInG z ⊔ conjugateCore z g) (htQ : t ∈ Q) :
    centralizer ({(⟨t, htQ⟩ : Q)} : Set Q) ≃* Q.comap (ambient z t g) where
  toFun x := ⟨⟨⟨x, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
    hQ x.val.property⟩, x.val.property⟩
  invFun x := ⟨⟨ambient z t g x, x.property⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp (x.val.val : Centralizer t).property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The order of the literal local centralizer follows from its two core centralizers
and its action on V; no ambient group order or centralizer model is used. -/
public theorem local_card (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) : Nat.card (localCentralizer z t a.g) = 48 := by
  let C := localCentralizer z t a.g
  let A := (coreInG z).comap (ambient z t a.g)
  let B := (conjugateCore z a.g).comap (ambient z t a.g)
  let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
  let : IsExtraspecial 2 (conjugateCore z a.g) :=
    IsExtraspecial.of_mulEquiv ((MulAut.conj a.g).subgroupMap (coreInG z)) h.coreInG_extraspecial
  have hgcard : Nat.card (conjugateCore z a.g) = 32 :=
    (card_map_of_injective (MulAut.conj a.g).injective).trans h.coreInG_card
  let eA := corePartEquiv z t a.g (coreInG z) le_sup_left htE.1
  let eB := corePartEquiv z t a.g (conjugateCore z a.g) le_sup_right htE.2
  have hA : 16 ≤ Nat.card A := by
    rw [← Nat.card_congr eA.toEquiv]
    exact IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two h.coreInG_card _
  have hB : 16 ≤ Nat.card B := by
    rw [← Nat.card_congr eB.toEquiv]
    exact IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two hgcard _
  have hA32 : Nat.card A ∣ 32 := by
    rw [← Nat.card_congr eA.toEquiv, ← h.coreInG_card]
    exact card_subgroup_dvd_card _
  have hC := local_card_dvd h d a htE ht hnt
  have hA48 : Nat.card A ∣ 48 := A.card_subgroup_dvd_card.trans hC
  have hA16 : Nat.card A = 16 := le_antisymm
    (Nat.le_of_dvd (by decide) (show Nat.card A ∣ 16 from Nat.dvd_gcd hA32 hA48)) hA
  have h16C : 16 ∣ Nat.card C := hA16 ▸ A.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := h16C
  have hk3 : k ∣ 3 := by
    rw [hk] at hC
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 16)).mp hC
  rcases Nat.prime_three.eq_one_or_self_of_dvd k hk3 with rfl | rfl
  · have hc16 : Nat.card C = 16 := by omega
    have hAtop : A = ⊤ := eq_of_le_of_card_ge le_top (by rw [card_top, hc16, hA16])
    have hBE : B ≤ eight z t a.g := by
      intro x hx
      exact ⟨show ambient z t a.g x ∈ coreInG z from (show x ∈ A from hAtop.symm ▸ mem_top x), hx⟩
    have hb8 := (Nat.card_le_card_of_injective _ (inclusion_injective hBE)).trans_eq (eight_card h a htE)
    omega
  · omega

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
