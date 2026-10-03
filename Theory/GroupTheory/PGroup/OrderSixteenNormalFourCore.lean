module

public import Theory.GroupTheory.PGroup.MultipleNormalFourSylow
public import Theory.GroupTheory.PGroup.DihedralCentralFactor
public import Theory.GroupTheory.RankTwoNormalAbelian

/-!
# The order-sixteen core with no ambient normal four

In a finite group of elementary binary rank at most two with no normal
four-group, an order-sixteen normal two-subgroup containing a normal four
has a dihedral central factor and cyclic center of order four.

A unique normal four in the core would be characteristic, hence normal in
the ambient group. Two distinct normal fours instead give a dihedral
central factor. Its centralizer has order four and is therefore abelian;
it is the center of the core. The absence of ambient normal fours forces
this characteristic abelian subgroup to be cyclic.

Source: the order-sixteen specialization of Janko–Thompson,
Math. Z. 113 (1970), §4, printed pp.392–393.
-/

namespace Subgroup
open Subgroup

/-- A normal four in a normal subgroup cannot be unique if the ambient group
has no normal four. -/
public theorem exists_distinct_normal_four_of_no_ambient_normal_four
    {K : Type*} [Group K] [Finite K] (P : Subgroup K) [P.Normal]
    (hno : ∀ U : Subgroup K, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    ∃ F : Subgroup P, F.Normal ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧ F ≠ E := by
  by_contra! hn
  let : E.Characteristic := characteristic_of_unique_normal_four E hE hn
  let : (E.map P.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  exact hno (E.map P.subtype) inferInstance (IsElementaryAbelian.map _)
    (by rwa [card_map_of_injective P.subtype_injective])

/-- The core is a central product of a dihedral eight and its cyclic center of order four. -/
public theorem dihedral_central_factor_of_order_sixteen_of_no_ambient_normal_four
    {K : Type*} [Group K] [Finite K] (P : Subgroup K) [P.Normal]
    (hP : IsPGroup 2 P) (hcard : Nat.card P = 16)
    (hrank : ∀ U : Subgroup K, IsElementaryAbelian 2 U → Nat.card U < 8)
    (hno : ∀ U : Subgroup K, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    IsCyclic (center P) ∧ Nat.card (center P) = 4 ∧
      ∃ D : Subgroup P, D.Normal ∧ Nonempty (D ≃* DihedralGroup 4) ∧
        D ⊔ center P = ⊤ := by
  obtain ⟨F, hFn, hFe, hF, hne⟩ :=
    exists_distinct_normal_four_of_no_ambient_normal_four P hno E hE
  let : F.Normal := hFn
  let : IsElementaryAbelian 2 F := hFe
  have hr := elementary_card_lt_eight_of_subgroup hrank P
  obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours hr E F hE hF hne.symm
  have hgen := sup_centralizer_eq_top_of_distinct_normal_fours hP hr E F hE hF hne.symm
  let D := E ⊔ F
  let C := centralizer (D : Set P)
  have hC : Nat.card C = 4 := by
    have hh := card_eq_four_mul_card_centralizer_of_dihedral_factor D e hgen
    change Nat.card P = 4 * Nat.card C at hh
    rw [hcard] at hh
    omega
  let : IsMulCommutative C :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hC)
  have hCZ : C = center P := by
    apply le_antisymm ?_ (center_le_centralizer _)
    have hh : (⊤ : Subgroup P) ≤ centralizer (C : Set P) := by
      rw [← hgen]
      exact sup_le (le_centralizer_iff.mp le_rfl) (le_centralizer C)
    simpa only [coe_top, centralizer_univ] using (le_centralizer_iff.mp hh)
  have hcyc : IsCyclic (center P) :=
    isCyclic_characteristic_abelian_of_no_normal_four P hP
      (fun U hU _ => hrank U hU) hno (center P)
  refine ⟨hcyc, hCZ ▸ hC, D, inferInstance, ⟨e⟩, ?_⟩
  rwa [← hCZ]

end Subgroup
