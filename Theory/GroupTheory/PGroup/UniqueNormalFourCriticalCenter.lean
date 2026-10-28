module

public import Theory.GroupTheory.PGroup.UniqueNormalFourCritical
public import Theory.GroupTheory.PGroup.NormalEightAbelianCriticalAction
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.PGroup.CriticalSubgroupAutDetection

/-!
# The center of a critical subgroup in the unique-four case

Nontrivial odd automorphisms rule out an abelian critical subgroup when the
ambient central omega has order two: a cyclic critical subgroup has a two-group
of automorphisms, while an abelian omega-four critical subgroup detects an odd
automorphism fixing no nonidentity element. The latter contradicts the unique
central involution, which every ambient automorphism fixes.

The critical center has first omega of order two or four. In the order-four
branch its ambient image is the unique normal four, so all critical involutions
are central. These reductions do not exclude the order-two branch or prove that
the critical center is elementary.

Sources: Thompson's critical subgroup theorem, Gorenstein, *Finite Groups*,
Theorem 5.3.11; Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, p.386;
MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- An abelian critical subgroup is impossible in the central-two outer-action case. -/
public theorem not_isMulCommutative_of_unique_four_of_omega_center_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P))
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C) : ¬ IsMulCommutative C := by
  intro hc
  let : IsMulCommutative C := hc
  rcases hC.card_omega_one_eq_two_or_four_of_unique_four hP hZ hno W hW hunique with ho | ho
  · let : IsCyclic C := (hP.to_subgroup C).isCyclic_of_card_omega_one_le_two ho.le
    exact hC.not_isPGroup_mulAut_of_ambient hP hAut (hP.to_subgroup C).mulAut_of_isCyclic_two
  · obtain ⟨a, ha, hfree⟩ := hC.exists_order_three_free_on_critical hP hAut ho
    let O := omega₁ (center P) (p := 2)
    let : O.Characteristic := omega₁_characteristic _
    let r := (MulAut.characteristic O).comp (MulAut.characteristic (center P))
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := O) 2 (by rw [hZ])
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    have haz1 : r a z ≠ 1 := by
      intro h
      exact hz1 ((r a).injective (h.trans (map_one (r a)).symm))
    obtain ⟨t, -, ht⟩ := (Nat.card_eq_two_iff' (1 : O)).mp hZ
    have hfix : r a z = z := (ht _ haz1).trans (ht _ hz1).symm
    have hzC : ((z : center P) : P) ∈ C := by
      apply map_subtype_le (center C)
      rw [← hC.centralizer_eq]
      exact center_le_centralizer _ (z : center P).property
    have hone := hfree ((z : center P) : P) hzC
      (congrArg (fun x : O => ((x : center P) : P)) hfix)
    exact hz1 (Subtype.ext (Subtype.ext hone))

end IsCriticalPSubgroup

namespace IsCriticalPSubgroup

/-- The critical center omega four maps onto the unique normal four. -/
public theorem omega_center_map_eq_unique_four_of_card_four
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hfour : Nat.card (omega₁ (center C) (p := 2)) = 4) :
    ((omega₁ (center C) (p := 2)).map (center C).subtype).map C.subtype = W := by
  let : C.Characteristic := hC.characteristic
  let O := omega₁ (center C) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center C).subtype
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let E := Z.map C.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  apply hunique E inferInstance inferInstance
  simpa only [E, Z, O, card_map_of_injective C.subtype_injective,
    card_map_of_injective (center C).subtype_injective] using hfour

/-- Critical involutions are central once the critical center omega has order four. -/
public theorem square_one_mem_center_of_unique_four_of_omega_center_four
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hfour : Nat.card (omega₁ (center C) (p := 2)) = 4)
    (x : C) (hx : x ^ 2 = 1) : x ∈ center C := by
  have hxW := hC.mem_unique_four_of_square_eq_one hno W hW hunique x.property
    (congrArg Subtype.val hx)
  rw [← hC.omega_center_map_eq_unique_four_of_card_four W hunique hfour] at hxW
  obtain ⟨z, hz, hzv⟩ := hxW
  exact (Subtype.ext hzv : z = x) ▸ map_subtype_le _ hz

/-- An elementary center with first omega of order four has order four. -/
public theorem card_center_eq_four_of_elementary_of_omega_center_four
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hfour : Nat.card (omega₁ (center C) (p := 2)) = 4)
    [IsElementaryAbelian 2 (center C)] : Nat.card (center C) = 4 := by
  have ht : omega₁ (center C) (p := 2) = ⊤ := by
    apply top_unique
    intro x hx
    apply Subgroup.subset_closure
    change x ^ 2 = 1
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center C)) x
  rw [ht, card_top] at hfour
  exact hfour

end IsCriticalPSubgroup

namespace IsCriticalPSubgroup

/-- The ambient central omega embeds in the critical center omega. -/
public theorem omega_ambient_center_le_critical_center_map
    {P : Type*} [Group P] {p : ℕ} {C : Subgroup P}
    (hC : IsCriticalPSubgroup p C) :
    (omega₁ (center P) (p := p)).map (center P).subtype ≤
      ((omega₁ (center C) (p := p)).map (center C).subtype).map C.subtype := by
  rw [map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  intro z hz
  have hzC : (z : P) ∈ C := map_subtype_le _
    (hC.centralizer_eq ▸ center_le_centralizer (C : Set P) z.property)
  have hzZ : (⟨z, hzC⟩ : C) ∈ center C := mem_center_iff.mpr
    (fun c => Subtype.ext (mem_center_iff.mp z.property c))
  refine ⟨⟨z, hzC⟩, ⟨⟨⟨z, hzC⟩, hzZ⟩, Subgroup.subset_closure ?_, rfl⟩, rfl⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : center P => (t : P)) hz

/-- The critical center has first omega of order two or four in the unique-four case. -/
public theorem card_omega_center_eq_two_or_four_of_unique_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C) :
    Nat.card (omega₁ (center C) (p := 2)) = 2 ∨
      Nat.card (omega₁ (center C) (p := 2)) = 4 := by
  let : C.Characteristic := hC.characteristic
  let O := omega₁ (center C) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center C).subtype
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let E := Z.map C.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  have hlow := card_le_of_le (hC.omega_ambient_center_le_critical_center_map (p := 2))
  rw [card_map_of_injective (center P).subtype_injective,
    card_map_of_injective C.subtype_injective,
    card_map_of_injective (center C).subtype_injective, hZ] at hlow
  have hupp := card_le_of_le (normal_elementary_le_unique_four hno W hW hunique E)
  change Nat.card ((O.map (center C).subtype).map C.subtype) ≤ Nat.card W at hupp
  rw [card_map_of_injective C.subtype_injective,
    card_map_of_injective (center C).subtype_injective, hW] at hupp
  rcases (((hP.to_subgroup C).to_subgroup (center C)).to_subgroup O).card_eq_or_dvd with h | h
  · change Nat.card O ≥ 2 at hlow
    omega
  · change Nat.card O ≥ 2 at hlow
    change Nat.card O = 2 ∨ Nat.card O = 4
    omega

end IsCriticalPSubgroup
