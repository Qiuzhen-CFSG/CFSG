module

public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PGroup.Omega

/-!
# Four-groups under an elementary rank bound

If every elementary binary subgroup has order less than eight, an involution
centralizing an elementary four-group already belongs to that four-group.
Indeed its join with the four-group is elementary, has order divisible by four,
and has order less than eight. In particular a central four-group is the whole
first omega subgroup. No two-group assumption is needed for these facts.

For a nontrivial finite two-group the first omega subgroup of its center has
order two or four under the same bound. This is the elementary case division
used in Janko–Thompson, Math. Z. 113 (1970), §6, p.394. The central-four
consequence supplies the omega equality required by Lyons, Trans. AMS 164
(1972), Theorem 2, p.372.
-/

namespace Subgroup

/-- An element of square one centralizing an elementary four-group belongs to it
when the ambient group has no elementary subgroup of order at least eight. -/
public theorem mem_four_of_square_eq_one_of_elementary_card_lt_eight
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    {x : P} (hx : x ^ 2 = 1) (hxC : x ∈ centralizer (E : Set P)) : x ∈ E := by
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  let : IsElementaryAbelian 2 (E ⊔ zpowers x : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hxC)
  have hlt := hrank (E ⊔ zpowers x) inferInstance
  have hdiv : 4 ∣ Nat.card (E ⊔ zpowers x : Subgroup P) := by
    rw [← hE]
    exact card_dvd_of_le le_sup_left
  have hge := card_le_of_le (le_sup_left : E ≤ E ⊔ zpowers x)
  have heq : E = E ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (by omega)
  rw [heq]
  exact (le_sup_right : zpowers x ≤ E ⊔ zpowers x) (mem_zpowers x)

/-- A central elementary four-group contains every involution and equals first omega. -/
public theorem omega_one_eq_of_central_four_of_elementary_card_lt_eight
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hEZ : E ≤ center P) : omega₁ P (p := 2) = E := by
  apply le_antisymm ?_ elementaryAbelian_le_omega₁
  apply (closure_le E).2
  intro x hx
  apply mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
    (by simpa using hx)
  rw [mem_centralizer_iff]
  intro e he
  exact (mem_center_iff.mp (hEZ he) x).symm

/-- The bound on elementary subgroup orders descends to each subgroup carrier. -/
public theorem elementary_card_lt_eight_of_subgroup
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (H : Subgroup G) :
    ∀ A : Subgroup H, IsElementaryAbelian 2 A → Nat.card A < 8 := by
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  have h := hrank (A.map H.subtype) (IsElementaryAbelian.map H.subtype)
  rwa [card_map_of_injective H.subtype_injective] at h

/-- If first omega of the center has order four, it contains every involution
under the elementary rank bound. The equality is in the ambient carrier. -/
public theorem omega_one_eq_map_center_of_card_four
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    omega₁ P (p := 2) = (omega₁ (center P) (p := 2)).map (center P).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := omega₁ (center P) (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 (O.map (center P).subtype) := IsElementaryAbelian.map _
  apply omega_one_eq_of_central_four_of_elementary_card_lt_eight hrank
    (O.map (center P).subtype) ?_ (map_subtype_le _)
  rwa [card_map_of_injective (center P).subtype_injective]

/-- All elements of square one are central in the central-four case. -/
public theorem mem_center_of_square_eq_one_of_omega_center_card_four
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center P) (p := 2)) = 4)
    {x : P} (hx : x ^ 2 = 1) : x ∈ center P := by
  have hmem : x ∈ omega₁ P (p := 2) := subset_closure (by simpa using hx)
  rw [omega_one_eq_map_center_of_card_four hrank hfour] at hmem
  exact map_subtype_le _ hmem

/-- The central-four rank bound gives exactly four elements of square one,
without any assumption on the exponent of the ambient group. -/
public theorem card_square_one_of_omega_center_card_four
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    Nat.card {x : P // x ^ 2 = 1} = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E := (omega₁ (center P) (p := 2)).map (center P).subtype
  let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hmem (x : P) : x ^ 2 = 1 ↔ x ∈ E := by
    constructor
    · intro hx
      rw [show E = omega₁ P (p := 2) from
        (omega_one_eq_map_center_of_card_four hrank hfour).symm]
      exact subset_closure (by simpa using hx)
    · exact elemPow_eq_one_of_isElementaryAbelian x
  have he : {x : P // x ^ 2 = 1} ≃ E :=
    Equiv.subtypeEquiv (Equiv.refl P) hmem
  rw [Nat.card_congr he, card_map_of_injective (center P).subtype_injective]
  exact hfour

/-- In the central-four case there are precisely three involutions. -/
public theorem card_involutions_of_omega_center_card_four
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    Nat.card {x : P // orderOf x = 2} = 3 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := {x : P // x ^ 2 = 1}
  let oneX : X := ⟨1, by simp⟩
  let e : {x : P // orderOf x = 2} ≃ {x : X // x ≠ oneX} :=
    { toFun := fun x => ⟨⟨x, by simpa only [x.property] using pow_orderOf_eq_one x.val⟩,
        fun h => (orderOf_eq_prime_iff.mp x.property).2 (congrArg (fun x : X => x.val) h)⟩
      invFun := fun x => ⟨x.val.val, orderOf_eq_prime x.val.property
        (fun h => x.property (Subtype.ext h))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype X := Fintype.ofFinite X
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hX : Fintype.card X = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_square_one_of_omega_center_card_four hrank hfour
  simp [hX]

end Subgroup

namespace IsPGroup

/-- First omega of the center of a nontrivial two-group has order two or four
under the elementary rank bound. -/
public theorem card_omega_one_center_eq_two_or_four
    {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hP : IsPGroup 2 P)
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8) :
    Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 2 ∨
      Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  let O := omega₁ (Subgroup.center P) (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  have hdiv : 2 ∣ Nat.card (Subgroup.center P) :=
    (hP.to_subgroup _).card_eq_or_dvd.resolve_left (Nat.ne_of_gt Finite.one_lt_card)
  have hnb := omega₁_map_subtype_ne_bot (Subgroup.center P) 2 hdiv
  have hone : Nat.card O ≠ 1 := by
    intro hc
    have hb : O = ⊥ := Subgroup.card_eq_one.mp hc
    exact hnb (by rw [show omega₁ (Subgroup.center P) (p := 2) = ⊥ from hb,
      Subgroup.map_bot])
  have hlt := Subgroup.elementary_card_lt_eight_of_subgroup hrank (Subgroup.center P)
    O inferInstance
  obtain ⟨n, hn⟩ := ((hP.to_subgroup (Subgroup.center P)).to_subgroup O).exists_card_eq
  have hnlt : n < 3 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    simpa [← hn] using hlt
  change Nat.card O = 2 ∨ Nat.card O = 4
  interval_cases n
  · exact False.elim (hone (by simpa using hn))
  · exact Or.inl (by simpa using hn)
  · exact Or.inr (by simpa using hn)

end IsPGroup
