module

public import Theory.GroupTheory.NormalFourCentralizerAutomorphisms
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo

/-!
# The centralizer of a four inside an extraspecial subgroup of order thirty-two

A normal elementary four has centralizer of index two when the ambient
central omega has order two. An extraspecial subgroup containing the four
cannot centralize it, since its center has order two. Their intersection
therefore has order sixteen, is nonabelian, and all its squares lie in the
extraspecial center. Under elementary rank at most two, the whole four
centralizer has exactly three involutions, all central; the intersection
contains all of them.

These are the local inputs to an intrinsic square-fiber obstruction replacing
the outer-action calculation in Janko–Thompson, Math. Z. 113 (1970), §4,
printed pp.389–390. The fusion and transitive-involution input follows §1,
Theorem 1.3. No simplicity, ambient fusion, or index of the extraspecial
subgroup is needed for the results here.
-/

open Subgroup

/-- The centralizer of a normal four in a rank-two group has precisely three
involutions, all central. -/
public theorem Subgroup.centralizer_three_involutions_of_rank_two
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    (∀ x : centralizer (E : Set P), x ^ 2 = 1 →
      x ∈ center (centralizer (E : Set P))) ∧
    Nat.card {x : centralizer (E : Set P) // orderOf x = 2} = 3 := by
  classical
  let C := centralizer (E : Set P)
  let F := E.subgroupOf C
  have hEC : E ≤ C := le_centralizer E
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hEC
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hE
  have hmem (x : C) (hx : x ^ 2 = 1) : (x : P) ∈ E :=
    mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
      (congrArg Subtype.val hx) x.property
  refine ⟨?_, ?_⟩
  · intro x hx
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property x (hmem x hx)).symm
  · let e : {x : C // orderOf x = 2} ≃ {x : F // x ≠ 1} :=
      { toFun := fun x => ⟨⟨x, hmem x (by simpa only [x.property] using pow_orderOf_eq_one x.val)⟩,
          fun he => (orderOf_eq_prime_iff.mp x.property).2 (congrArg Subtype.val he)⟩
        invFun := fun x => ⟨x.val, orderOf_eq_prime
          (elemPow_eq_one_of_isElementaryAbelian _ x.val.property)
          (fun he => x.property (Subtype.ext he))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let : Fintype F := Fintype.ofFinite F
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, hF]
    simp

/-- Intersecting a large extraspecial subgroup with the centralizer of a normal
four gives a nonabelian subgroup of order sixteen with at most two squares. -/
public theorem Subgroup.normal_four_centralizer_large_extraspecial_data
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (K : Subgroup P) [IsExtraspecial 2 K] (hK : Nat.card K = 32) (hEK : E ≤ K) :
    ¬ IsMulCommutative (centralizer (E : Set P)) ∧
    ∃ A : Subgroup (centralizer (E : Set P)), Nat.card A = 16 ∧
      (∀ x : centralizer (E : Set P), x ^ 2 = 1 → x ∈ A) ∧
      ∃ z : centralizer (E : Set P),
        ∀ a : A, (a : centralizer (E : Set P)) ^ 2 = 1 ∨
          (a : centralizer (E : Set P)) ^ 2 = z := by
  let C := centralizer (E : Set P)
  have hiC : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two hP hZ E hE
  let : C.Normal := C.normal_of_index_eq_two hiC
  have hnot : ¬ K ≤ C := by
    intro hKC
    have hcenter : E.subgroupOf K ≤ center K := by
      intro e he
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext ((hKC k.property) e he).symm
    have hc := card_le_of_le hcenter
    rw [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv, hE,
      IsExtraspecial.center_order_p 2 K] at hc
    omega
  let B := C.subgroupOf K
  have hiB : B.index = 2 := by
    have hd : C.relIndex K ∣ 2 := by
      simpa only [hiC] using (relIndex_dvd_index_of_normal (H := C) (K := K))
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (hnot (relIndex_eq_one.mp h)).elim
    · exact h
  have hZB : center K ≤ B := by
    intro k hk e he
    exact congrArg Subtype.val (mem_center_iff.mp hk (⟨e, hEK he⟩ : K))
  have hnonab : ¬ IsMulCommutative C := by
    intro hab
    let : IsMulCommutative C := hab
    exact IsExtraspecial.not_isMulCommutative_of_index_two (by omega) B hiB hZB
      (C.comap_injective_isMulCommutative K.subtype_injective)
  refine ⟨hnonab, K.subgroupOf C, ?_, ?_, ?_⟩
  · have e : K.subgroupOf C ≃ B := {
      toFun := fun a => ⟨⟨a, a.property⟩, a.val.property⟩
      invFun := fun b => ⟨⟨b, b.property⟩, b.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hh := B.card_mul_index
    rw [hiB, hK] at hh
    rw [Nat.card_congr e]
    omega
  · intro x hx
    exact hEK (mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
      (congrArg Subtype.val hx) x.property)
  · obtain ⟨w, hw, hall⟩ := (Nat.card_eq_two_iff' (1 : center K)).mp
      (IsExtraspecial.center_order_p 2 K)
    let z : C := ⟨(w : K), hZB w.property⟩
    refine ⟨z, ?_⟩
    intro a
    let k : K := ⟨((a : C) : P), a.property⟩
    by_cases hk : k ^ 2 = 1
    · exact Or.inl (Subtype.ext (congrArg (fun v : K => (v : P)) hk))
    · right
      have hh := hall ⟨k ^ 2, IsExtraspecial.square_mem_center k⟩
        (fun h => hk (congrArg Subtype.val h))
      exact Subtype.ext (congrArg (fun u : center K => ((u : K) : P)) hh)
