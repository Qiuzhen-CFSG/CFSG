module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.NormalEightFour
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Critical subgroups and a unique normal four

If a finite two-group has a unique normal elementary four and no normal
elementary eight, every normal elementary subgroup lies in that four.
Indeed its order is one, two, or four; a normal subgroup of order two is
central, and the order-four case is the uniqueness hypothesis.

Every element of a critical subgroup lies in a normal abelian subgroup.
Applying the preceding observation to its omega subgroup confines every
critical involution, and hence the entire critical first omega, to the
unique normal four. Unlike the central-four reduction, this does not claim
that those involutions are central.

Source context: Thompson's critical subgroup theorem, Gorenstein,
*Finite Groups*, Theorem 5.3.11; Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3, printed p.386.
-/

open Subgroup

namespace Subgroup

/-- Every normal elementary subgroup lies in the unique normal four when
normal elementary eights are absent. -/
public theorem normal_elementary_le_unique_four
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] : E ≤ W := by
  have hlt : Nat.card E < 8 := by
    by_contra! h
    exact hno ⟨E, inferInstance, inferInstance, h⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnlt : n < 3 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    simpa [← hn] using hlt
  interval_cases n
  · have hbot : E = ⊥ := card_eq_one.mp (by simpa using hn)
    simp [hbot]
  · have hc : Nat.card E = 2 := by simpa using hn
    exact normal_elementary_le_four_of_no_normal_eight hno W E hW
      ((central_of_normal_card_two E hc).trans (center_le_centralizer _))
  · exact (hunique E inferInstance inferInstance (by simpa using hn)).le

/-- An involution in a normal abelian subgroup lies in the unique normal four. -/
public theorem mem_unique_four_of_square_eq_one_of_normal_abelian
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (A : Subgroup P) [A.Normal] [IsMulCommutative A]
    {x : P} (hx : x ∈ A) (hx2 : x ^ 2 = 1) : x ∈ W := by
  let O := omega₁ A (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let E := O.map A.subtype
  let : E.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  apply normal_elementary_le_unique_four hno W hW hunique E
  refine ⟨⟨x, hx⟩, subset_closure ?_, rfl⟩
  change (⟨x, hx⟩ : A) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa using hx2

end Subgroup

namespace IsCriticalPSubgroup

/-- The commutator subgroup of a critical subgroup is central in the ambient group. -/
public theorem commutator_self_le_ambient_center
    {P : Type*} [Group P] {p : ℕ} {C : Subgroup P}
    (hC : IsCriticalPSubgroup p C) : ⁅C, C⁆ ≤ center P := by
  have hzero : ⁅⁅(⊤ : Subgroup P), C⁆, C⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hC.commutator_le.trans (by rw [← hC.centralizer_eq])
  apply commutator_top_right_eq_bot_iff_le_center.mp
  apply commutator_commutator_eq_bot_of_rotate
  · simpa only [commutator_comm C (⊤ : Subgroup P)] using hzero
  · exact hzero

/-- Every involution in a critical subgroup lies in the unique normal four. -/
public theorem mem_unique_four_of_square_eq_one
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    {x : P} (hx : x ∈ C) (hx2 : x ^ 2 = 1) : x ∈ W := by
  obtain ⟨A, hAn, hAa, hxA, _⟩ := hC.exists_normal_abelian_of_mem hx
  let : A.Normal := hAn
  let : IsMulCommutative A := hAa
  exact mem_unique_four_of_square_eq_one_of_normal_abelian hno W hW hunique A hxA hx2

/-- The critical first omega lies in the unique normal four. -/
public theorem omega_one_map_le_unique_four
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    (omega₁ C (p := 2)).map C.subtype ≤ W := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  intro x hx
  exact hC.mem_unique_four_of_square_eq_one hno W hW hunique x.property
    (by simpa using congrArg Subtype.val hx)

/-- The first omega of a critical subgroup is elementary under the unique-four hypothesis. -/
public theorem omega_one_elementary_of_unique_four
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) : IsElementaryAbelian 2 (omega₁ C (p := 2)) := by
  have hle := hC.omega_one_map_le_unique_four hno W hW hunique
  have hmem (x : omega₁ C (p := 2)) : ((x : C) : P) ∈ W :=
    hle (mem_map_of_mem C.subtype x.property)
  refine {
    toIsMulCommutative := ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : W => (a : P)) (IsMulCommutative.is_comm.comm
      (⟨((x : C) : P), hmem x⟩ : W) (⟨((y : C) : P), hmem y⟩ : W))
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian _ (hmem x)

/-- Central omega embeds in the first omega of every critical subgroup. -/
public theorem omega_center_le_omega_one_map
    {P : Type*} [Group P] {p : ℕ} {C : Subgroup P}
    (hC : IsCriticalPSubgroup p C) :
    (omega₁ (center P) (p := p)).map (center P).subtype ≤
      (omega₁ C (p := p)).map C.subtype := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  intro z hz
  have hzC : (z : P) ∈ C :=
    map_subtype_le _ (hC.centralizer_eq ▸ center_le_centralizer (C : Set P) z.property)
  refine ⟨⟨z, hzC⟩, subset_closure ?_, rfl⟩
  apply Subtype.ext
  exact congrArg (fun a : center P => (a : P)) hz

/-- In the central-two case, a critical subgroup's elementary omega has order two or four. -/
public theorem card_omega_one_eq_two_or_four_of_unique_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    Nat.card (omega₁ C (p := 2)) = 2 ∨ Nat.card (omega₁ C (p := 2)) = 4 := by
  have hlower := card_le_of_le hC.omega_center_le_omega_one_map
  rw [card_map_of_injective (center P).subtype_injective,
    card_map_of_injective C.subtype_injective, hZ] at hlower
  have hupper := card_le_of_le (hC.omega_one_map_le_unique_four hno W hW hunique)
  rw [card_map_of_injective C.subtype_injective, hW] at hupper
  rcases ((hP.to_subgroup C).to_subgroup (omega₁ C (p := 2))).card_eq_or_dvd with h | h
  · omega
  · omega

end IsCriticalPSubgroup
