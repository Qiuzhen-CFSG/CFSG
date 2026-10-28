module

public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.GroupTheory.PGroup.NormalFourElementaryReplacement
public import Theory.GroupTheory.PGroup.NormalEightCenterTwoHomocyclicAction
public import Theory.GroupTheory.PGroup.NormalEightCenterTwoUnequalAction

/-!
# The central-omega-two elementary-order bound

Choose a self-centralizing normal abelian base containing a prescribed normal
four `W`. In the absence of normal elementary eights its first omega is `W`,
and the base is a product of two nontrivial cyclic two-groups. Elementary
replacement reduces the order bound to elementary subgroups containing `W`.
For such a subgroup the conjugation kernel on the base is exactly `W`.
Thus an action image of order at most four gives order at most sixteen.

The equal- and unequal-factor action theorems discharge this bound when the
central omega has order two and `W` is the unique normal elementary four.
The exact kernel formula and conditional assembly remain available separately.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.1, printed p.385,
applied in Lemma 3.1, pp.387–388,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace Subgroup

/-- On an elementary subgroup, conjugation on a self-centralizing normal
abelian base has kernel its intersection with the base's first omega. -/
public theorem card_eq_inf_omega_mul_conj_image_of_elementary
    {P : Type*} [Group P] [Finite P]
    (W D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card A = Nat.card (A ⊓ W : Subgroup P) *
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range := by
  let f := (MulAut.conjNormal : P →* MulAut D).comp A.subtype
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hk : f.ker.map A.subtype = A ⊓ W := by
    apply le_antisymm
    · rintro x ⟨a, ha, rfl⟩
      have haD : (a : P) ∈ D := by
        apply hDC
        intro d hd
        have hh := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P))
          (MonoidHom.mem_ker.mp ha)
        change (a : P) * d * (a : P)⁻¹ = d at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      refine ⟨a.property, ?_⟩
      rw [← hO]
      refine ⟨⟨a, haD⟩, subset_closure ?_, rfl⟩
      change (⟨(a : P), haD⟩ : D) ^ (2 ^ 1) = 1
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (a : P) a.property
    · intro a ha
      refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      change a * (d : P) * a⁻¹ = d
      rw [(D.le_centralizer (hWD ha.2) d d.property).symm, mul_inv_cancel_right]
  have hkc : Nat.card f.ker = Nat.card (A ⊓ W : Subgroup P) := by
    have hh := congrArg (fun H : Subgroup P => Nat.card H) hk
    simpa only [card_map_of_injective A.subtype_injective] using hh
  have hc := f.ker.card_mul_index
  rw [index_ker, hkc] at hc
  exact hc.symm

end Subgroup

namespace IsPGroup

/-- Bounding the action images of elementary overgroups of the normal four
on rank-two abelian bases suffices to bound all elementary orders by sixteen.
The structural action bound is an explicit premise, not a rank assumption. -/
public theorem elementary_card_le_sixteen_of_normal_four_of_overgroup_action_bound
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (himage : ∀ (D : Subgroup P) [D.Normal] [IsMulCommutative D],
      centralizer (D : Set P) ≤ D → (omega₁ D (p := 2)).map D.subtype = W →
      ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
      (D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) →
      ∀ (B : Subgroup P) [IsElementaryAbelian 2 B], W ≤ B →
        Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4) :
    ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A ≤ 16 := by
  obtain ⟨D, -, hDn, hDa, hDC, hO, n, m, hn, hm, ⟨e⟩⟩ :=
    hP.exists_normal_abelian_base_of_no_normal_eight hno W hW
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  obtain ⟨B, hB, hWB, hAB⟩ := hP.exists_elementary_overgroup_normal_four_card_ge W hW A
  let : IsElementaryAbelian 2 B := hB
  apply hAB.trans
  rw [card_eq_inf_omega_mul_conj_image_of_elementary W D hDC hO B,
    inf_eq_right.mpr hWB, hW]
  exact Nat.mul_le_mul_left 4 (himage D hDC hO n m hn hm e B hWB)

/-- If the central omega has order two and the normal elementary four is unique,
excluding normal elementary subgroups of order at least eight bounds every
elementary subgroup by sixteen. -/
public theorem elementary_card_le_sixteen_of_center_omega_two_of_unique_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A ≤ 16 := by
  apply hP.elementary_card_le_sixteen_of_normal_four_of_overgroup_action_bound hno W hW
  intro D _ _ hDC hO n m hn hm e B _ hWB
  by_cases hnm : n = m
  · subst m
    exact hP.conj_image_card_le_four_of_homocyclic_overgroup hZ hno W hW hunique
      D hDC hO n hn e B hWB
  · exact hP.card_conj_image_le_four_of_unequal_overgroup hno hZ W hW hunique
      D hDC hO n m hn hm hnm e B hWB

end IsPGroup
