module

public import Theory.GroupTheory.PGroup.NormalAbelian
public import Theory.GroupTheory.PGroup.NormalAbelianIndexFour
public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic

/-!
# Normal abelian bases containing a normal four

In a finite two-group with no normal elementary eight, a normal abelian
subgroup containing a normal four has that four as its first omega subgroup.
Extending the four to a maximal normal abelian subgroup therefore gives a
self-centralizing product of two nontrivial cyclic two-groups.

An elementary subgroup containing the four meets this base in exactly the
four. Consequently an elementary sixteen induces a four-group of
automorphisms of the base. These are intrinsic reductions for the structural
problem in Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386; they do
not assert the cited MacWilliams classification.
-/

open Subgroup

namespace Subgroup

/-- A normal abelian overgroup of a normal four has precisely that omega four
when normal elementary eights are absent. -/
public theorem omega_one_eq_normal_four_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup P) [IsElementaryAbelian 2 W] [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4) (hWD : W ≤ D) :
    (omega₁ D (p := 2)).map D.subtype = W := by
  have hle : W ≤ (omega₁ D (p := 2)).map D.subtype := by
    intro w hw
    refine ⟨⟨w, hWD hw⟩, subset_closure ?_, rfl⟩
    change (⟨w, hWD hw⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian w hw
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective D.subtype_injective, hW]
  exact card_omega_one_le_four_of_normal_abelian_of_no_normal_eight hno D

/-- Every elementary overgroup of the omega four intersects the abelian base
in exactly that four. -/
public theorem elementary_inf_eq_of_omega_one_eq_four
    {P : Type*} [Group P]
    (W D B : Subgroup P) [IsElementaryAbelian 2 B]
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B) : B ⊓ D = W := by
  apply le_antisymm
  · intro b hb
    rw [← hO]
    refine ⟨⟨b, hb.2⟩, subset_closure ?_, rfl⟩
    change (⟨b, hb.2⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian b hb.1
  · exact le_inf hWB (hO ▸ map_subtype_le _)

/-- Conjugation by an elementary sixteen on a self-centralizing normal
abelian base with the specified omega four has image of order four. -/
public theorem card_conj_image_four_of_elementary_sixteen
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hB : Nat.card B = 16)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range = 4 := by
  let f := (MulAut.conjNormal : P →* MulAut D).comp B.subtype
  have hi := elementary_inf_eq_of_omega_one_eq_four W D B hO hWB
  have hk : f.ker.map B.subtype = W := by
    rw [← hi]
    apply le_antisymm
    · rintro x ⟨b, hb, rfl⟩
      refine ⟨b.property, hDC ?_⟩
      intro d hd
      have hh := congrArg (fun a : MulAut D => (a ⟨d, hd⟩ : P))
        (MonoidHom.mem_ker.mp hb)
      change (b : P) * d * (b : P)⁻¹ = d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro b hb
      refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      change b * (d : P) * b⁻¹ = d
      rw [(D.le_centralizer hb.2 d d.property).symm, mul_inv_cancel_right]
  have hkc : Nat.card f.ker = 4 := by
    have hh := congrArg (fun H : Subgroup P => Nat.card H) hk
    simpa only [card_map_of_injective B.subtype_injective, hW] using hh
  have hc := f.ker.card_mul_index
  rw [index_ker, hkc, hB] at hc
  change Nat.card f.range = 4
  omega

end Subgroup

/-- A normal four extends to a self-centralizing normal abelian rank-two base
with the same omega subgroup. -/
public theorem IsPGroup.exists_normal_abelian_base_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) :
    ∃ D : Subgroup P, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set P) ≤ D ∧
      (omega₁ D (p := 2)).map D.subtype = W ∧
      ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) := by
  obtain ⟨D, hWD, hDn, hDa, -, hDC⟩ :=
    exists_normal_abelian_selfCentralizing_containing hP W inferInstance inferInstance
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWD
  have hc : Nat.card (omega₁ D (p := 2)) = 4 := by
    have hh := congrArg (fun H : Subgroup P => Nat.card H) hO
    simpa only [card_map_of_injective D.subtype_injective, hW] using hh
  exact ⟨D, hWD, hDn, hDa, hDC, hO,
    (hP.to_subgroup D).equiv_two_cyclic_factors_of_card_omega_one_eq_four hc⟩
