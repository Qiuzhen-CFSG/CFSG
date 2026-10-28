module

public import Theory.GroupTheory.PGroup.DihedralCentralFactor
public import Theory.GroupTheory.PGroup.RankTwoFour
public import Theory.GroupTheory.SpecificGroups.QuaternionCentralSquareEmbedding

/-!
# Absorbing the tail of a large extraspecial central factor

In a finite two-group with no elementary subgroup of order eight, an
extraspecial central factor of order thirty-two is the entire group.
The rank-two classification writes the factor as a central product of
quaternion and dihedral groups of order eight. The centralizer of the
dihedral subgroup has no elementary four, hence is cyclic or generalized
quaternion. Its embedded quaternion subgroup forces every element of the
commuting tail to square to one. The unique involution then puts that tail
inside the original extraspecial factor.

This supplies the whole-core reduction preceding the width-two exclusion in
Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389. The statement is
intrinsic: it needs no Hall presentation for the commuting tail.
-/

open Subgroup
open scoped IsMulCommutative

private theorem quaternion_commute_of_common_nonsquare
    {m : ℕ} (x a b : QuaternionGroup m) (ha : Commute a x) (hb : Commute b x)
    (hx : x ^ 2 ≠ 1) : Commute a b := by
  cases x <;> cases a <;> cases b <;>
    simp_all only [Commute, SemiconjBy, pow_two, QuaternionGroup.a_mul_a,
      QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa,
      QuaternionGroup.a.injEq, QuaternionGroup.xa.injEq, QuaternionGroup.one_def]
  · exact add_comm _ _
  · exact (hx (by congr 1; linear_combination hb)).elim
  · exact (hx (by congr 1; linear_combination ha)).elim
  · exact (hx (by congr 1; linear_combination ha)).elim
  · exact add_comm _ _
  · linear_combination ha
  · linear_combination -hb
  · linear_combination ha - hb

namespace Subgroup

/-- A quaternion-eight subgroup forces its centralizer in a rank-one two-group
inside itself. -/
public theorem centralizer_le_quaternion_of_no_elementary_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hfour : ∀ F : Subgroup P, IsElementaryAbelian 2 F → Nat.card F ≠ 4)
    (U : Subgroup P) (e : U ≃* QuaternionGroup 2) :
    centralizer (U : Set P) ≤ U := by
  let a : U := e.symm (QuaternionGroup.a 1)
  let b : U := e.symm (QuaternionGroup.xa 0)
  have hnc : ¬ Commute (a : P) (b : P) := by
    intro h
    have hh : a * b = b * a := Subtype.ext h.eq
    have he := congrArg e hh
    simp only [map_mul, a, b, e.apply_symm_apply] at he
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1) he
  have hsq (x : P) (hx : x ∈ centralizer (U : Set P)) : x ^ 2 = 1 := by
    rcases hP.isCyclic_or_quaternion_of_no_elementary_four hfour with hcyc | ⟨n, -, ⟨f⟩⟩
    · let : IsCyclic P := hcyc
      exact (hnc (Commute.all _ _)).elim
    · by_contra h
      have hf : (f x) ^ 2 ≠ 1 := fun hh => h (f.injective (by simpa using hh))
      have hab := quaternion_commute_of_common_nonsquare (f x) (f a) (f b)
        ((show Commute (a : P) x from hx a a.property).map f.toMonoidHom)
        ((show Commute (b : P) x from hx b b.property).map f.toMonoidHom) hf
      exact hnc (show Commute (a : P) (b : P) from
        f.injective (by simpa only [map_mul] using hab.eq))
  have hUcard : Nat.card U = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by omega : 1 < Nat.card U) U.card_le_card_group)
  obtain ⟨z, hz, -, hzunique⟩ := hP.exists_central_involution_of_no_elementary_four hfour
  let u : U := e.symm (QuaternionGroup.a 2)
  have hu : orderOf (u : P) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a]
    decide
  have huz : (u : P) = z := (hzunique u (by rw [← hu]; exact pow_orderOf_eq_one _)).resolve_left
    (by intro h; simp [h] at hu)
  intro x hx
  rcases hzunique x (hsq x hx) with rfl | rfl
  · exact U.one_mem
  · exact huz ▸ u.property

/-- An order-thirty-two extraspecial central factor absorbs every commuting
supplement under the elementary rank-two bound. -/
public theorem eq_top_of_extraspecial_card_thirty_two_of_central_product
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hrank : ∀ F : Subgroup P, IsElementaryAbelian 2 F → Nat.card F < 8)
    (A D : Subgroup P) [IsExtraspecial 2 A] (hA : Nat.card A = 32)
    (hc : D ≤ centralizer (A : Set P)) (hgen : A ⊔ D = ⊤) : A = ⊤ := by
  rcases IsExtraspecial.rank_two_classification (elementary_card_lt_eight_of_subgroup hrank A)
      with h | h | ⟨U, V, ⟨eU⟩, ⟨eV⟩, hVU, -, -⟩
  · obtain ⟨e⟩ := h
    have hh := Nat.card_congr e.toEquiv
    rw [hA, DihedralGroup.nat_card] at hh
    omega
  · obtain ⟨e⟩ := h
    have hh := Nat.card_congr e.toEquiv
    rw [hA, Nat.card_eq_fintype_card, QuaternionGroup.card] at hh
    omega
  · let V' := V.map A.subtype
    let U' := U.map A.subtype
    let C := centralizer (V' : Set P)
    have hUC : U' ≤ C := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      exact congrArg Subtype.val ((hVU hv u hu).symm)
    have hDC : D ≤ C := hc.trans (centralizer_le (map_subtype_le V))
    let Uc := U'.subgroupOf C
    let eu : Uc ≃* QuaternionGroup 2 := (subgroupOfEquivOfLe hUC).trans
      ((U.equivMapOfInjective A.subtype A.subtype_injective).symm.trans eU)
    let ev : V' ≃* DihedralGroup 4 :=
      (V.equivMapOfInjective A.subtype A.subtype_injective).symm.trans eV
    have hcentral := centralizer_le_quaternion_of_no_elementary_four (hP.to_subgroup C)
      (no_elementary_four_centralizer_of_dihedral hrank V' ev) Uc eu
    have hDA : D ≤ A := by
      intro d hd
      have hdC : (⟨d, hDC hd⟩ : C) ∈ centralizer (Uc : Set C) := by
        intro u hu
        exact Subtype.ext (hc hd u (map_subtype_le U hu))
      exact map_subtype_le U (hcentral hdC)
    exact top_unique (hgen ▸ sup_le le_rfl hDA)

end Subgroup
