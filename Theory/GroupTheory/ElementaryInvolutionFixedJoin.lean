module
public import Theory.GroupTheory.ElementaryKernelInvolutionNormalizer
public import Theory.ElementaryAbelian.Join

/-!
# Fixed-join geometry for an elementary normal 2-subgroup

Let `E` be a normal elementary abelian 2-subgroup and let `y` be an
involution outside `E`. With `Z = E ∩ C_E(y)` and `X = ⟨y⟩Z`, this module
proves the elementary structure of `X`, the normalization of `X` by `E`, and
the exact fixed intersections `E ∩ C_H(X) = E ∩ X = Z`. Every element of
`X \ Z` has the same intersection `E ∩ C_H(x) = Z`.

The normalizer statement is obtained by applying the elementary-kernel
normalizer theorem to the quotient by `E`; the remaining identities are the
two normal forms `a` and `a*y` in `X`. This source-neutral geometry is the
fixed-join input to the actual Parrott core-involution argument.
-/

open Subgroup
open scoped IsMulCommutative Pointwise

/-- Fixed-join data for an outer involution acting on a normal elementary
abelian two-subgroup. -/
public theorem elementary_involution_fixed_join_data
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (y : G) (hy : orderOf y = 2) (hyE : y ∉ E) :
    let Z := E ⊓ centralizer ({y} : Set G)
    let X := zpowers y ⊔ Z
    IsElementaryAbelian 2 X ∧ E ≤ normalizer (X : Set G) ∧
      E ⊓ centralizer (X : Set G) = Z ∧ E ⊓ X = Z ∧
      ∀ x : G, x ∈ X → x ∉ Z → E ⊓ centralizer ({x} : Set G) = Z := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let Z := E ⊓ centralizer ({y} : Set G)
  let Y := zpowers y
  let X := Y ⊔ Z
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  let : IsElementaryAbelian 2 Z := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro a b
      exact Subtype.ext (congrArg (fun x : E => (x : G))
        (mul_comm (⟨(a : G), a.property.1⟩ : E) (⟨(b : G), b.property.1⟩ : E))))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property.1)) }
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.zpowers_of_pow_eq_one hy2
  have hyCZ : y ∈ centralizer (Z : Set G) :=
    fun _ hz => mem_centralizer_singleton_iff.mp hz.2
  have hYZ : Y ≤ centralizer (Z : Set G) := zpowers_le.mpr hyCZ
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mpr hYZ)
  have hyX : y ∈ X := (le_sup_left : Y ≤ X) (mem_zpowers y)
  have hcases (x : G) (hx : x ∈ X) : x ∈ Z ∨ ∃ a ∈ Z, x = a * y := by
    have hxprod : x ∈ (Z : Set G) * (Y : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left Z Y
        (hYZ.trans (centralizer_le_normalizer _)), sup_comm]
      exact hx
    obtain ⟨a, ha, b, hb, hab⟩ := hxprod
    change b ∈ zpowers y at hb
    rw [mem_zpowers_iff_mem_range_orderOf, hy] at hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · apply Or.inl
      have hax : x = a := by simpa only [pow_zero, mul_one] using hab.symm
      rw [hax]
      exact ha
    · exact Or.inr ⟨a, ha, by simpa only [pow_one] using hab.symm⟩
  have hEX : E ⊓ X = Z := by
    apply le_antisymm
    · intro x hx
      rcases hcases x hx.2 with hz | ⟨a, ha, hxa⟩
      · exact hz
      · exfalso
        apply hyE
        have hh := E.mul_mem (E.inv_mem ha.1) hx.1
        simpa only [hxa, inv_mul_cancel_left] using hh
    · exact le_inf inf_le_left le_sup_right
  have hcentral : E ⊓ centralizer (X : Set G) = Z := by
    apply le_antisymm
    · intro a ha
      exact ⟨ha.1, mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp ha.2) y hyX).symm⟩
    · intro a ha
      refine ⟨ha.1, ?_⟩
      intro x hx
      exact congrArg (fun x : X => (x : G))
        (mul_comm (⟨x, hx⟩ : X) (⟨a, (le_sup_right : Z ≤ X) ha⟩ : X))
  have houter (x : G) (hx : x ∈ X) (hxZ : x ∉ Z) :
      E ⊓ centralizer ({x} : Set G) = Z := by
    obtain ⟨a, ha, rfl⟩ := (hcases x hx).resolve_left hxZ
    apply le_antisymm
    · intro b hb
      refine ⟨hb.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have hba : b * a = a * b := congrArg (fun e : E => (e : G))
        (mul_comm (⟨b, hb.1⟩ : E) (⟨a, ha.1⟩ : E))
      have hh := mem_centralizer_singleton_iff.mp hb.2
      apply mul_left_cancel (a := a)
      simpa only [← mul_assoc, hba] using hh
    · intro b hb
      exact ⟨hb.1, mem_centralizer_singleton_iff.mpr
        (congrArg (fun x : X => (x : G))
          (mul_comm (⟨b, (le_sup_right : Z ≤ X) hb⟩ : X) (⟨a * y, hx⟩ : X)))⟩
  have hEN : E ≤ normalizer (X : Set G) := by
    let f := QuotientGroup.mk' E
    have hq : orderOf (f y) = 2 := orderOf_eq_prime
      (by rw [← map_pow, hy2, map_one])
      (fun hh => hyE ((QuotientGroup.eq_one_iff (N := E) y).mp hh))
    have hZmap : Z.map f = ⊥ := (map_eq_bot_iff Z).mpr (by
      rw [QuotientGroup.ker_mk']
      exact inf_le_left)
    have hXmap : X.map f = zpowers (f y) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hZmap, sup_bot_eq]
    have hn := normalizer_eq_comap_centralizer_of_elementary_kernel f X
      (by rw [QuotientGroup.ker_mk']; infer_instance) inferInstance
      (by rw [QuotientGroup.ker_mk', hcentral, hEX]) (f y) hq hXmap
    rw [hn]
    intro a ha
    change f a ∈ centralizer ({f y} : Set _)
    have hh : f a = 1 := (QuotientGroup.eq_one_iff (N := E) a).mpr ha
    rw [hh]
    exact one_mem _
  exact ⟨inferInstance, hEN, hcentral, hEX, houter⟩

/-- The fixed join is normalized exactly by the stabilizer of the
nonidentity coset of the chosen involution. -/
public theorem elementary_involution_fixed_join_normalizer
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (y : G) (hy : orderOf y = 2) (hyE : y ∉ E) :
    normalizer ((zpowers y ⊔ (E ⊓ centralizer ({y} : Set G)) : Subgroup G) : Set G) =
      (centralizer ({QuotientGroup.mk' E y} : Set (G ⧸ E))).comap
        (QuotientGroup.mk' E) := by
  let Z := E ⊓ centralizer ({y} : Set G)
  let X := zpowers y ⊔ Z
  let f := QuotientGroup.mk' E
  obtain ⟨hX, _, hcentral, hEX, _⟩ := elementary_involution_fixed_join_data E y hy hyE
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hq : orderOf (f y) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hy2, map_one])
    (fun hh => hyE ((QuotientGroup.eq_one_iff (N := E) y).mp hh))
  have hZmap : Z.map f = ⊥ := (map_eq_bot_iff Z).mpr (by
    rw [QuotientGroup.ker_mk']
    exact inf_le_left)
  have hXmap : X.map f = zpowers (f y) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hZmap, sup_bot_eq]
  exact normalizer_eq_comap_centralizer_of_elementary_kernel f X
    (by rw [QuotientGroup.ker_mk']; infer_instance) hX
    (by rw [QuotientGroup.ker_mk', hcentral, hEX]) (f y) hq hXmap
