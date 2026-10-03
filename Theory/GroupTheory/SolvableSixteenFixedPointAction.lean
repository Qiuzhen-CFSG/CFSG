module

public import Theory.GroupTheory.ElementaryEightSolvableCore

/-!
# Solvable actions fixing an involution in an elementary sixteen

A solvable automorphism subgroup with trivial two-core that fixes a nonidentity
point of an elementary abelian group of order sixteen has Sylow two-subgroups
of order at most two. In fact, four does not divide its order.

The fixed point generates a line of order two. The induced action on the
quotient of order eight has a normal two-group kernel: an element of the
kernel fixes its own displacements in the line, and consequently squares to
one. The trivial two-core makes this action faithful. The elementary-eight
solvable-core bound then excludes four-divisibility of the image order.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p. 387,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
This module isolates the fixed-involution automizer argument.
-/

open Subgroup
open scoped IsMulCommutative

private def fixedLineQuotientAction
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (A : Subgroup (MulAut V)) (v : V)
    (hfix : ∀ a : A, (a : MulAut V) v = v) :
    A →* MulAut (V ⧸ zpowers v) where
  toFun a := QuotientGroup.congr _ _ (a : MulAut V) (by
    rw [MonoidHom.map_zpowers]
    change zpowers ((a : MulAut V) v) = zpowers v
    rw [hfix a])
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zpowers v) x
    rfl
  map_mul' a b := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zpowers v) x
    rfl

private theorem fixedLineQuotientAction_kernel
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (A : Subgroup (MulAut V)) (v : V)
    (hfix : ∀ a : A, (a : MulAut V) v = v) :
    IsPGroup 2 (fixedLineQuotientAction A v hfix).ker := by
  let f := fixedLineQuotientAction A v hfix
  have hline (a : A) (x : V) (hx : x ∈ zpowers v) : (a : MulAut V) x = x := by
    obtain ⟨n, rfl⟩ := hx
    simp only [map_zpow, hfix]
  have hinv (x : V) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x
  intro a
  refine ⟨1, ?_⟩
  suffices ha : a ^ 2 = 1 by simpa using ha
  apply Subtype.ext
  apply Subtype.ext
  ext x
  have he := MulEquiv.congr_fun (MonoidHom.mem_ker.mp a.property)
    (QuotientGroup.mk' (zpowers v) x)
  have hdelta : x⁻¹ * (a.val : MulAut V) x ∈ zpowers v :=
    QuotientGroup.eq.mp he.symm
  have hh := hline a.val _ hdelta
  simp only [map_mul, hinv] at hh
  change (a.val : MulAut V) ((a.val : MulAut V) x) = x
  apply mul_left_cancel (a := (a.val : MulAut V) x)
  exact hh.trans (mul_comm _ _)

/-- Four does not divide the order of a solvable automorphism group with trivial
two-core fixing a nonidentity element of an elementary abelian sixteen. -/
public theorem not_four_dvd_card_of_solvable_sixteen_fixed_point
    (V : Type*) [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (A : Subgroup (MulAut V)) [Group.IsSolvable A]
    (hcore : pCore 2 A = ⊥) (v : V) (hv : v ≠ 1)
    (hfix : ∀ a : A, (a : MulAut V) v = v) : ¬ 4 ∣ Nat.card A := by
  let L := zpowers v
  have hL : Nat.card L = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime _ hv
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hQ : Nat.card (V ⧸ L) = 8 := by
    have hh := L.index_mul_card
    change Nat.card (V ⧸ L) * Nat.card L = Nat.card V at hh
    rw [hL, hV] at hh
    omega
  let : IsElementaryAbelian 2 (V ⧸ L) :=
    { exponent_dvd_p := (Group.exponent_quotient_dvd L).trans
        (IsElementaryAbelian.exponent_dvd_p 2 V) }
  let f := fixedLineQuotientAction A v hfix
  have hk : f.ker = ⊥ := by
    apply bot_unique
    calc
      f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance, fixedLineQuotientAction_kernel A v hfix⟩
      _ = ⊥ := hcore
  let e : A ≃* f.range := MonoidHom.ofInjective (f.ker_eq_bot_iff.mp hk)
  have hc : pCore 2 f.range = ⊥ := by
    rw [← pCore_map_iso 2 e, hcore, Subgroup.map_bot]
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  intro hfour
  have hf : 4 ∣ Nat.card f.range := by rwa [← Nat.card_congr e.toEquiv]
  have hbound := four_le_card_pCore_of_solvable_elementary_eight_automorphisms
    (V ⧸ L) hQ f.range hf
  rw [hc, card_bot] at hbound
  omega

/-- Every Sylow two-subgroup of a solvable automorphism group with trivial two-core
fixing a nonidentity element of an elementary abelian sixteen has order at most two. -/
public theorem sylow_card_le_two_of_solvable_sixteen_fixed_point
    (V : Type*) [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (A : Subgroup (MulAut V)) [Group.IsSolvable A]
    (hcore : pCore 2 A = ⊥) (v : V) (hv : v ≠ 1)
    (hfix : ∀ a : A, (a : MulAut V) v = v) (R : Sylow 2 A) : Nat.card R ≤ 2 := by
  have hfour := not_four_dvd_card_of_solvable_sixteen_fixed_point V hV A hcore v hv hfix
  obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    apply hfour
    calc
      4 = 2 ^ 2 := by decide
      _ ∣ 2 ^ n := pow_dvd_pow 2 hh
      _ = Nat.card R := hn.symm
      _ ∣ Nat.card A := (R : Subgroup A).card_subgroup_dvd_card
  rw [hn]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hnle).trans (by decide)
