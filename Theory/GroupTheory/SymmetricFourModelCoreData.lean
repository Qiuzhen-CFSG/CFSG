module

public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.Algebra.Group.End
import Mathlib.Tactic

/-!
# Elementary two-cores of the symmetric-four models

For a finite group isomorphic to `S₄` or `C₂ × S₄`, the two-core is elementary
abelian, with core and ambient orders `(4, 24)` or `(8, 48)`, respectively.
This supplies the intrinsic model calculation used in Stellmacher's
Section 11 argument, `refs/latex/stellmacher-n-group.tex`, lines 2076–2081.

The Klein four subgroup is realized as the even permutations whose square
is one. Kernel-checked finite calculations verify its subgroup laws,
normality, commutativity, exponent bound, and order. They also show that
every permutation outside it either has order three or has a product with
a conjugate of order three. Thus a normal two-subgroup cannot contain such
a permutation. Projection to `S₄` gives the corresponding upper bound in
`C₂ × S₄`, while the product with `C₂` gives the lower bound. Finally
`pCore_map_iso` transports both computations to the supplied model.

All concrete subgroups and transfer helpers are private; the public theorem
retains the two cardinality alternatives together with elementary abelianness.
-/

private abbrev S4 := Equiv.Perm (Fin 4)

set_option maxRecDepth 10000 in
private def fourCore : Subgroup S4 where
  carrier := {sigma | sigma.sign = 1 ∧ sigma ^ 2 = 1}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

private instance : DecidablePred (· ∈ fourCore) :=
  fun sigma => inferInstanceAs (Decidable (sigma.sign = 1 ∧ sigma ^ 2 = 1))

set_option maxRecDepth 10000 in
private instance : fourCore.Normal where
  conj_mem := by decide

private instance : IsElementaryAbelian 2 fourCore where
  is_comm.comm := by decide
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide)

private theorem fourCore_card : Nat.card fourCore = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 10000 in
private theorem outside_fourCore : ∀ sigma : S4, sigma ∉ fourCore →
    (sigma ^ 3 = 1 ∧ sigma ≠ 1) ∨
      ∃ tau : S4, (sigma * (tau * sigma * tau⁻¹)) ^ 3 = 1 ∧
        sigma * (tau * sigma * tau⁻¹) ≠ 1 := by
  decide

private theorem normal_two_le_fourCore (N : Subgroup S4) [N.Normal]
    (hN : IsPGroup 2 N) : N ≤ fourCore := by
  have no_three (sigma : S4) (hmem : sigma ∈ N) (hpow : sigma ^ 3 = 1)
      (hne : sigma ≠ 1) : False := by
    let element : N := ⟨sigma, hmem⟩
    have hc := hN.orderOf_coprime (n := 3) (by decide) element
    have hd : orderOf element ∣ 3 := orderOf_dvd_of_pow_eq_one
      (show element ^ 3 = 1 from Subtype.ext hpow)
    have he : orderOf element = 1 := Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd
    exact hne (congrArg Subtype.val (orderOf_eq_one_iff.mp he))
  intro sigma hmem
  by_contra hout
  rcases outside_fourCore sigma hout with ⟨hpow, hne⟩ | ⟨tau, hpow, hne⟩
  · exact no_three sigma hmem hpow hne
  · exact no_three _ (N.mul_mem hmem (Subgroup.Normal.conj_mem inferInstance sigma hmem tau))
      hpow hne

private theorem fourCore_eq : pCore 2 S4 = fourCore := by
  apply le_antisymm (normal_two_le_fourCore _ pCore_isPGroup)
  exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 fourCore⟩

private abbrev C2 := Multiplicative (ZMod 2)

private def eightCore : Subgroup (C2 × S4) :=
  (⊤ : Subgroup C2).prod fourCore

private instance : eightCore.Normal :=
  inferInstanceAs (((⊤ : Subgroup C2).prod fourCore).Normal)

private instance : IsElementaryAbelian 2 eightCore where
  is_comm.comm := by
    intro first second
    apply Subtype.ext
    apply Prod.ext
    · exact mul_comm _ _
    · exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨first.1.2, first.2.2⟩ : fourCore)
          ⟨second.1.2, second.2.2⟩)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro element
    apply Subtype.ext
    apply Prod.ext
    · exact (show ∀ value : C2, value ^ 2 = 1 by decide) element.1.1
    · exact element.2.2.2

private theorem eightCore_eq : pCore 2 (C2 × S4) = eightCore := by
  apply le_antisymm
  · let projection : C2 × S4 →* S4 := MonoidHom.snd _ _
    have hsurj : Function.Surjective projection := fun sigma => ⟨(1, sigma), rfl⟩
    let image := (pCore 2 (C2 × S4)).map projection
    let : image.Normal := Subgroup.Normal.map inferInstance projection hsurj
    have hle := normal_two_le_fourCore image (pCore_isPGroup.map projection)
    intro element hmem
    exact ⟨Subgroup.mem_top _, hle (Subgroup.mem_map.mpr ⟨element, hmem, rfl⟩)⟩
  · exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 eightCore⟩

private theorem eightCore_card : Nat.card eightCore = 8 := by
  change Nat.card ((⊤ : Subgroup C2).prod fourCore) = 8
  rw [Nat.card_congr ((⊤ : Subgroup C2).prodEquiv fourCore).toEquiv,
    Nat.card_prod, Nat.card_congr (Subgroup.topEquiv (G := C2)).toEquiv,
    fourCore_card]
  norm_num [Nat.card_eq_fintype_card]

private theorem elementary_of_equiv {G H : Type*} [Group G] [Group H]
    (equiv : G ≃* H) [IsElementaryAbelian 2 H] : IsElementaryAbelian 2 G where
  is_comm.comm := by
    intro first second
    apply equiv.injective
    simpa only [map_mul] using IsMulCommutative.is_comm.comm (equiv first) (equiv second)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro element
    apply equiv.injective
    simpa only [map_pow, map_one] using
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 H) (equiv element)

private noncomputable def coreEquiv {G H : Type*} [Group G] [Group H]
    (equiv : G ≃* H) : pCore 2 G ≃* pCore 2 H :=
  (equiv.subgroupMap (pCore 2 G)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 equiv))

public theorem symmetric_four_model_twoCore_data
    {K : Type*} [Group K] [Finite K]
    (hModel : Nonempty (K ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (K ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    IsElementaryAbelian 2 (pCore 2 K) ∧
      ((Nat.card (pCore 2 K) = 4 ∧ Nat.card K = 24) ∨
        (Nat.card (pCore 2 K) = 8 ∧ Nat.card K = 48)) := by
  rcases hModel with hModel | hModel
  · obtain ⟨equiv⟩ := hModel
    let core := (coreEquiv equiv).trans (MulEquiv.subgroupCongr fourCore_eq)
    refine ⟨elementary_of_equiv core, Or.inl ⟨?_, ?_⟩⟩
    · exact (Nat.card_congr core.toEquiv).trans fourCore_card
    · rw [Nat.card_congr equiv.toEquiv, Nat.card_eq_fintype_card]
      decide
  · obtain ⟨equiv⟩ := hModel
    let core := (coreEquiv equiv).trans (MulEquiv.subgroupCongr eightCore_eq)
    refine ⟨elementary_of_equiv core, Or.inr ⟨?_, ?_⟩⟩
    · exact (Nat.card_congr core.toEquiv).trans eightCore_card
    · rw [Nat.card_congr equiv.toEquiv, Nat.card_eq_fintype_card]
      decide
