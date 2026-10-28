module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveFaithfulSylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.AlternatingFive
public import Theory.SpecificGroups.SU3.InnerInvolutionAlternatingFive
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Mathlib.NumberTheory.Multiplicity

/-!
# Odd ternary groups cannot contain a normalized local A₅

An involution centralizer in odd PSL₃ or PSU₃ has a cubic-kernel covering
by a subgroup of GL₂. Its perfect subgroups have at most one involution,
so cannot contain A₅. Thus a Sylow subgroup normalizing an actual A₅ acts
faithfully and has order dividing eight. Both ternary group orders are
divisible by sixteen, which excludes these rows in A.3.14.

Source: Aschbacher--Smith A.3.14 and A.3.21(a), pp.49--50,55.
-/

public section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow centralizer is trivial when it contains no involution. -/
theorem sylow_centralizer_eq_bot_of_no_involution (S : Sylow 2 G) (B : Subgroup G)
    (hno : ∀ t ∈ centralizer (B : Set G), orderOf t = 2 → False) :
    (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥ := by
  let C := (S : Subgroup G) ⊓ centralizer (B : Set G)
  by_contra h
  let : Nontrivial C := (C.nontrivial_iff_ne_bot).mpr h
  have hp : IsPGroup 2 C := S.isPGroup'.to_le inf_le_left
  obtain ⟨n, hn, hc⟩ := hp.nontrivial_iff_card.mp inferInstance
  have hd : 2 ∣ Nat.card C := by
    rw [hc]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
  exact hno t t.property.2 (by simpa only [orderOf_coe] using ht)

/-- The order obstruction needs only the literal absence of a centralizing
involution, not an ambient even-characteristic hypothesis. -/
theorem not_sixteen_dvd_of_no_involution (S : Sylow 2 G) (B : Subgroup G)
    (e : B ≃* alternatingGroup (Fin 5))
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hno : ∀ t ∈ centralizer (B : Set G), orderOf t = 2 → False) :
    ¬ 16 ∣ Nat.card G := by
  intro hd
  have hs := S.pow_dvd_card_of_pow_dvd_card (n := 4) hd
  have hh := hs.trans (sylow_card_dvd_of_faithful S B e hSB
    (sylow_centralizer_eq_bot_of_no_involution S B hno))
  norm_num at hh

omit [Finite G] in
private theorem local_perfect (S : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let eB : B.subgroupOf (B ⊔ (S : Subgroup G)) ≃* B := subgroupOfEquivOfLe le_sup_left
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective (f := eB.toMonoidHom) eB.surjective

private def centralizer_embedding {H : Type*} [Group H] (e : G ≃* H)
    (B : Subgroup G) (t : G) (ht : t ∈ centralizer (B : Set G)) :
    B →* centralizer ({e t} : Set H) :=
  (e.toMonoidHom.comp B.subtype).codRestrict _ (by
    intro b
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      ← map_mul] using congrArg e (mem_centralizer_iff.mp ht b b.property))

omit [Finite G] in
private theorem centralizer_embedding_injective {H : Type*} [Group H] (e : G ≃* H)
    (B : Subgroup G) (t : G) (ht : t ∈ centralizer (B : Set G)) :
    Function.Injective (centralizer_embedding e B t ht) := by
  intro a b h
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val h)

private theorem sixteen_linear {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) : 16 ∣ Nat.card PSL(3,F) := by
  have h2 : 2 ∣ Nat.card F ^ 3 - 1 := by
    have := Nat.odd_iff.mp (ho.pow : Odd (Nat.card F ^ 3))
    omega
  have h16 : 16 ∣ Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
    exact mul_dvd_mul (dvd_mul_of_dvd_right h2 _) (Nat.eight_dvd_sq_sub_one_of_odd ho)
  rw [← PSL3.LinearThree.card_projective_mul_scalar F] at h16
  exact ((by decide : Nat.Coprime 16 3).of_dvd_right
    (Nat.gcd_dvd_left 3 (Nat.card F - 1))).dvd_of_dvd_mul_right h16

private theorem sixteen_unitary {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p ^ 2) (hj : ∀ x, J.conj x = x ^ p) :
    16 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hfix := FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
    (by simpa using hc) (by simpa using hj)
  simp only [pow_one] at hfix
  rw [Representation.SU3.BinaryDegree.card_projective J hc hfix]
  have hg : Nat.gcd 3 (p + 1) ∣ p ^ 2 - 1 := by
    rw [show p ^ 2 - 1 = (p - 1) * (p + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq p 1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (p + 1)) _
  have hd := dvd_mul_of_dvd_right hg ((p ^ 3 + 1) * p ^ 3)
  have h2 : 2 ∣ p ^ 3 + 1 := by
    have := Nat.odd_iff.mp (ho.pow : Odd (p ^ 3))
    omega
  have hcop := (by decide : Nat.Coprime 16 3).of_dvd_right (Nat.gcd_dvd_left 3 (p + 1))
  apply hcop.dvd_of_dvd_mul_right
  rw [Nat.div_mul_cancel hd]
  exact mul_dvd_mul (dvd_mul_of_dvd_left h2 _) (Nat.eight_dvd_sq_sub_one_of_odd ho)

/-- The actual odd PSL₃ row is incompatible with a full Sylow normalizing
an actual local A₅. -/
theorem not_odd_linear (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by simpa using hc)
  let : Group.IsPerfect B := local_perfect S hB
  have hp2 : p ≠ 2 := fun he => (by decide : ¬ Odd (2 : ℕ)) (he ▸ ho)
  have h2 : (2 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime F (p := p) Nat.prime_two hp2
  apply not_sixteen_dvd_of_no_involution S B eB hSB ?_
    (by rw [Nat.card_congr e.toEquiv]; exact sixteen_linear (hc.symm ▸ ho))
  intro t ht hot
  exact PSL3.OddInvolutionFixed.no_perfect_alternating_five_in_centralizer h2
    (e t) ((e.orderOf_eq t).trans hot) (centralizer_embedding e B t ht)
    (centralizer_embedding_injective e B t ht) eB

/-- The actual odd PSU₃ row has the same Sylow order obstruction. -/
theorem not_odd_unitary (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU G 3 p) : False := by
  obtain ⟨F, hF, hfin, J, hc, hj, ⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect B := local_perfect S hB
  apply not_sixteen_dvd_of_no_involution S B eB hSB ?_
    (by rw [Nat.card_congr e.toEquiv]; exact sixteen_unitary J ho hc hj)
  intro t ht hot
  exact SU3.InnerComponentExclusion.no_perfect_alternating_five_in_centralizer p ho F J hc hj
    (e t) ((e.orderOf_eq t).trans hot) (centralizer_embedding e B t ht)
    (centralizer_embedding_injective e B t ht) eB

/-- Both signs of the odd ternary Theorem C family are excluded. -/
theorem not_three_odd (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (unitary : Bool) (hm : Chapter1.Section02.LocalModels.IsPSLSign G unitary 3 p) : False := by
  cases unitary with
  | false => exact not_odd_linear S hB hSB eB hp ho hm
  | true => exact not_odd_unitary S hB hSB eB hp ho hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
