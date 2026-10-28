module
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.InvertedOddSupportRank
public import Theory.Representation.CyclicFixedRank
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Binary displacement of a five-plane inverter

An irreducible three-group action on a group of order 25 has no fixed
hyperplane. Its hyperplane orbits therefore have at least three elements.
Each nonzero binary hyperplane contribution has dimension at least four,
so a faithful action has moving dimension at least twelve. Inversion of
an odd subgroup makes its support order the square of the inverter's
displacement on that support, giving displacement at least six.

All normalizer actions and the binary representation are retained.
Source: Aschbacher--Smith, proof of 12.6.26, p.832, using G.7.1 and D.2.11.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.BinaryCoprimeDegree
open scoped IsMulCommutative Pointwise
namespace Representation.IrreducibleFivePlaneInverter
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G A W : Type*} [Group G] [Finite G] [Group A]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem three_le_orbit
    (P : Subgroup G) (hP : Nat.card P = 25)
    (j : A →* normalizer (P : Set G)) (hA : IsPGroup 3 A)
    (hi : ∀ B : Subgroup P,
      (∀ a x, x ∈ B → P.normalizerMonoidHom (j a) x ∈ B) → B = ⊥ ∨ B = ⊤)
    (B : Subgroup P) (hB : B.index = 5) :
    3 ≤ Nat.card (normalizerHyperplaneOrbit P B) := by
  let α := P.normalizerMonoidHom.comp j
  let : MulAction A (Subgroup P) := MulAction.compHom _ α
  obtain ⟨n,hn⟩ := hA.card_orbit B
  have hnpos : 0 < n := by
    by_contra! hnzero
    have hn0 : n = 0 := by omega
    rw [hn0,pow_zero] at hn
    let : Subsingleton (MulAction.orbit A B) := Nat.card_eq_one_iff_unique.mp hn |>.1
    have hfixed : B ∈ MulAction.fixedPoints A (Subgroup P) :=
      MulAction.subsingleton_orbit_iff_mem_fixedPoints.mp ((Set.subsingleton_coe _).mp inferInstance)
    have hinv : ∀ a x, x ∈ B → P.normalizerMonoidHom (j a) x ∈ B := by
      intro a x hx
      have he := hfixed a
      change B.map (α a).toMonoidHom = B at he
      have hh := mem_map_of_mem (α a).toMonoidHom hx
      rw [he] at hh
      exact hh
    rcases hi B hinv with hb | ht
    · rw [hb,index_bot,hP] at hB
      omega
    · rw [ht,index_top] at hB
      omega
  have hsub : MulAction.orbit A B ⊆ normalizerHyperplaneOrbit P B := by
    rintro C ⟨a,rfl⟩
    exact ⟨j a,rfl⟩
  have hc := Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  rw [hn] at hc
  exact (show 3 ≤ 3 ^ n from (Nat.le_pow hnpos)).trans hc

private theorem twelve_le_fixedCodim
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (P : Subgroup G) [IsElementaryAbelian 5 P] (hP : Nat.card P = 25)
    (j : A →* normalizer (P : Set G)) (hA : IsPGroup 3 A)
    (hi : ∀ B : Subgroup P,
      (∀ a x, x ∈ B → P.normalizerMonoidHom (j a) x ∈ B) → B = ⊥ ∨ B = ⊤) :
    12 ≤ fixedCodim ρ P := by
  classical
  have hne : P ≠ ⊥ := by intro he; rw [he,card_bot] at hP; omega
  have hsum := hyperplane_dimension_sum ρ (by decide : 5 ≠ 2) P
  have hproper := fixed_finrank_lt_of_faithful ρ hf P hne
  have hpos : 0 < hyperplaneDimensionSum ρ P 5 := by omega
  obtain ⟨B,hB,hposB⟩ := Finset.sum_pos_iff.mp hpos
  have hidx := (mem_hyperplanes P 5 B).mp hB
  have hcontrib := orderOf_le_hyperplaneMultiplicity ρ (by decide : 5 ≠ 2) P B hidx hposB
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hcontrib
  have ho := three_le_orbit P hP j hA hi B hidx
  have hcount := orbit_mul_multiplicity_le_sum ρ P B hidx
  have he := fixedCodim_add_finrank ρ P
  change fixedCodim ρ P + Module.finrank (ZMod 2) (invariants (ρ.comp P.subtype)) = _ at he
  nlinarith

/-- The moving dimension of an inverted odd subgroup is at most twice the
inverter's displacement in the same module. -/
theorem fixedCodim_le_twice_displacement
    (ρ : Representation (ZMod 2) G W) (P : Subgroup G)
    (hodd : Odd (Nat.card P)) (t : G) (ht : IsInvolution t)
    (hinv : ∀ x ∈ P, t*x*t⁻¹ = x⁻¹) :
    fixedCodim ρ P ≤ 2 * Module.finrank (ZMod 2) (ρ t - LinearMap.id).range := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := W)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (Multiplicative W)) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (Multiplicative W)).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := Multiplicative W) (A := P)
    (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have hp := card_sup_eq_mul_of_normalizes_of_disjoint
    (FixedPoints.subgroup P (Multiplicative W)) (commutatorAction P (Multiplicative W))
    (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
  rw [hcompl.sup_eq_top,card_top,BinaryGroupAction.fixedPoints_eq,
    BinaryGroupAction.card_submoduleEquivSubgroup,BinaryGroupAction.commutator_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ P),Nat.card_zmod] at hp
  have hcW : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative W ≃ W),
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [hcW,←pow_add] at hp
  have hd := Nat.pow_right_injective (by decide : 1 < 2) hp
  have hcod := fixedCodim_add_finrank ρ P
  have hm : fixedCodim ρ P = Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ P) := by omega
  obtain ⟨hsq,_,hle⟩ := invertedOddSubgroup_support_card_data (W := Multiplicative W) P hodd t ht hinv
  have hb := Nat.pow_le_pow_left (Subgroup.card_le_of_le hle) 2
  rw [←hsq,BinaryGroupAction.commutator_card,BinaryGroupAction.commutator_card,
    CyclicFixedRank.commutator_eq_range,←pow_mul] at hb
  have hdim := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  omega

/-- An involution inverting a five-plane with irreducible cubic normalizer
action moves at least six binary dimensions in every faithful action. -/
theorem six_le_displacement
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (P : Subgroup G) [IsElementaryAbelian 5 P] (hP : Nat.card P = 25)
    (j : A →* normalizer (P : Set G)) (hA : IsPGroup 3 A)
    (hi : ∀ B : Subgroup P,
      (∀ a x, x ∈ B → P.normalizerMonoidHom (j a) x ∈ B) → B = ⊥ ∨ B = ⊤)
    (t : G) (ht : IsInvolution t) (hinv : ∀ x ∈ P, t*x*t⁻¹ = x⁻¹) :
    6 ≤ Module.finrank (ZMod 2) (ρ t - LinearMap.id).range := by
  have hl := twelve_le_fixedCodim ρ hf P hP j hA hi
  have hu := fixedCodim_le_twice_displacement ρ P (by rw [hP]; decide) t ht hinv
  omega
end Representation.IrreducibleFivePlaneInverter
