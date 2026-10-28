module

public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Binary commutators and abelian self-centralizers

Central commutators taking values in a subgroup of order two identify the
centralizer quotient with a subgroup of the binary character group. Factoring
characters through an elementary abelian quotient gives an index bound. For an
abelian two-group the square quotient has the order of its first omega subgroup.
The final lemma gives the normal-abelian containment needed in rotation products:
if its squares lie in a normal abelian rotation subgroup, it centralizes all
rotation squares.

This is the commutator-pairing calculation used in the symplectic specialization
of MacWilliams–Sah (Janko–Thompson, Math. Z. 113 (1970), result 1.1, p.385).
The binary character count follows `ExtraspecialCommutatorPairing`.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem binary_hom_card_le
    {X Z : Type*} [Group X] [Finite X] [IsElementaryAbelian 2 X]
    [Group Z] [Finite Z] [IsElementaryAbelian 2 Z] (hZ : Nat.card Z = 2) :
    Nat.card (X →* Z) ≤ Nat.card X := by
  classical
  let b := Module.Basis.ofVectorSpace (ZMod 2) (Additive X)
  let I := Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive X)
  let evaluation : (X →* Z) → (I → Z) := fun f i => f (b i).toMul
  have hinj : Function.Injective evaluation := by
    intro f g heq
    apply MonoidHom.toAdditive.injective
    apply (AddMonoidHom.toZModLinearMap_injective 2)
    apply b.ext
    intro i
    exact congrArg Additive.ofMul (congrFun heq i)
  have hcard := Nat.card_le_card_of_injective evaluation hinj
  have hX : Nat.card X = 2 ^ Nat.card I := by
    let _ : Fintype X := Fintype.ofFinite X
    let _ : Fintype I := Fintype.ofFinite I
    simpa only [Nat.card_eq_fintype_card, Fintype.card_additive, ZMod.card] using
      Module.card_fintype b
  simpa only [Nat.card_fun, hZ, ← hX] using hcard

private def commutatorRow {G : Type*} [Group G] (A Z : Subgroup G)
    (hZc : Z ≤ center G) (hc : ⁅(⊤ : Subgroup G), A⁆ ≤ Z) (g : G) : A →* Z where
  toFun a := ⟨⁅g, (a : G)⁆, hc (commutator_mem_commutator (mem_top g) a.property)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅g, (a : G) * (b : G)⁆ = ⁅g, (a : G)⁆ * ⁅g, (b : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅g, (a : G)⁆ (a : G) ⁅g, (b : G)⁆,
      mem_center_iff.mp (hZc (hc (commutator_mem_commutator (mem_top g) b.property))) (a : G)]
    simp only [← mul_assoc, mul_inv_cancel_right]

namespace Subgroup

/-- Count the commutator characters on an elementary abelian quotient of a
subgroup. The subgroup being centralized need not be normal or abelian. -/
public theorem centralizer_index_le_card_quotient_of_binary_commutators
    {G : Type*} [Group G] [Finite G] (A Z : Subgroup G)
    (K : Subgroup A) [K.Normal] [IsElementaryAbelian 2 (A ⧸ K)]
    (hZc : Z ≤ center G) (hZ : Nat.card Z = 2)
    (hc : ⁅(⊤ : Subgroup G), A⁆ ≤ Z)
    (hK : ∀ a : A, a ∈ K → ∀ g : G, Commute g (a : G)) :
    (centralizer (A : Set G)).index ≤ Nat.card (A ⧸ K) := by
  classical
  let : IsMulCommutative Z := isMulCommutative_iff.mpr fun x y =>
    Subtype.ext (mem_center_iff.mp (hZc y.property) x)
  let : IsElementaryAbelian 2 Z := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [hZ] using (pow_card_eq_one' (x := z)) }
  have hkill (g : G) : K ≤ (commutatorRow A Z hZc hc g).ker := by
    intro a ha
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hK a ha g).eq
  let pairing : G →* ((A ⧸ K) →* Z) := {
    toFun g := QuotientGroup.lift K (commutatorRow A Z hZc hc g) (hkill g)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K q
      apply Subtype.ext
      change ⁅(1 : G), (a : G)⁆ = 1
      simp
    map_mul' g h := by
      apply MonoidHom.ext
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K q
      apply Subtype.ext
      change ⁅g * h, (a : G)⁆ = ⁅g, (a : G)⁆ * ⁅h, (a : G)⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (hZc (hc (commutator_mem_commutator (mem_top h) a.property))) g]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp
        (hZc (hc (commutator_mem_commutator (mem_top h) a.property))) ⁅g, (a : G)⁆).symm }
  have hker : pairing.ker = centralizer (A : Set G) := by
    ext g
    change pairing g = 1 ↔ ∀ a ∈ A, a * g = g * a
    constructor
    · intro heq a ha
      have hh := congrArg (fun f : (A ⧸ K) →* Z =>
        (f (QuotientGroup.mk' K ⟨a, ha⟩) : G)) heq
      change ⁅g, a⁆ = 1 at hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
    · intro hg
      apply MonoidHom.ext
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K q
      apply Subtype.ext
      change ⁅g, (a : G)⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hg a a.property).symm
  let : Finite ((A ⧸ K) →* Z) := Finite.of_injective
    (fun f : (A ⧸ K) →* Z => (f : (A ⧸ K) → Z)) DFunLike.coe_injective
  rw [← hker, index_ker]
  exact (Nat.card_le_card_of_injective pairing.range.subtype
    pairing.range.subtype_injective).trans (binary_hom_card_le hZ)

/-- The index of an abelian self-centralizer with binary central commutators
is bounded by the order of its first omega subgroup. -/
public theorem index_le_omega_one_of_binary_commutators
    {G : Type*} [Group G] [Finite G] (A Z : Subgroup G)
    [IsMulCommutative A] (hA : IsPGroup 2 A)
    (hZc : Z ≤ center G) (hZ : Nat.card Z = 2)
    (hc : ⁅(⊤ : Subgroup G), A⁆ ≤ Z)
    (hC : centralizer (A : Set G) ≤ A) :
    A.index ≤ Nat.card (omega₁ A (p := 2)) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let : IsElementaryAbelian 2 (A ⧸ frattini A) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  have hK (a : A) (ha : a ∈ frattini A) (g : G) : Commute g (a : G) := by
    rw [← hA.square_range_eq_frattini] at ha
    obtain ⟨b, rfl⟩ := ha
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have he : (commutatorRow A Z hZc hc g) (b ^ 2) = 1 := by
      rw [map_pow, ← hZ]
      exact pow_card_eq_one'
    exact congrArg Subtype.val he
  exact (index_antitone hC).trans
    ((centralizer_index_le_card_quotient_of_binary_commutators A Z
      (frattini A) hZc hZ hc hK).trans_eq hA.card_frattini_quotient_eq_card_omega_one)

/-- A normal abelian subgroup whose squares lie in a normal abelian subgroup
centralizes the squares of that subgroup. -/
public theorem normal_abelian_centralizes_squares_of_squares_mem
    {G : Type*} [Group G] (A R : Subgroup G)
    [A.Normal] [R.Normal] [IsMulCommutative A] [IsMulCommutative R]
    (hsq : ∀ a ∈ A, a ^ 2 ∈ R) {r : G} (hr : r ∈ R) :
    A ≤ centralizer ({r ^ 2} : Set G) := by
  intro a ha
  have hcA : ⁅a, r⁆ ∈ A :=
    commutator_le_left A R (commutator_mem_commutator ha hr)
  have hcR : ⁅a, r⁆ ∈ R :=
    commutator_le_right A R (commutator_mem_commutator ha hr)
  have hac : a * ⁅a, r⁆ = ⁅a, r⁆ * a := A.le_centralizer hcA a ha
  have hrc : r * ⁅a, r⁆ = ⁅a, r⁆ * r := R.le_centralizer hcR r hr
  have hs : ⁅a ^ 2, r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (R.le_centralizer hr (a ^ 2) (hsq a ha))
  rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hac,
    mul_inv_cancel_right, ← pow_two] at hs
  apply mem_centralizer_singleton_iff.mpr
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [pow_two, commutatorElement_mul_right_eq_mul_conj,
    mul_assoc ⁅a, r⁆ r ⁅a, r⁆, hrc, ← mul_assoc,
    mul_inv_cancel_right, ← pow_two, hs]

end Subgroup
