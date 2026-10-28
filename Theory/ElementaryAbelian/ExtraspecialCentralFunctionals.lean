module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Central functionals and the full extraspecial transvection action

Let Z ≤ A ≤ U be literal subgroups, with A and Z elementary abelian,
|Z| = 2, [U,U] ≤ Z ≤ C_G(U), C_U(A) = A, and |A|² = 2|U|.
These are the standard maximal elementary subgroup data in an extraspecial
two-group. Commutation induces U/A ≃ Hom(A/Z,Z), with the original
commutator as its evaluation formula. The kernel is C_U(A); injectivity
on U/A and a binary basis bound for the dual give surjectivity.

For every functional f, the map a ↦ a f(aZ) is an involutory automorphism
of A. These maps embed the entire functional group in MulAut A, and their
image equals that of actual ambient conjugation by U. The center and all
quotient maps are literal subgroup inclusions, with relative normality proved
before taking U/A. The source convention a^u = u⁻¹au gives the same action.

This is the central-functional calculation in Aschbacher–Smith, Lemma
14.4.9, combined manuscript (1 March 2004), printed p.1010. The binary
basis argument follows `ExtraspecialCommutatorPairing`; it needs no choice
of central generator or coordinates for the extraspecial group.
-/

public section
open scoped IsMulCommutative commutatorElement
open Subgroup
namespace ExtraspecialCentralFunctionals
section Pairing
variable {G : Type*} [Group G] {U A Z : Subgroup G}

/-- Elementary maximal-subgroup data in a central extension with center of order two. -/
structure Configuration (U A Z : Subgroup G) : Prop where
  base_le : A ≤ U
  center_le : Z ≤ A
  central : Z ≤ centralizer (U : Set G)
  commutator_le : ⁅U,U⁆ ≤ Z
  self_centralizing : U ⊓ centralizer (A : Set G) = A
  center_card : Nat.card Z = 2
  card_eq : (Nat.card A)^2 = 2 * Nat.card U

variable (c : Configuration U A Z)

include c in
/-- The elementary base is normal relative to U. -/
theorem normal : (A.subgroupOf U).Normal := by
  refine ⟨fun a ha u => ?_⟩
  change (u : G) * (a : G) * (u : G)⁻¹ ∈ A
  have he : (u : G) * (a : G) * (u : G)⁻¹ = ⁅(u : G),(a : G)⁆ * (a : G) := by
    simp [commutatorElement_def, mul_assoc]
  rw [he]
  exact A.mul_mem (c.center_le (c.commutator_le
    (commutator_mem_commutator u.property a.property))) ha

include c in
/-- Every element of U normalizes the literal ambient subgroup A. -/
theorem normalizes : U ≤ normalizer (A : Set G) := by
  let := normal c
  exact le_normalizer_of_normal_subgroupOf c.base_le

variable [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 Z]

/-- All central-valued homomorphisms on the literal quotient A/Z. -/
abbrev Functionals := (A ⧸ Z.subgroupOf A) →* Z

private def commutatorHom (u : U) : A →* Z where
  toFun a := ⟨⁅(u : G),(a : G)⁆, c.commutator_le
    (commutator_mem_commutator u.property (c.base_le a.property))⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅(u : G),(a : G)*(b : G)⁆ = ⁅(u : G),(a : G)⁆ * ⁅(u : G),(b : G)⁆
    have hc := c.central (c.commutator_le
      (commutator_mem_commutator u.property (c.base_le b.property)))
      a (c.base_le a.property)
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅(u : G),(a : G)⁆, hc]
    simp only [← mul_assoc, mul_inv_cancel_right]

omit [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 Z] in
private theorem kills_center (u : U) : Z.subgroupOf A ≤ (commutatorHom c u).ker := by
  intro z hz
  apply Subtype.ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr (c.central hz u u.property)

/-- The central commutator pairing, with U as the acting variable. -/
def pairing : U →* Functionals (A := A) (Z := Z) where
  toFun u := QuotientGroup.lift (Z.subgroupOf A) (commutatorHom c u) (kills_center c u)
  map_one' := by
    apply MonoidHom.ext
    intro q
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf A) q
    apply Subtype.ext
    change ⁅(1 : G),(a : G)⁆ = 1
    simp
  map_mul' u v := by
    apply MonoidHom.ext
    intro q
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf A) q
    apply Subtype.ext
    change ⁅(u : G)*(v : G),(a : G)⁆ = ⁅(u : G),(a : G)⁆ * ⁅(v : G),(a : G)⁆
    have hc := c.central (c.commutator_le
      (commutator_mem_commutator v.property (c.base_le a.property)))
    rw [commutatorElement_mul_left_eq_conj_mul, hc u u.property, mul_inv_cancel_right]
    exact (hc _ (U.mul_mem (U.mul_mem (U.mul_mem u.property (c.base_le a.property))
      (U.inv_mem u.property)) (U.inv_mem (c.base_le a.property)))).symm

/-- Evaluation is the original ambient commutator, with no coordinate changes. -/
theorem pairing_apply (u : U) (a : A) :
    (pairing c u (QuotientGroup.mk' (Z.subgroupOf A) a) : G) = ⁅(u : G),(a : G)⁆ := by rfl

/-- The pairing kills exactly A, since its kernel is C_U(A). -/
theorem pairing_ker : (pairing c).ker = A.subgroupOf U := by
  ext u
  change pairing c u = 1 ↔ (u : G) ∈ A
  constructor
  · intro h
    rw [← c.self_centralizing]
    refine ⟨u.property, ?_⟩
    intro a ha
    have he := congrArg (fun f : Functionals (A := A) (Z := Z) =>
      (f (QuotientGroup.mk' (Z.subgroupOf A) ⟨a,ha⟩) : G)) h
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  · intro hu
    apply MonoidHom.ext
    intro q
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf A) q
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mul_comm (⟨u,hu⟩ : A) a))

private theorem binary_hom_card_le
    {X Y : Type*} [Group X] [Finite X] [IsElementaryAbelian 2 X]
    [Group Y] [Finite Y] [IsElementaryAbelian 2 Y] (hY : Nat.card Y = 2) :
    Nat.card (X →* Y) ≤ Nat.card X := by
  classical
  let b := Module.Basis.ofVectorSpace (ZMod 2) (Additive X)
  let I := Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive X)
  let evaluation : (X →* Y) → (I → Y) := fun f i => f (b i).toMul
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
  simpa only [Nat.card_fun, hY, ← hX] using hcard

variable [Finite G]

/-- Every central functional is realized by an element of U. -/
theorem pairing_surjective : Function.Surjective (pairing c) := by
  classical
  let := normal c
  let F := Functionals (A := A) (Z := Z)
  let : Finite F := Finite.of_injective (fun f : F => (f : (A ⧸ Z.subgroupOf A) → Z))
    DFunLike.coe_injective
  let p : (U ⧸ A.subgroupOf U) →* F :=
    QuotientGroup.lift (A.subgroupOf U) (pairing c) (pairing_ker c).ge
  have hinj : Function.Injective p :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr (pairing_ker c).symm
  let : IsElementaryAbelian 2 (A ⧸ Z.subgroupOf A) := {
    exponent_dvd_p := (MonoidHom.exponent_dvd
      (f := QuotientGroup.mk' (Z.subgroupOf A)) (QuotientGroup.mk'_surjective _)).trans
        (IsElementaryAbelian.exponent_dvd_p 2 A) }
  have hbound : Nat.card F ≤ Nat.card (A ⧸ Z.subgroupOf A) :=
    binary_hom_card_le c.center_card
  have hA := (A.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe c.base_le).toEquiv, index_eq_card] at hA
  have hZ := (Z.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe c.center_le).toEquiv, c.center_card,
    index_eq_card] at hZ
  have hpos : 0 < Nat.card A := Nat.card_pos
  have heq : Nat.card (A ⧸ Z.subgroupOf A) = Nat.card (U ⧸ A.subgroupOf U) := by
    have hs := c.card_eq
    nlinarith
  have hsurj := (hinj.bijective_of_nat_card_le (heq ▸ hbound)).2
  intro f
  obtain ⟨q,hq⟩ := hsurj f
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf U) q
  exact ⟨u,hq⟩

/-- The actual quotient U/A is isomorphic to the full functional group. -/
noncomputable def quotientEquiv : letI := normal c;
    (U ⧸ A.subgroupOf U) ≃* Functionals (A := A) (Z := Z) := by
  let := normal c
  exact (QuotientGroup.quotientMulEquivOfEq (pairing_ker c).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (pairing c) (pairing_surjective c))

/-- The quotient isomorphism retains the commutator evaluation formula. -/
theorem quotientEquiv_apply (u : U) (a : A) : letI := normal c;
    (quotientEquiv c (QuotientGroup.mk' (A.subgroupOf U) u)
      (QuotientGroup.mk' (Z.subgroupOf A) a) : G) = ⁅(u : G),(a : G)⁆ := by rfl

end Pairing

section Twists
variable {G : Type*} [Group G] {A Z : Subgroup G}
variable [IsElementaryAbelian 2 A]
variable (hZA : Z ≤ A)

private def shear (f : Functionals (A := A) (Z := Z)) : A →* A where
  toFun a := a * inclusion hZA (f (QuotientGroup.mk' (Z.subgroupOf A) a))
  map_one' := by simp
  map_mul' a b := by simp only [map_mul]; ac_rfl

private theorem quotient_inclusion (z : Z) :
    QuotientGroup.mk' (Z.subgroupOf A) (inclusion hZA z) = 1 :=
  (QuotientGroup.eq_one_iff (N := Z.subgroupOf A) (inclusion hZA z)).mpr z.property

private theorem shear_quotient (f : Functionals (A := A) (Z := Z)) (a : A) :
    QuotientGroup.mk' (Z.subgroupOf A) (shear hZA f a) =
      QuotientGroup.mk' (Z.subgroupOf A) a := by
  change QuotientGroup.mk' (Z.subgroupOf A) (a * inclusion hZA (f _)) = _
  rw [map_mul, quotient_inclusion, mul_one]

private theorem shear_involutive (f : Functionals (A := A) (Z := Z)) :
    Function.Involutive (shear hZA f) := by
  intro a
  change (a * inclusion hZA (f _)) * inclusion hZA
    (f (QuotientGroup.mk' (Z.subgroupOf A) (shear hZA f a))) = a
  rw [shear_quotient, mul_assoc, ← pow_two]
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A), mul_one]

/-- The central transvection attached to a functional, using the literal inclusion of Z in A. -/
def twist (f : Functionals (A := A) (Z := Z)) : MulAut A :=
  { shear hZA f with
    invFun := shear hZA f
    left_inv := shear_involutive hZA f
    right_inv := shear_involutive hZA f }

theorem twist_apply (f : Functionals (A := A) (Z := Z)) (a : A) :
    twist hZA f a = a * inclusion hZA (f (QuotientGroup.mk' (Z.subgroupOf A) a)) := by rfl

/-- All central functionals form a subgroup of the automorphism group. -/
def twists [IsMulCommutative Z] : Functionals (A := A) (Z := Z) →* MulAut A where
  toFun := twist hZA
  map_one' := by ext a; simp [twist_apply]
  map_mul' f g := by
    apply MulEquiv.ext
    intro a
    change shear hZA (f*g) a = shear hZA f (shear hZA g a)
    change a * inclusion hZA ((f*g) (QuotientGroup.mk' (Z.subgroupOf A) a)) =
      (a * inclusion hZA (g _)) * inclusion hZA
        (f (QuotientGroup.mk' (Z.subgroupOf A) (shear hZA g a)))
    rw [shear_quotient]
    simp only [MonoidHom.mul_apply, map_mul]
    ac_rfl

/-- Evaluation of the embedding uses the literal inclusion Z ≤ A. -/
theorem twists_apply [IsMulCommutative Z]
    (f : Functionals (A := A) (Z := Z)) (a : A) :
    twists hZA f a = a * inclusion hZA (f (QuotientGroup.mk' (Z.subgroupOf A) a)) := by rfl

theorem twists_injective [IsMulCommutative Z] : Function.Injective (twists hZA) := by
  intro f g h
  apply MonoidHom.ext
  intro q
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf A) q
  have he := congrArg (fun t : MulAut A => t a) h
  change a * inclusion hZA (f _) = a * inclusion hZA (g _) at he
  exact Subtype.ext (congrArg (fun x : A => (x : G)) (mul_left_cancel he))

theorem twist_fixes_center (f : Functionals (A := A) (Z := Z)) (z : Z) :
    twist hZA f (inclusion hZA z) = inclusion hZA z := by
  rw [twist_apply, quotient_inclusion, map_one, map_one, mul_one]

theorem twist_fixes_quotient (f : Functionals (A := A) (Z := Z)) (a : A) :
    QuotientGroup.mk' (Z.subgroupOf A) (twist hZA f a) =
      QuotientGroup.mk' (Z.subgroupOf A) a := shear_quotient hZA f a

/-- In characteristic two each central-functional automorphism is its own inverse. -/
theorem twist_inv (f : Functionals (A := A) (Z := Z)) :
    (twist hZA f)⁻¹ = twist hZA f := by rfl

end Twists

section Conjugation
variable {G : Type*} [Group G] [Finite G] {U A Z : Subgroup G}
variable [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 Z]
variable (c : Configuration U A Z)

/-- Restriction of actual ambient conjugation to A. -/
def conjugation : U →* MulAut A :=
  A.normalizerMonoidHom.comp (inclusion (normalizes c))

omit [Finite G] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 Z] in
theorem conjugation_apply (u : U) (a : A) :
    (conjugation c u a : G) = (u : G) * (a : G) * (u : G)⁻¹ := by rfl

omit [Finite G] in
theorem conjugation_eq_twists_pairing : conjugation c = (twists c.center_le).comp (pairing c) := by
  apply MonoidHom.ext
  intro u
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change (u : G) * (a : G) * (u : G)⁻¹ =
    (a : G) * (pairing c u (QuotientGroup.mk' (Z.subgroupOf A) a) : G)
  rw [pairing_apply]
  have hc := c.central (c.commutator_le
    (commutator_mem_commutator u.property (c.base_le a.property)))
    a (c.base_le a.property)
  rw [hc]
  simp [commutatorElement_def, mul_assoc]

/-- The action image is exactly the full group of central transvections. -/
theorem conjugation_range : (conjugation c).range = (twists c.center_le).range := by
  rw [conjugation_eq_twists_pairing]
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (pairing_surjective c),
    ← MonoidHom.range_eq_map]

omit [Finite G] in
/-- The book's right conjugation convention gives the same action. -/
theorem conjugation_source_apply (u : U) (a : A) :
    (conjugation c u a : G) = (u : G)⁻¹ * (a : G) * (u : G) := by
  have hi : (conjugation c u)⁻¹ = conjugation c u := by
    rw [conjugation_eq_twists_pairing]
    exact twist_inv _ _
  have hu : conjugation c u⁻¹ = conjugation c u := (map_inv _ _).trans hi
  rw [← hu, conjugation_apply]
  simp only [Subgroup.coe_inv, inv_inv]

end Conjugation

end ExtraspecialCentralFunctionals
