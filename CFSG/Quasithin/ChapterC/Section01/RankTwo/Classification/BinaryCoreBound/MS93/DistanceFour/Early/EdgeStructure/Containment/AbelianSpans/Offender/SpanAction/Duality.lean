module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SpanAction.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Commutator self-duality of the actual span quotient

For a span W whose derived subgroup D has order two and centralizes its
local stabilizer, commutation defines a pairing W/Z(W) × W/Z(W) → D.
The class-two commutator identities make it multiplicative in each variable;
its radical is trivial by the definition of Z(W). No restriction on the
order or exponent of the whole center is needed.

Identify the actual D with the multiplicative form of the additive group
of ZMod 2. The resulting bilinear form identifies the finite binary quotient
with its linear dual. The supplied conjugation equation and the surjective
local projection show that the action preserves the form, so this is an
equivalence with the contragredient representation for the same actor.

The pairing construction adapts the algebra in
`Theory.GroupTheory.Commutator.ElementaryCentralQuotient` with D as target;
the linear conversion follows `Theory.ElementaryAbelian.BinaryPairingDuality`.
This proves the conditional duality input to the nonabelian-span argument,
not the separate offender bound or its source-theorem assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.4), printed p.902.
-/

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender

private theorem exists_derived_pairing {G : Type*} [Group G]
    (W : Subgroup G) [IsMulCommutative (⁅W,W⁆ : Subgroup G)]
    (hc : ⁅W,W⁆ ≤ centralizer (W : Set G)) :
    ∃ b : (W ⧸ center W) →* ((W ⧸ center W) →* (⁅W,W⁆ : Subgroup G)),
      (∀ x y : W, (b (QuotientGroup.mk' (center W) x)
        (QuotientGroup.mk' (center W) y) : G) = ⁅(x : G),(y : G)⁆) ∧
      (∀ x, b x x = 1) ∧
      (∀ x, (∀ y, b x y = 1) → x = 1) := by
  let D := ⁅W,W⁆
  let Z := center W
  let V := W ⧸ Z
  have hmem (x y : W) : ⁅(x : G),(y : G)⁆ ∈ D :=
    commutator_mem_commutator x.property y.property
  have hconj (g : W) (x y : W) :
      (g : G) * ⁅(x : G),(y : G)⁆ * (g : G)⁻¹ = ⁅(x : G),(y : G)⁆ := by
    rw [hc (hmem x y) g g.property, mul_assoc, mul_inv_cancel, mul_one]
  let c (x y : W) : D := ⟨⁅(x : G),(y : G)⁆, hmem x y⟩
  have c_right (x y z : W) : c x (y*z) = c x y * c x z := by
    apply Subtype.ext
    change ⁅(x : G), (y : G)*(z : G)⁆ = ⁅(x : G),(y : G)⁆ * ⁅(x : G),(z : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅(x : G),(y : G)⁆ * ((y : G) * ⁅(x : G),(z : G)⁆ * (y : G)⁻¹) := by group
      _ = _ := by rw [hconj]
  have c_left (x y z : W) : c (x*y) z = c x z * c y z := by
    apply Subtype.ext
    change ⁅(x : G)*(y : G), (z : G)⁆ = ⁅(x : G),(z : G)⁆ * ⁅(y : G),(z : G)⁆
    rw [commutatorElement_mul_left_eq_conj_mul, hconj]
    exact congrArg Subtype.val (mul_comm (c y z) (c x z))
  have c_center_left (z y : W) (hz : z ∈ Z) : c z y = 1 := by
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact congrArg Subtype.val (mem_center_iff.mp hz y).symm
  have c_center_right (x z : W) (hz : z ∈ Z) : c x z = 1 := by
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact congrArg Subtype.val (mem_center_iff.mp hz x)
  let f (x : W) : W →* D := {
    toFun := c x
    map_one' := c_center_right x 1 (one_mem Z)
    map_mul' := c_right x }
  let g (x : W) : V →* D := QuotientGroup.lift Z (f x) (by
    intro z hz
    exact (MonoidHom.mem_ker).2 (c_center_right x z hz))
  have g_mul (x y : W) : g (x*y) = g x * g y := by
    apply MonoidHom.ext
    intro t
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Z t
    exact c_left x y z
  have g_center (z : W) (hz : z ∈ Z) : g z = 1 := by
    apply MonoidHom.ext
    intro t
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z t
    exact c_center_left z y hz
  let b : V →* (V →* D) := QuotientGroup.lift Z
    { toFun := g
      map_one' := g_center 1 (one_mem Z)
      map_mul' := g_mul }
    (by intro z hz; exact MonoidHom.mem_ker.mpr (g_center z hz))
  have hb (x y : W) : (b (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z y) : G) =
      ⁅(x : G),(y : G)⁆ := rfl
  refine ⟨b, hb, ?_, ?_⟩
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
    apply Subtype.ext
    rw [hb]
    simp
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
    apply (QuotientGroup.eq_one_iff g).2
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hy := congrArg Subtype.val (hx (QuotientGroup.mk' Z y))
    rw [hb] at hy
    exact (commutatorElement_eq_one_iff_mul_comm.mp hy).symm


private theorem binary_pairing_selfDual {H V : Type*} [Group H]
    [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (ρ : H →* MulAut V)
    (f : V →* (V →* Multiplicative (ZMod 2)))
    (hrad : ∀ x, (∀ y, f x y = 1) → x = 1)
    (hinv : ∀ g x y, f (ρ g x) (ρ g y) = f x y) :
    Nonempty ((Offenders.linearize ρ).Equiv (Offenders.linearize ρ).dual) := by
  classical
  let pairing : Additive V →+ (Additive V →ₗ[ZMod 2] ZMod 2) := {
    toFun := fun a => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditiveLeft (f a.toMul))
    map_zero' := by
      ext b
      change (f 1 b.toMul).toAdd = 0
      simp
    map_add' := by
      intro a b
      ext x
      change (f (a.toMul*b.toMul) x.toMul).toAdd =
        (f a.toMul x.toMul).toAdd + (f b.toMul x.toMul).toAdd
      rw [map_mul]
      rfl }
  let linearPairing := pairing.toZModLinearMap 2
  have hlinj : Function.Injective linearPairing := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Additive.toMul.injective
    apply hrad
    intro y
    apply Multiplicative.toAdd.injective
    exact congrArg (fun l : Additive V →ₗ[ZMod 2] ZMod 2 => l (Additive.ofMul y)) hx
  let _ : Finite (Additive V →ₗ[ZMod 2] ZMod 2) :=
    Finite.of_injective (fun f : Additive V →ₗ[ZMod 2] ZMod 2 => (f : Additive V → ZMod 2))
      DFunLike.coe_injective
  have hdualcard : Nat.card (Additive V →ₗ[ZMod 2] ZMod 2) = Nat.card (Additive V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
      ← Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)]
  let e := LinearEquiv.ofBijective linearPairing (hlinj.bijective_of_nat_card_le hdualcard.le)
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  ext x y
  change (f (ρ g x.toMul) y.toMul).toAdd = (f x.toMul (ρ g⁻¹ y.toMul)).toAdd
  have hh := hinv g x.toMul (ρ g⁻¹ y.toMul)
  rw [map_inv, MulAut.apply_inv_self] at hh
  simpa only [map_inv] using congrArg Multiplicative.toAdd hh

/-- The action on the literal central quotient is self-dual through the
invariant, nondegenerate commutator pairing into the derived group of order two. -/
public theorem SpanCentralAction.selfDual {M : Type*} [Group M] {R : Subgroup M}
    {a : Vertex R} {W : Subgroup (FreeAmalgam R)} (c : SpanCentralAction a W)
    (hWS : W ≤ stabilizer R a)
    (hcard : Nat.card (⁅W,W⁆ : Subgroup (FreeAmalgam R)) = 2)
    (hcentral : ⁅W,W⁆ ≤ centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    letI := c.elementary
    Nonempty ((Offenders.linearize c.action).Equiv (Offenders.linearize c.action).dual) := by
  classical
  let := c.elementary
  let := c.finite
  let D := ⁅W,W⁆
  let V := W ⧸ center W
  let : IsCyclic D := isCyclic_of_prime_card hcard
  obtain ⟨b, hb, _, hrad⟩ := exists_derived_pairing W
    (hcentral.trans (centralizer_le hWS))
  have hinv (s : SL) (x y : V) : b (c.action s x) (c.action s y) = b x y := by
    obtain ⟨g, rfl⟩ := c.projection_surjective s
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center W) x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center W) y
    let γ := Offenders.conjugation (stabilizer R a) W c.normalized g
    rw [c.conjugation g u (γ u) rfl, c.conjugation g v (γ v) rfl]
    apply Subtype.ext
    rw [hb, hb]
    change ⁅(g : FreeAmalgam R) * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
      (g : FreeAmalgam R) * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹⁆ = _
    calc
      _ = (g : FreeAmalgam R) * ⁅(u : FreeAmalgam R),(v : FreeAmalgam R)⁆ *
          (g : FreeAmalgam R)⁻¹ := by simp only [commutatorElement_def]; group
      _ = _ := by
        rw [hcentral (commutator_mem_commutator u.property v.property) g g.property,
          mul_assoc, mul_inv_cancel, mul_one]
  let e : D ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard (by simp)
  let f : V →* (V →* Multiplicative (ZMod 2)) :=
    (MonoidHom.compHom e.toMonoidHom).comp b
  apply binary_pairing_selfDual c.action f
  · intro x hx
    apply hrad x
    intro y
    apply e.injective
    change f x y = e 1
    rw [map_one]
    exact hx y
  · intro g x y
    change e (b (c.action g x) (c.action g y)) = e (b x y)
    rw [hinv]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
