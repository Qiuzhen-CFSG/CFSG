module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# The commutator pairing modulo a centralizing layer

If the commutators lie in D and [D,G] lies in Z, commutators modulo Z
are multiplicative in both variables. The target is the literal quotient
D/(Z.subgroupOf D), with its supplied normality and commutativity instances.
The two commutator product identities prove the homomorphism laws because
conjugation is trivial on that quotient.

This is the class-two quotient pairing used in Parrott's core centralizer
counts (1972), pp.673–674.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

/-- The literal quotient commutator is a homomorphism in both variables. -/
public theorem exists_central_quotient_commutator_pairing
    {G : Type*} [Group G] (D Z : Subgroup G) [D.Normal]
    [(Z.subgroupOf D).Normal] [IsMulCommutative (D ⧸ Z.subgroupOf D)]
    (hD : _root_.commutator G ≤ D) (hcomm : ⁅D, (⊤ : Subgroup G)⁆ ≤ Z) :
    ∃ f : G →* (G →* (D ⧸ Z.subgroupOf D)),
      ∀ x y : G, f x y = QuotientGroup.mk' (Z.subgroupOf D)
        ⟨⁅x,y⁆, hD (commutator_mem_commutator (mem_top x) (mem_top y))⟩ := by
  let q := QuotientGroup.mk' (Z.subgroupOf D)
  have hmem (x y : G) : ⁅x,y⁆ ∈ D :=
    hD (commutator_mem_commutator (mem_top x) (mem_top y))
  have hinv (g : G) (d : D) :
      q ⟨g * d * g⁻¹, (inferInstance : D.Normal).conj_mem d d.property g⟩ = q d := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (g * (d : G) * g⁻¹) / (d : G) ∈ Z
    have hm : ⁅g, (d : G)⁆ ∈ Z := by
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top g) d.property
    simpa only [div_eq_mul_inv, commutatorElement_def] using hm
  let f : G →* (G →* (D ⧸ Z.subgroupOf D)) := {
    toFun x := {
      toFun y := q ⟨⁅x,y⁆, hmem x y⟩
      map_one' := by
        rw [show (⟨⁅x,1⁆, hmem x 1⟩ : D) = 1 from Subtype.ext (by simp), map_one]
      map_mul' y z := by
        have heq : (⟨⁅x,y*z⁆, hmem x (y*z)⟩ : D) =
            ⟨⁅x,y⁆, hmem x y⟩ *
              ⟨y * ⁅x,z⁆ * y⁻¹, (inferInstance : D.Normal).conj_mem _ (hmem x z) y⟩ := by
          apply Subtype.ext
          simpa only [Subgroup.coe_mul, mul_assoc] using commutatorElement_mul_right_eq_mul_conj x y z
        rw [heq, map_mul, hinv y ⟨⁅x,z⁆, hmem x z⟩] }
    map_one' := by
      apply MonoidHom.ext
      intro y
      change q ⟨⁅1,y⁆, _⟩ = 1
      rw [show (⟨⁅1,y⁆, hmem 1 y⟩ : D) = 1 from Subtype.ext (by simp), map_one]
    map_mul' x y := by
      apply MonoidHom.ext
      intro z
      have heq : (⟨⁅x*y,z⁆, hmem (x*y) z⟩ : D) =
          ⟨x * ⁅y,z⁆ * x⁻¹, (inferInstance : D.Normal).conj_mem _ (hmem y z) x⟩ *
            ⟨⁅x,z⁆, hmem x z⟩ := by
        apply Subtype.ext
        exact commutatorElement_mul_left_eq_conj_mul x y z
      change q ⟨⁅x*y,z⁆, _⟩ = q ⟨⁅x,z⁆, _⟩ * q ⟨⁅y,z⁆, _⟩
      rw [heq, map_mul, hinv x ⟨⁅y,z⁆, hmem y z⟩, mul_comm] }
  exact ⟨f, fun _ _ => rfl⟩

end Subgroup
