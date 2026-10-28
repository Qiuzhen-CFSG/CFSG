module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic.Cubic
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.Actors
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms
public import Mathlib.GroupTheory.PGroup

/-!
# Transport to the marked source code action

The proved comparison with Aut(M22) constructs the pair-stabilizer marking
needed by the minimum-actor-rank theorem. Cubic displacement is transported
through a source homomorphism with two-group kernel: disjointness of the
kernel and a cubic subgroup proves that the cubic image still has order three.
Thus this applies to the original action of M, as well as its faithful quotient.

Source: Aschbacher–Smith, Proposition 8.2.2(1), printed p.715 (PDF p.732),
using the source module marking from Chapter 7 and H.13.1. The marking is an
explicit group map and equivariant linear isomorphism, not a family tag.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
open Subgroup Representation.BinaryOffender MathieuCode
open Sporadic.Mathieu (M22)

private theorem cubic_image_card {G K : Type*} [Group G] [Group K]
    (f : G →* K) (hker : IsPGroup 2 f.ker)
    (D : Subgroup G) (hD : Nat.card D = 3) : Nat.card (D.map f) = 3 := by
  have hp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hi : Function.Injective (f.comp D.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp
      (hp.disjoint_of_coprime hker (by decide)) x.property hx
  let e : D ≃* D.map f := MulEquiv.ofBijective (f.subgroupMap D) ⟨fun x y h =>
    hi (congrArg Subtype.val h), f.subgroupMap_surjective D⟩
  exact (Nat.card_congr e.toEquiv).symm.trans hD

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- A genuine Aut(M22) marking yields the minimum actor rank in 3.1.9(6).
The pair-stabilizer marking is constructed by the proved automorphism comparison. -/
theorem marked_code_actor_rank [Finite G]
    (ρ : Representation (ZMod 2) G W) (e : G ≃* MulAut M22)
    (E : W ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ g w, E (ρ g w) = m22AutCodeRepresentation (e g) (E w))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hr : actionRatio ρ A ≤ 2) :
    2 ≤ rank A := by
  let f := m22PairStabilizerEquivAut.symm.toMonoidHom.comp e.toMonoidHom
  exact code_actor_rank_of_equivariant ρ f
    (m22PairStabilizerEquivAut.symm.injective.comp e.injective) E hE A hA hr

/-- Cubic displacement on the original source module, allowing its actual
centralizer kernel to be a two-group. This applies to the subgroups of C_M(Z). -/
theorem marked_code_cubic_displacement
    (ρ : Representation (ZMod 2) G W) (f : G →* MulAut M22)
    (hker : IsPGroup 2 f.ker) (E : W ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ g w, E (ρ g w) = m22AutCodeRepresentation (f g) (E w))
    (D : Subgroup G) (hD : Nat.card D = 3) : fixedCodim ρ D = 6 := by
  let j := m22PairStabilizerEquivAut.symm.toMonoidHom
  have hc : Nat.card (D.map (j.comp f)) = 3 := by
    rw [← Subgroup.map_map, Subgroup.card_map_of_injective
      m22PairStabilizerEquivAut.symm.injective]
    exact cubic_image_card f hker D hD
  rw [fixedCodim_map_equivariant ρ m22OuterCodeRepresentation (j.comp f) E hE]
  exact (outer_cubic_displacement _ hc).1

/-- The dual in 3.1.9 has the same cubic displacement on the literal actor. -/
theorem marked_code_dual_cubic_displacement [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (f : G →* MulAut M22)
    (hker : IsPGroup 2 f.ker) (E : W ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ g w, E (ρ g w) = m22AutCodeRepresentation (f g) (E w))
    (D : Subgroup G) (hD : Nat.card D = 3) : fixedCodim ρ.dual D = 6 := by
  have hc := marked_code_cubic_displacement ρ f hker E hE D hD
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  obtain ⟨g, rfl⟩ := D.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  rwa [fixedCodim_zpowers_dual]

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
