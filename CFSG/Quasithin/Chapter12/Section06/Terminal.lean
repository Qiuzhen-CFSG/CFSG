module

public import Theory.LinearAlgebra.DisplacementFiltration
public import Theory.Representation.SubspaceQuotient
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The final displacement contradiction in Section 12.6

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of Theorem 12.6.34, printed p.838 (PDF p.855).
The source first identifies `H/O₂(H)` with `S₅ × S₃`, decomposes `U_H/V₁`
into two isomorphic modules, and obtains a geometric actor `b` using F.9.16.
For this same actor, the filtration bound gives displacement at most three,
and the two summands give displacement at least four.

The theorems below prove this terminal linear and commutator argument. They
leave the earlier local analysis, the decomposition, and the geometric actor
explicit. Those inputs still have to be constructed for the source theorem.
Normality and conjugation here concern the local group `H`, not the ambient
simple group of the classification.
-/

public section
open Module

namespace CFSG.Quasithin.Chapter12.Section06
variable {H U W : Type*} [Group H]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The linear contradiction on the literal quotient `U/Z`. The geometric
filtration contributes at most three dimensions of displacement, whereas
the two invariant copies each contribute at least two.

In the source, `U = U_H`, `Z = V₁`, `D = D_H` and `A = A₁`. The F.9 geometry
supplies the bounds on `D` and `A` and the commutator containment. The final
`S₅ × S₃` action analysis supplies the marked decomposition and factor bound. -/
theorem terminal_contradiction_of_quotient_action (ρ : Representation (ZMod 2) H U)
    (Z : Subrepresentation ρ) (D A : Submodule (ZMod 2) U) (b : H)
    (s : W →ₗ[ZMod 2] W)
    (e : (U ⧸ Z.toSubmodule) ≃ₗ[ZMod 2] W × W)
    (he : ∀ u, e (Z.quotientRepresentation b u) = (s (e u).1, s (e u).2))
    (hD : finrank (ZMod 2) (U ⧸ D) ≤ 2)
    (hA : finrank (ZMod 2) A ≤ 1)
    (hcomm : ∀ u ∈ D, ρ b u - u ∈ A)
    (hs : 2 ≤ finrank (ZMod 2) (s - LinearMap.id).range) : False := by
  have hupper := LinearMap.finrank_range_le_of_surjective_intertwining (ρ b - LinearMap.id)
    (Z.quotientRepresentation b - LinearMap.id) Z.toSubmodule.mkQ
    Z.toSubmodule.mkQ_surjective (by
      intro u
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
        Subrepresentation.quotientRepresentation_mk]) D A hcomm
  have hlower := LinearMap.finrank_range_add_le_of_intertwining_prod
    (Z.quotientRepresentation b - LinearMap.id) (s - LinearMap.id) (s - LinearMap.id) e (by
      intro u
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, he]
      rfl)
  omega
end CFSG.Quasithin.Chapter12.Section06

open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup
variable {H W : Type*} [Group H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Application to the actual subgroup `U_H` of the local group `H`. The
representation is tied to ambient conjugation by `hρ`, and `hcomm` uses the
images of the actual subgroups under the inclusion `U ↪ H`. In particular,
this converts the source's `[D_H,b] ≤ A₁` to the displacement hypothesis on
`U_H/V₁`, retaining the original quotient and the commutator convention.

The action, decomposition, and geometric bounds are explicit inputs; this
helper does not claim that these witnesses exist under Hypothesis 12.2.3. -/
theorem terminal_contradiction_of_conjugation (U : Subgroup H) [Finite U] [IsElementaryAbelian 2 U]
    (ρ : Representation (ZMod 2) H (Additive U))
    (hρ : ∀ (a : H) (u : Additive U),
      ((ρ a u).toMul : H) = a * (u.toMul : H) * a⁻¹)
    (Z : Subrepresentation ρ) (D A : Subgroup U) (b : H)
    (s : W →ₗ[ZMod 2] W)
    (e : (Additive U ⧸ Z.toSubmodule) ≃ₗ[ZMod 2] W × W)
    (he : ∀ u, e (Z.quotientRepresentation b u) = (s (e u).1, s (e u).2))
    (hD : finrank (ZMod 2)
      (Additive U ⧸ (AddSubgroup.toZModSubmodule 2 D.toAddSubgroup)) ≤ 2)
    (hA : finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2 A.toAddSubgroup) ≤ 1)
    (hcomm : ⁅D.map U.subtype, zpowers b⁆ ≤ A.map U.subtype)
    (hs : 2 ≤ finrank (ZMod 2) (s - LinearMap.id).range) : False := by
  apply terminal_contradiction_of_quotient_action ρ Z (AddSubgroup.toZModSubmodule 2 D.toAddSubgroup)
    (AddSubgroup.toZModSubmodule 2 A.toAddSubgroup) b s e he hD hA _ hs
  intro u hu
  change (ρ b u - u).toMul ∈ A
  have hc : ⁅b, (u.toMul : H)⁆ ∈ A.map U.subtype := by
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator (mem_zpowers b) ⟨u.toMul, hu, rfl⟩)
  obtain ⟨a, ha, haeq⟩ := hc
  have ha' : a = (ρ b u - u).toMul := by
    apply Subtype.ext
    calc
      (a : H) = ⁅b, (u.toMul : H)⁆ := haeq
      _ = ((ρ b u - u).toMul : H) := by
        simp only [commutatorElement_def, toMul_sub,
          div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, hρ]
  rwa [← ha']
end CFSG.Quasithin.Chapter12.Section06

end
