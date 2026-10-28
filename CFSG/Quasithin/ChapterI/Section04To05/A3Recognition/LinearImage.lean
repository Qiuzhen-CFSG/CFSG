module

public import CFSG.Quasithin.ChapterI.Section04To05.A3Recognition.Reconstruction
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
/-!
# The full linear image in A₃ recognition

The original point stabilizer embeds in the actual stabilizer of its quotient
vector. Its PSL₃(2) quotient and nontrivial two-core force that embedding to
be onto: conjugation is the full automorphism action on the ambient
elementary-eight displacement group. Point transitivity then gives every
linear automorphism of the four-dimensional quotient, and faithfulness
produces an actual equivalence to PSL₄(2).

The final equivalence is conditional only on the earlier incidence facts
in GeometryData and the nontrivial core from I.5.7(2). Their construction
from a bare DSystem remains with the geometry producer and final assembly.
No surjectivity, nonzero quotient, recognition or model-order premise is added.

Source: Aschbacher–Smith I.5.10 and the A₃ branch of I.5.1, combined manuscript
of 1 March 2004, printed p.422. The last equality recognizes G itself;
the vertex group G₀ is its point stabilizer.
-/

@[expose] public section

namespace Quasithin.I5.A3Recognition
open Module
open Theory.LinearAlgebra
variable {G : Type*} [Group G] (S : DSystem .A3 G)

noncomputable def stabilizerHom : S.family 0 →*
    BinaryFivePointStabilizer.stabilizer (pointMap S S.basePoint) where
  toFun g := ⟨linearAction g.val, by
    change g.val • pointMap S S.basePoint = pointMap S S.basePoint
    rw [← pointMap_equivariant]
    have hg : g.val • S.basePoint = S.basePoint := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [S.stabilizer_basePoint]
      exact g.property
    rw [hg]⟩
  map_one' := by apply Subtype.ext; exact map_one linearAction
  map_mul' g h := by apply Subtype.ext; exact map_mul linearAction g.val h.val

variable {S}
theorem stabilizerHom_injective (d : GeometryData S) :
    Function.Injective (stabilizerHom S) := by
  intro g h he
  apply Subtype.ext
  exact linearAction_injective d (congrArg Subtype.val he)

theorem stabilizerHom_surjective (d : GeometryData S) (hQ : S.Q 0 ≠ ⊥) :
    Function.Surjective (stabilizerHom S) := by
  let : Finite S.Point := d.finite_points
  have hc : pCore 2 (S.family 0) ≠ ⊥ := by
    intro h
    apply hQ
    simp only [DSystem.Q, Subgroup.pCoreIn, h, Subgroup.map_bot]
  apply BinaryFourPointStabilizer.surjective_of_quotient
    (pointMap S S.basePoint) (pointMap_nonzero d S.basePoint)
    (quotient_finrank d) (stabilizerHom S) (stabilizerHom_injective d) _ hc
  obtain ⟨e⟩ := S.point_A3 rfl
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.PSL3Two.card_PSL

/-- The faithful quotient action has the full linear group as its image. -/
theorem linearAction_surjective (d : GeometryData S) (hQ : S.Q 0 ≠ ⊥) :
    Function.Surjective (linearAction (S := S)) := by
  intro a
  have hz := pointMap_nonzero d S.basePoint
  obtain ⟨x, hx⟩ := (pointMap_bijective d).surjective
    ⟨a (pointMap S S.basePoint), by simpa only [ne_eq, a.map_eq_zero_iff] using hz⟩
  have hx' : pointMap S x = a (pointMap S S.basePoint) := congrArg Subtype.val hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S.basePoint x
  have hga : linearAction g (pointMap S S.basePoint) = a (pointMap S S.basePoint) := by
    change g • pointMap S S.basePoint = _
    rw [← pointMap_equivariant, hg, hx']
  let b : BinaryFivePointStabilizer.stabilizer (pointMap S S.basePoint) :=
    ⟨(linearAction g)⁻¹ * a, by
      change (linearAction g).symm (a (pointMap S S.basePoint)) = _
      rw [← hga, LinearEquiv.symm_apply_apply]⟩
  obtain ⟨h, hh⟩ := stabilizerHom_surjective d hQ b
  have hh' : linearAction h.val = (linearAction g)⁻¹ * a := congrArg Subtype.val hh
  refine ⟨g * h.val, ?_⟩
  rw [map_mul, hh', mul_inv_cancel_left]

noncomputable def equivLinearGroup (d : GeometryData S) (hQ : S.Q 0 ≠ ⊥) :
    G ≃* (V S ≃ₗ[ZMod 2] V S) :=
  MulEquiv.ofBijective linearAction
    ⟨linearAction_injective d, linearAction_surjective d hQ⟩


/-- Conditional I.5.10 / the A₃ conclusion: an actual equivalence to PSL₄(2).
The geometry and the nontrivial local core are earlier-source obligations. -/
noncomputable def equivPSL4_of_geometry (d : GeometryData S) (hQ : S.Q 0 ≠ ⊥) :
    G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) := by
  let : Finite S.Point := d.finite_points
  exact (equivLinearGroup d hQ).trans (BinaryFourPointStabilizer.equivPSL4 (quotient_finrank d))

end Quasithin.I5.A3Recognition
