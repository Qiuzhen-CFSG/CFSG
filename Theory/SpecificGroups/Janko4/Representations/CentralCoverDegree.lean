module

public import Theory.Representation.BinaryCoprimeDegree.CentralQuotient
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.CoordinateEmbedding
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.MatrixRelations

/-!
# Binary degree at least 110 for perfect central covers of J₄

The certified ATLAS eleven-local words embed the coordinate group of order
11³ in the actual binary J₄ model. Its generators do not commute, so it is
extraspecial. The central-quotient degree bound therefore gives degree at
least 11 * ord₁₁(2) = 110 for any faithful irreducible binary representation
of a finite perfect central cover of this model.

The argument includes covers whose center has eleven-torsion, using the
Schur-field and determinant bound in that case. It needs no computation of
the J₄ multiplier or catalogue of irreducible representations.

Sources: the concrete words are ATLAS J4G1-max7W1, with certificates and
attribution in `Elevens.LocalCertificates.MatrixRelations`; the extraspecial
degree argument is Aschbacher–Smith G.7.1(2), printed p.347. This supplies the
J₄ degree-window exclusion needed in K.4, printed p.457.
-/

public section
namespace Janko4.BinaryDegree
open Subgroup Representation.BinaryCoprimeDegree
open Simplicity.Elevens Simplicity.Elevens.LocalCoordinates

private theorem coordinate_extraspecial : IsExtraspecial 11 Coord := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply IsExtraspecial.of_noncommutative_card_prime_cube (by
    simpa only [show 11 ^ 3 = 1331 from rfl] using card_coord)
  intro h
  let := h
  exact (by decide : X * Y ≠ Y * X) (mul_comm' X Y)

private theorem exists_extraspecial_eleven :
    ∃ P : Subgroup Model, IsExtraspecial 11 P ∧ Nat.card P = 11 ^ 3 := by
  obtain ⟨f, hf, _hX, _hY, _hZ⟩ := coordinate_embedding_of_relations
    _ _ _ (matrix_elevenRelations matrixA_mul_self matrixB_pow_four)
  let e : Coord ≃* f.range := MonoidHom.ofInjective hf
  refine ⟨f.range, IsExtraspecial.of_mulEquiv e coordinate_extraspecial, ?_⟩
  exact (Nat.card_congr e.toEquiv).symm.trans card_coord

/-- Every faithful irreducible binary representation of a finite perfect
central cover of the actual J₄ model has degree at least 110. -/
theorem faithful_irreducible_central_cover_degree
    {L V : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (e : L ⧸ center L ≃* Model) :
    110 ≤ Module.finrank (ZMod 2) V := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨P, hP, hcP⟩ := exists_extraspecial_eleven
  let : IsExtraspecial 11 P := hP
  let f : L →* Model := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hsurj : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center L))
  have hker : f.ker = center L := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker = center L
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven, Nat.reduceMul] using
    extraspecial_central_quotient_degree ρ hf f hsurj hker.le (by decide : 11 ≠ 2) P hcP

end Janko4.BinaryDegree
