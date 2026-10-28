module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.NormLattice.Coordinates.Construction.Embeddings
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.NormLattice.Coordinates.Construction.CentralProduct
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.NormLattice.Coordinates.Construction.Product

/-!
# Construction of the actual component-pair coordinates

The two-or-four component orbit is partitioned into pairs oriented by the
marked involution. Multiplication of the commuting component embeddings gives
coordinates on the literal quotient by the orbit's intrinsic center. The norm
formula maps each chosen norm generator to an equal-coordinate singleton;
these generate the product of diagonals. Finally actual B-conjugation by
`r_j * r_i⁻¹` transports the entire pair factor from i to j.

Source: GLS2, Chapter B, Lemmas 3.25--3.27; Chapter G, Theorem 25.14,
Steps 2--3. This constructs the shared `NormPairCoordinates` interface without
using recognition, diagonal maximality, or the centralizer-layer identification.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}
  {h : Hypotheses ρ L B a}
namespace PairConstruction
namespace Frame

/-- Assemble the quotient, norm image, and actual pair action from oriented component embeddings. -/
theorem coordinates_exists (d : Frame h) : Nonempty (NormPairCoordinates h) := by
  classical
  obtain ⟨e₀,he₀⟩ := centralProduct_quotient_coordinates d.embedding
    d.embedding_injective d.embedding_commute d.embedding_generate
  let S := L ⧸ center L
  let q : L →* S := QuotientGroup.mk' (center L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let e : (componentOrbit L B ⧸ center (componentOrbit L B)) ≃*
      (Fin d.count → S × S) := e₀.trans pairedEquiv
  let ψ : componentOrbit L B →* (Fin d.count → S × S) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center (componentOrbit L B)))
  have hEmb (i : Fin d.count) (s : Bool) (x : L) :
      ψ (d.embedding (i,s) x) = axisSingle i s (q x) := by
    change pairedEquiv (e₀ (QuotientGroup.mk' _ (d.embedding (i,s) x))) = _
    rw [he₀, pairedEquiv_single]
    exact (axisSingle_apply i s (q x)).symm
  have hAxis (i : Fin d.count) (s : Bool) :
      (d.embedding (i,s)).range.map ψ = (axisSingle (S := S) i s).range := by
    rw [MonoidHom.map_range]
    have he : ψ.comp (d.embedding (i,s)) = (axisSingle i s).comp q := by
      apply MonoidHom.ext
      intro x
      exact hEmb i s x
    rw [he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hq, ← MonoidHom.range_eq_map]
  have hNorm (i : Fin d.count) :
      (d.normEmbedding i).range.map ψ = (diagonalSingle (S := S) i).range := by
    rw [MonoidHom.map_range]
    have he : ψ.comp (d.normEmbedding i) = (diagonalSingle i).comp q := by
      apply MonoidHom.ext
      intro x
      funext j
      change (ψ (d.normEmbedding i x) j) = _
      rw [d.normEmbedding_apply, map_mul, hEmb, hEmb]
      by_cases hji : j = i
      · subst j; simp [axisSingle, diagonalSingle]
      · simp [axisSingle, diagonalSingle, Pi.mulSingle_eq_of_ne hji]
    rw [he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hq, ← MonoidHom.range_eq_map]
  have hNormImage : (h.normDiagonal.subgroupOf (componentOrbit L B)).map ψ =
      PairedProduct.diagonal (Fin d.count) S := by
    rw [← d.normEmbedding_generate, Subgroup.map_iSup]
    simp_rw [hNorm]
    exact diagonal_generate
  let P (i : Fin d.count) : Subgroup (componentOrbit L B) :=
    (d.embedding (i,false)).range ⊔ (d.embedding (i,true)).range
  have hP (i : Fin d.count) : (P i).map ψ = PairedProduct.factor (Fin d.count) S i := by
    rw [show P i = _ ⊔ _ from rfl, Subgroup.map_sup, hAxis, hAxis]
    exact axis_generate i
  have hTrans (i j : Fin d.count) :
      (P i).map (h.orbitConjugation (d.rep j * (d.rep i)⁻¹)).toMonoidHom = P j := by
    have he (s : Bool) :
        (h.orbitConjugation (d.rep j * (d.rep i)⁻¹)).toMonoidHom.comp
          (d.embedding (i,s)) = d.embedding (j,s) := by
      apply MonoidHom.ext
      intro x
      exact d.conjugation_embedding i j s x
    simp only [P, Subgroup.map_sup, MonoidHom.map_range, he]
  refine ⟨⟨d.count,d.pos,d.le_two,e,hNormImage,?_⟩⟩
  intro i j
  let b := d.rep j * (d.rep i)⁻¹
  refine ⟨b, ?_⟩
  rw [← hP i, ← hP j, map_map]
  have he : (h.orbitCoordinateAction e b).toMonoidHom.comp ψ =
      ψ.comp (h.orbitConjugation b).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact h.orbitCoordinateAction_apply e b x
  rw [he, ← map_map, hTrans]
end Frame
end PairConstruction

/-- The source four-group hypotheses supply literal norm-pair coordinates.
Neither generation of the ambient group nor a two-core hypothesis is needed. -/
theorem Hypotheses.normPairCoordinates_nonempty [Finite G]
    (h : Hypotheses ρ L B a) : Nonempty (NormPairCoordinates h) := by
  obtain ⟨d⟩ := PairConstruction.frame_exists h
  exact d.coordinates_exists

end Representation.QuadraticFourGroup

end
