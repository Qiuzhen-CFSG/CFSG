module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceSetup
public import Theory.Representation.BinaryNaturalDual.Transport

/-!
# The source subgroups and module spaces under the constructed H.9 model

The layer, point stabilizer and embedded two-residual map to their literal
coordinate counterparts. The fixed and moving subspaces and the corank core
map under the same linear comparison. For nonsingular vectors the residual
is the inner stabilizer and the moving module is ker(f) ⊕ ann(x).

Source: Aschbacher–Smith H.9.1 and E.3.30. These are change-of-model
identities for the source setup, not additional model hypotheses.
-/

public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.VectorStabilizers
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

/-- The actual source layer maps onto the inner automorphism subgroup. -/
theorem layer_map : (componentLayer M).map S.model.group.toMonoidHom =
    MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup n) := by
  ext a
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (S.model.inner_iff g).mpr hg
  · intro ha
    refine ⟨S.model.group.symm a, ?_, S.model.group.apply_symm_apply a⟩
    exact (S.model.inner_iff _).mp (by simpa using ha)

/-- The full source stabilizer has exactly the coordinate image. -/
theorem stabilizer_map (v : V) : (S.stabilizer v).map S.model.group.toMonoidHom =
    fullStabilizer (AutomorphismModel.coordinateAction S.degree) (S.model.coordinates v) :=
  Transport.stabilizer_map S.representation _ S.model.group S.model.coordinates
    S.model.equivariant v

/-- The same map preserves the layer centralizer. -/
theorem innerStabilizer_map (v : V) :
    (S.innerStabilizer v).map S.model.group.toMonoidHom =
      VectorStabilizers.innerStabilizer (AutomorphismModel.coordinateAction S.degree)
        (S.model.coordinates v) := by
  rw [innerStabilizer, Subgroup.map_inf _ _ _ S.model.group.injective,
    S.layer_map, S.stabilizer_map]
  rfl

/-- Residual transport respects the relative subgroup and its embedding in M. -/
theorem residual_map (v : V) : (S.residual v).map S.model.group.toMonoidHom =
    innerResidual (AutomorphismModel.coordinateAction S.degree) (S.model.coordinates v) := by
  let := S.finite_group
  rw [residual, Subgroup.map_embedded_pResidual, S.innerStabilizer_map]
  rfl

/-- Fixed spaces of every source actor map under the same marked comparison. -/
theorem fixed_map (A : Subgroup M) :
    (S.fixed A).map S.model.coordinates.toLinearMap =
      Representation.BinaryOffender.fixedSpace
        (AutomorphismModel.coordinateAction S.degree).representation
        (A.map S.model.group.toMonoidHom) :=
  Transport.fixed_map S.representation _ S.model.group S.model.coordinates
    S.model.equivariant A

/-- The fixed-vector convention used by the adapted-coordinate theorem is identical. -/
theorem fixed_map_adapted (A : Subgroup M) :
    (S.fixed A).map S.model.coordinates.toLinearMap =
      AdaptedPair.fixedVectors (AdaptedPair.linearAction
        (AutomorphismModel.coordinateAction S.degree)) (A.map S.model.group.toMonoidHom) := by
  rw [S.fixed_map]
  ext w
  exact ⟨fun hw g hg => hw ⟨g,hg⟩, fun hw g => hw g g.property⟩

/-- The source fixed-space dimension is the coordinate fixed-space dimension. -/
theorem fixed_finrank (A : Subgroup M) :
    Module.finrank (ZMod 2) (S.fixed A) =
      Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace
        (AutomorphismModel.coordinateAction S.degree).representation
        (A.map S.model.group.toMonoidHom)) :=
  Transport.fixed_finrank S.representation _ S.model.group S.model.coordinates
    S.model.equivariant A

/-- The actual source commutator space maps to the residual commutator space. -/
theorem moving_map (v : V) : (S.moving v).map S.model.coordinates.toLinearMap =
    Representation.Coinvariants.ker
      (residualRepresentation (AutomorphismModel.coordinateAction S.degree)
        (S.model.coordinates v)) := by
  rw [moving, Transport.commutator_map S.representation _ S.model.group
    S.model.coordinates S.model.equivariant, S.residual_map]
  rfl

/-- The generated core is transported for every actor and every corank. -/
theorem core_map (A : Subgroup M) (k : ℕ) :
    (generatedCore (S.representation.comp A.subtype) k).map S.model.coordinates.toLinearMap =
      generatedCore ((AutomorphismModel.coordinateAction S.degree).representation.comp
        (A.map S.model.group.toMonoidHom).subtype) k := by
  let := S.finite_group
  exact Transport.core_map S.representation _ S.model.group S.model.coordinates
    S.model.equivariant A k

/-- In the nonsingular case the source two-residual is the full layer centralizer. -/
theorem residual_eq_innerStabilizer {v : V} (hv : S.quadratic v = 1) :
    S.residual v = S.innerStabilizer v := by
  have hv' : (S.model.coordinates v).2 (S.model.coordinates v).1 = 1 := by
    simpa only [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv
  apply Subgroup.map_injective (f := S.model.group.toMonoidHom) S.model.group.injective
  rw [S.residual_map, S.innerStabilizer_map]
  exact innerResidual_eq_innerStabilizer S.degree _ (x := (S.model.coordinates v).1)
    (f := (S.model.coordinates v).2) hv'

/-- For a nonsingular vector the actual moving module is the two orthogonal complements. -/
theorem moving_map_nonsingular {v : V} (hv : S.quadratic v = 1) :
    (S.moving v).map S.model.coordinates.toLinearMap =
      AdaptedPair.movingSpace (S.model.coordinates v) := by
  have hv' : (S.model.coordinates v).2 (S.model.coordinates v).1 = 1 := by
    simpa only [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv
  rw [S.moving_map,
    residual_commutator S.degree _ (x := (S.model.coordinates v).1)
      (f := (S.model.coordinates v).2) hv']
  ext w
  rw [AdaptedPair.mem_movingSpace]
  rfl

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
