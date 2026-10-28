module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels

/-!
# The concrete binary projective parabolics are symmetric groups

The point and line parabolics in PSL₃(2) are each isomorphic to S₄.
The line identification comes from the faithful action of its SL₃(2)
preimage on the four vectors with last coordinate one. The point
identification uses the coordinate-reversing inverse-transpose automorphism.
These actions and their surjectivity are proved in `SymmetricModels`.

Here both identifications are transported through the restriction of the
actual central quotient map `project`. Its injectivity over F₂ identifies
each coordinate stabilizer with its projective image. The compatibility
lemmas record the resulting maps on projected matrices.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.4
and I.5.7, printed pp. 420–421, the binary projective-plane local model.
-/

namespace Matrix.PSL3Two

/-- The concrete projective point stabilizer is the symmetric group on four letters. -/
public noncomputable def pointParabolicEquivS4 : pointParabolic ≃* Equiv.Perm (Fin 4) :=
  (pointParabolicSL.equivMapOfInjective project project_injective).symm.trans
    MarkedAutomorphisms.pointEquivSymmetric

/-- The concrete projective line stabilizer is the symmetric group on four letters. -/
public noncomputable def lineParabolicEquivS4 : lineParabolic ≃* Equiv.Perm (Fin 4) :=
  (lineParabolicSL.equivMapOfInjective project project_injective).symm.trans
    MarkedAutomorphisms.lineEquivSymmetric

@[simp] public theorem pointParabolicEquivS4_project (g : pointParabolicSL) :
    pointParabolicEquivS4
      ⟨project (g : SL), Subgroup.mem_map_of_mem project g.property⟩ =
        MarkedAutomorphisms.pointEquivSymmetric g :=
  congrArg MarkedAutomorphisms.pointEquivSymmetric
    ((pointParabolicSL.equivMapOfInjective project project_injective).symm_apply_apply g)

@[simp] public theorem lineParabolicEquivS4_project (g : lineParabolicSL) :
    lineParabolicEquivS4
      ⟨project (g : SL), Subgroup.mem_map_of_mem project g.property⟩ =
        MarkedAutomorphisms.lineEquivSymmetric g :=
  congrArg MarkedAutomorphisms.lineEquivSymmetric
    ((lineParabolicSL.equivMapOfInjective project project_injective).symm_apply_apply g)

end Matrix.PSL3Two
