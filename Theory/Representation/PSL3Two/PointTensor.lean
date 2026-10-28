module

public import Theory.Representation.PSL3Two.FanoCoreStructure
public import Theory.Representation.InvertedCubicTensor.BinaryPlane
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates

/-!
# Marked point seeds for SL₃(2) × S₃

The point permutation module tensored with the binary natural S₃-module is
an explicit representation on the actual seven Fano points. A generating
point seed is a binary plane stable under S₃, fixed by the marked point
parabolic in SL₃(2), and with fixed-point-free cubic action.

Parabolic invariance of such a plane already implies pointwise fixation by
the first factor: the inverted-cubic multiplicity space is a binary line.
The definitions retain the point marking throughout; no graph automorphism
or choice of natural/dual orientation is involved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed p.957; the Fano permutation module is H.5.1–3.
-/

@[expose] public section
open Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct
namespace BinaryLinearThree.PointTensor

abbrev Actor := Group × S₃

/-- The literal point permutation module tensored with the natural S₃-module. -/
noncomputable def pointTensor : Representation (ZMod 2) Actor
    ((BinaryPermutation.Full Point) ⊗[ZMod 2] BinaryPermutation.core (Fin 3)) :=
  Representation.tprod
    (FanoCoreStructure.pointRepresentation.comp (MonoidHom.fst Group S₃))
    ((BinaryPermutation.coreRepresentation (Fin 3)).comp (MonoidHom.snd Group S₃))

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- Linear data on an actual generating plane. This does not assume a module
quotient, a chief section, or its natural/dual orientation. -/
structure IsGeneratingSeed (ρ : Representation (ZMod 2) Actor U)
    (D : Submodule (ZMod 2) U) : Prop where
  dimension_two : Module.finrank (ZMod 2) D = 2
  symmetric_stable : ∀ s : S₃, ∀ v ∈ D, ρ (1, s) v ∈ D
  point_fixed : ∀ p ∈ Matrix.PSL3Two.pointParabolicSL, ∀ v ∈ D, ρ (p, 1) v = v
  cubic_fixed_free : ∀ v ∈ D, ρ (1, cubic) v = v → v = 0
  generates : ∀ N : Subrepresentation ρ, D ≤ N.toSubmodule → N = ⊤

/-- On a binary plane the full second factor forces the commuting point
parabolic to fix every vector. Mere invariance is the input. -/
theorem point_fixed_of_parabolic_plane [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Actor U) (D : Submodule (ZMod 2) U)
    (hd : Module.finrank (ZMod 2) D = 2)
    (hstable : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL.prod (⊤ : Subgroup S₃),
      ∀ v ∈ D, ρ g v ∈ D)
    (hc : ∀ v ∈ D, ρ (1, cubic) v = v → v = 0) :
    ∀ p ∈ Matrix.PSL3Two.pointParabolicSL, ∀ v ∈ D, ρ (p, 1) v = v := by
  let σ : Representation (ZMod 2) (Matrix.PSL3Two.pointParabolicSL × S₃) D := {
    toFun g := (ρ (g.1.val, g.2)).restrict (fun {v} hv =>
      hstable (g.1.val, g.2) ⟨g.1.property, Subgroup.mem_top _⟩ v hv)
    map_one' := by ext v; exact LinearMap.congr_fun ρ.map_one v.val
    map_mul' g h := by ext v; exact LinearMap.congr_fun (ρ.map_mul (g.1.val, g.2) (h.1.val, h.2)) v.val }
  have hfree : fixedSpace (rightAction σ) (alternatingGroup (Fin 3)) = ⊥ := by
    apply (fixedFree_iff_fixedSpace_eq_bot (rightAction σ)).mp
    intro v hv
    apply Subtype.ext
    exact hc v.val v.property (congrArg Subtype.val hv)
  intro p hp v hv
  exact congrArg Subtype.val
    (left_fixed_of_finrank_two σ hd hfree (⟨p, hp⟩ : Matrix.PSL3Two.pointParabolicSL)
      (⟨v, hv⟩ : D))

/-- The generating point-seed contract follows from parabolic invariance,
the actual two-dimensional seed and its cubic action. -/
theorem generatingSeed_of_parabolic_plane [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Actor U) (D : Submodule (ZMod 2) U)
    (hd : Module.finrank (ZMod 2) D = 2)
    (hstable : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL.prod (⊤ : Subgroup S₃),
      ∀ v ∈ D, ρ g v ∈ D)
    (hc : ∀ v ∈ D, ρ (1, cubic) v = v → v = 0)
    (hgen : ∀ N : Subrepresentation ρ, D ≤ N.toSubmodule → N = ⊤) :
    IsGeneratingSeed ρ D :=
  ⟨hd, fun s => hstable (1, s) ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩,
    point_fixed_of_parabolic_plane ρ D hd hstable hc, hc, hgen⟩

end BinaryLinearThree.PointTensor
