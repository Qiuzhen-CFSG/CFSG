module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed.Algebra
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed.Frames
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed.SeedFrame
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed.LowerDirections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Duality
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.CommutatorSpaces

/-!
# The fixed seed line lies in the central-root commutator space

The simple-root displacement plane is spanned by the marked seed vector
and a nonzero lower direction. Conjugating that root and, in the dual
orientation, using one further commuting shear proves membership of the
marked vector in the full central-root displacement space. This uses the
literal representation, not just equality of images in its natural head.

The final theorem constructs `SeedRootFrame` and `HasLowerRootDirections`
in a common basis adapted to the actual seed plane and incident Sylow flag.
Seed injectivity puts each nonzero fixed seed vector outside W. The preceding
cyclic conclusion W = I, with I irreducible, supplies `IsAtom W`; the
chief-factor classification then supplies the compatible natural or dual
lower representation. Thus the conclusion holds in the full module.

The remaining cyclic inputs used here are |A| = 2 and dim [U,A] = 2,
with A identified as the pullback of the intrinsic Borel center. The source
application supplies that identification, the actual parabolic and Sylow
images, and the preceding module conclusions. The lower commutator dimension,
uniqueness of the maximal submodule, and larger quadratic four-group are not
needed for this step. This proves the fixed-line inclusion used in 13.8.25;
the subsequent centralization and cyclic contradiction belong to its consumer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
open Representation BinaryLinear.MiddleParabolic CriticalTransfer.MarkedGeometry

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The root identities and the two lower-factor alternatives put the marked vector
in the full commutator space. The source application must construct both action inputs. -/
theorem mem_commSpace_of_root_frames (ρ : Representation (ZMod 2) H U)
    (φ : BinaryLinear.GL V ≃* H) (A : Subgroup H) (v : U)
    (hs : SeedRootFrame ρ φ A v) (hl : HasLowerRootDirections ρ φ v) :
    v ∈ commSpace ρ A := by
  have hconj : φ (actor 3) * φ (actor 1) * (φ (actor 3))⁻¹ =
      φ centralRoot * φ (actor 1) := by
    simpa only [map_mul, map_inv] using congrArg φ root_conjugation
  have hrz : φ (actor 5) * φ centralRoot = φ centralRoot * φ (actor 5) := by
    simpa only [map_mul] using congrArg φ shear_commutes_centralRoot
  obtain ⟨w, hw, hw0, hvw, hzw, hdir⟩ := hl
  have hv : v ∈ LinearMap.range (ρ (φ centralRoot) - 1) := by
    rcases hdir with htw | ⟨a, b, htw, hrw, hra, hb⟩
    · exact mem_range_of_fixed_lower_line ρ _ _ _ hconj v w
        hs.simple_rank hs.central_rank hs.simple_displacement hw hw0 hvw
        hs.cross_fixed htw hs.central_fixed hzw
    · exact mem_range_of_lower_shear ρ _ _ _ _ hconj hrz v w a b
        hs.simple_rank hs.central_rank hs.simple_displacement hw hw0 hvw
        hs.cross_fixed htw hs.central_fixed hzw hs.shear_fixed hrw hra hb
  obtain ⟨u, rfl⟩ := hv
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨φ centralRoot, hs.central_mem⟩ u

open Representation.BinaryOffender ChiefFactors BinaryLinear

/-- The Sylow-fixed line in the actual generating seed lies in the full central-root
commutator space. In the source cyclic branch, `hWat` follows from W = I in
`cyclic_sections`; that theorem also supplies `hcomm`. Both root-action frames
are constructed here, without any marked-vector commutator premise. -/
theorem fixed_seed_le_commSpace
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) (hWat : IsAtom W)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ g u, e (W.quotientRepresentation g u) = eH g (e u))
    (L F : Submodule (ZMod 2) NaturalSpace)
    (hLP : L ≤ headPlane ρ s W e) (hPF : headPlane ρ s W e ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1) (hF : Module.finrank (ZMod 2) F = 3)
    (hpar : s.parabolic.map eH.toMonoidHom = parabolic (headPlane ρ s W e))
    (hsyl : s.sylow.map eH.toMonoidHom = borel L (headPlane ρ s W e) F)
    (A : Subgroup H)
    (hAc : A = ((Subgroup.center (borel L (headPlane ρ s W e) F)).map
      (borel L (headPlane ρ s W e) F).subtype).comap eH.toMonoidHom)
    (hA : Nat.card A = 2) (hcomm : Module.finrank (ZMod 2) (commSpace ρ A) = 2) :
    s.space.toSubmodule ⊓ fixedSpace ρ s.sylow ≤ commSpace ρ A := by
  intro v hv
  by_cases hv0 : v = 0
  · subst v
    exact (commSpace ρ A).zero_mem
  have hvW : v ∉ W.toSubmodule := fun hvW =>
    hv0 ((Submodule.disjoint_def.mp (s.disjoint_proper ρ W hW)) v hv.1 hvW)
  obtain ⟨c, _, _, _, hs⟩ := exists_seedRootFrame ρ s W hW eH e he L F
    hLP hPF hL hF hpar hsyl A hAc hA hcomm v hv hv0
  have hl := hasLowerRootDirections_of_isNaturalOrDual ρ W eH
    (AxisExclusions.naturalOrDual_atom ρ eH hchief W hWat) c v hvW
  exact mem_commSpace_of_root_frames ρ (flagPullback eH c) A v hs hl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
