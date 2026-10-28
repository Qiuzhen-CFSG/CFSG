module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.RadicalAssembly
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.GoldschmidtONan.Consequences

/-!
# The point-radical normalizer on its omega center

The characteristic omega center gives an action of the actual radical
normalizer. Its kernel is precisely the relative centralizer, so quotienting
constructs the faithful binary action on the original omega center. The
fixed summand is retained as a subspace of this same module, with its original
ambient inclusion. Sylow invariance follows from normalization of R₁ and L.

Source: Aschbacher--Smith, 11.1.5, printed p.766. This is the action
construction preceding the Goldschmidt--O'Nan argument, not its TI input.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand

variable {G : Type*} [Group G]

/-- The normalizer of R preserves its literal ambient omega center. -/
theorem normalizes_omegaCenter (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (radicalOmegaCenter R : Set G) := by
  let Z := (center R).map R.subtype
  let : (omega₁ Z (p := 2)).Characteristic := omega₁_characteristic Z
  exact (normalizer_le_normalizer_characteristic_image R (center R)).trans
    (normalizer_le_normalizer_characteristic_image Z (omega₁ Z (p := 2)))

/-- The omega center is an elementary abelian two-group in the original G. -/
instance omegaCenter_elementary (R : Subgroup G) :
    IsElementaryAbelian 2 (radicalOmegaCenter R) := by
  let Z := (center R).map R.subtype
  let : IsElementaryAbelian 2 (omega₁ Z (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative Z
  exact IsElementaryAbelian.map_subtype

/-- Conjugation by Y=N_G(R), before factoring out its kernel. -/
def conjugation (R : Subgroup G) :
    normalizer (R : Set G) →* MulAut (radicalOmegaCenter R) :=
  (radicalOmegaCenter R).normalizerMonoidHom.comp
    (inclusion (normalizes_omegaCenter R))

/-- The denominator is C_Y(Z₁), relative to Y, not an ambient centralizer. -/
def kernel (R : Subgroup G) : Subgroup (normalizer (R : Set G)) :=
  (centralizer (radicalOmegaCenter R : Set G)).subgroupOf (normalizer (R : Set G))

theorem conjugation_ker (R : Subgroup G) : (conjugation R).ker = kernel R := by
  rw [conjugation, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

instance kernel_normal (R : Subgroup G) : (kernel R).Normal := by
  rw [← conjugation_ker]
  infer_instance

/-- The source's literal quotient Y/C_Y(Z₁). -/
abbrev Actor (R : Subgroup G) := normalizer (R : Set G) ⧸ kernel R

/-- The original quotient projection. -/
def projection (R : Subgroup G) : normalizer (R : Set G) →* Actor R :=
  QuotientGroup.mk' (kernel R)

/-- The faithful action induced by the same ambient conjugations. -/
def action (R : Subgroup G) : Actor R →* MulAut (radicalOmegaCenter R) :=
  QuotientGroup.lift (kernel R) (conjugation R) (by rw [conjugation_ker])

theorem action_injective (R : Subgroup G) : Function.Injective (action R) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (conjugation_ker R).symm

/-- The binary representation used in the source's GO pair. -/
def representation (R : Subgroup G) :
    Representation (ZMod 2) (Actor R) (Additive (radicalOmegaCenter R)) :=
  elementaryRepresentation (p := 2) (action R)

theorem representation_injective (R : Subgroup G) :
    Function.Injective (representation R) := by
  intro a b hab
  apply action_injective R
  apply MulEquiv.ext
  intro z
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (radicalOmegaCenter R)) =>
    (f (Additive.ofMul z)).toMul) hab

/-- Evaluation retains the original left-conjugation convention. -/
theorem representation_projection (R : Subgroup G)
    (y : normalizer (R : Set G)) (z : Additive (radicalOmegaCenter R)) :
    ((representation R (projection R y) z).toMul : G) =
      (y : G) * (z.toMul : G) * (y : G)⁻¹ := rfl

/-- Subspaces of this module are actual subgroups of Z₁. -/
def subspaceEquiv (R : Subgroup G) :
    Submodule (ZMod 2) (Additive (radicalOmegaCenter R)) ≃o
      Subgroup (radicalOmegaCenter R) :=
  (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup'

/-- The subspace C_{Z₁}(L), without changing its ambient inclusion. -/
def fixedSubspace (R L : Subgroup G) :
    Submodule (ZMod 2) (Additive (radicalOmegaCenter R)) :=
  (subspaceEquiv R).symm ((radicalFixedCenter R L).subgroupOf (radicalOmegaCenter R))

theorem mem_fixedSubspace (R L : Subgroup G) (z : Additive (radicalOmegaCenter R)) :
    z ∈ fixedSubspace R L ↔ (z.toMul : G) ∈ radicalFixedCenter R L := Iff.rfl

/-- The actual image of an ambient Cartan under the specified projection.
Its containment in Y is a separate geometric assertion. -/
def cartanImage (R X : Subgroup G) : Subgroup (Actor R) :=
  (X.subgroupOf (normalizer (R : Set G))).map (projection R)

/-- Fixed vectors for the Cartan image are exactly the original vectors
centralizing X. Surjectivity onto the image retains every element of X. -/
theorem fixedSpace_cartanImage (R X : Subgroup G)
    (hX : X ≤ normalizer (R : Set G)) :
    BinaryOffender.fixedSpace (representation R) (cartanImage R X) =
      fixedSubspace R X := by
  ext z
  constructor
  · intro hz
    refine ⟨z.toMul.property, ?_⟩
    intro x hx
    let y : normalizer (R : Set G) := ⟨x, hX hx⟩
    have hh := hz ⟨projection R y, mem_map_of_mem (projection R) hx⟩
    have he := congrArg (fun v : Additive (radicalOmegaCenter R) => (v.toMul : G)) hh
    change x * (z.toMul : G) * x⁻¹ = (z.toMul : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hz a
    obtain ⟨y, hy, he⟩ := a.property
    change representation R a.val z = z
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (y : G) * (z.toMul : G) * (y : G)⁻¹ = (z.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hz.2 (y : G) hy)

/-- Stabilizing the marked subspace is exactly normalizing the original
fixed summand. This identifies the relative stabilizer without replacing G. -/
theorem stabilizer_comap [Finite G] (R L : Subgroup G) :
    (BinaryOffender.subspaceStabilizer (representation R) (fixedSubspace R L)).comap
      (projection R) =
        (normalizer (radicalFixedCenter R L : Set G)).subgroupOf (normalizer (R : Set G)) := by
  ext y
  constructor
  · intro hy
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨z, hz, rfl⟩
      let z' : Additive (radicalOmegaCenter R) := Additive.ofMul ⟨z, hz.1⟩
      have hh := (hy z').mpr (show z' ∈ fixedSubspace R L from hz)
      exact hh
    · rw [card_map_of_injective (MulAut.conj (y : G)).injective]
  · intro hy z
    exact ((mem_normalizer_iff.mp hy) (z.toMul : G)).symm

/-- Invariance for the quotient action transports back along the original
surjection to the requested ambient normalizer containment. -/
theorem normalizes_fixed_of_invariant [Finite G] (R L : Subgroup G)
    (h : GoldschmidtONan.Invariant (representation R) (fixedSubspace R L)) :
    normalizer (R : Set G) ≤ normalizer (radicalFixedCenter R L : Set G) := by
  intro y hy
  have hh : (⟨y, hy⟩ : normalizer (R : Set G)) ∈
      (BinaryOffender.subspaceStabilizer (representation R) (fixedSubspace R L)).comap
        (projection R) :=
    (GoldschmidtONan.mem_subspaceStabilizer_iff_map _ _).mpr (h (projection R ⟨y, hy⟩))
  rwa [stabilizer_comap] at hh

/-- The actual source Sylow subgroup preserves the fixed summand, before
any assertion about the whole radical normalizer. -/
theorem sylow_normalizes_fixed [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V)
    {F : ChapterB.QuasisimpleSource.BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) :
    (T : Subgroup G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) :=
  (le_inf ((sylow_normalizes_Ri f 0).trans (normalizes_omegaCenter _))
    (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf

/-- Maximal-local uniqueness already controls the entire normalizer of a
nontrivial fixed summand, using only its proved Sylow invariance. -/
theorem chosen_fixed_normalizer_le [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    normalizer (radicalFixedCenter (f.Ri 0) L : Set G) ≤ normalizer (L : Set G) := by
  apply D.normal_subgroup_normalizer_le S.source.toHypothesis1221 _ hne
  · exact sup_le
      ((le_centralizer_iff.mpr inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
      (sylow_normalizes_fixed D f)
  · exact inf_le_left.trans ((omegaOneAmbient_le _).trans
      ((map_subtype_le (center (f.Ri 0))).trans ((localRadical_le_sylow _).trans le_sup_right)))

/-- The source equality N_Y(ZC)=Y intersect M, when ZC is nontrivial. -/
theorem chosen_fixed_stabilizer [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    normalizer (f.Ri 0 : Set G) ⊓ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) =
      normalizer (f.Ri 0 : Set G) ⊓ normalizer (L : Set G) := by
  apply le_antisymm (inf_le_inf_left _ (chosen_fixed_normalizer_le D S f hne))
  apply le_inf inf_le_left
  exact (le_inf (inf_le_left.trans (normalizes_omegaCenter _))
    (inf_le_right.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
