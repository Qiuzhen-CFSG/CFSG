module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Cosets
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Separation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylLifts
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# The middle Weyl word and the two signed Suzuki blocks

The actual split word `[1,2,1,2]` is fixed by the supplied Ree twist. Its
inverse is the reversed word, which the twist fixes by the integral B₂ braid
relation. Conjugation is the corresponding product of root reflections and
negates all four roots of the middle positive block, including its two
nonsimple roots. Thus it exchanges the literal two-parameter words for every
coefficient field `2^(2*m+1)`.

The prescribed radical and fixed torus are named here for the remaining
Borel-generation and normalization calculations. `SuzukiGauss` is the
remaining inversion identity for one nonzero negative coordinate word.
One instance of that identity puts the Weyl word in the actual root
parabolic. Its construction, and hence the resulting representative, remain
conditional on this local matrix calculation.

Source: GLS3, Theorems 2.3.4–8, Table 2.4 type V, and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`. The simple-root transport argument follows
`LocalIndices/LinearCover/RankOne`; the middle braid is reused from
`ParabolicAmalgam/BinaryLocals/FixedGeometry/WeylLifts` at arbitrary `m`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open Subgroup LargeLocalSeeds Parabolics BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.Binary.FixedGeometry
variable {m : ℕ}
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The longest middle-node word, inside the supplied fixed group. -/
def suzukiPanelWeyl (d : LocalBlockInput m) : d.fixedGroup :=
  ⟨simpleWord m (sideWord .suzuki), by
    change d.twist _ = _
    rw [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
    exact sideWord_fixed m .suzuki⟩

@[simp] theorem suzukiPanelWeyl_val (d : LocalBlockInput m) :
    (suzukiPanelWeyl d).val = simpleWord m (sideWord .suzuki) := rfl

/-- The fixed intersection of the prescribed Suzuki parabolic radical. -/
def suzukiPanelRadical (d : LocalBlockInput m) : Subgroup d.fixedGroup :=
  (splitRadical m .suzuki).subgroupOf d.fixedGroup

/-- The fixed intersection of the split coroot torus. -/
def suzukiPanelTorus (d : LocalBlockInput m) : Subgroup d.fixedGroup :=
  (splitTorus m).subgroupOf d.fixedGroup

theorem suzukiPanelRadical_le_borel (d : LocalBlockInput m) :
    suzukiPanelRadical d ≤ rootBorel d :=
  Subgroup.comap_mono ((splitRadical_le_unipotent m .suzuki).trans le_sup_left)

theorem suzukiPanelTorus_le_borel (d : LocalBlockInput m) :
    suzukiPanelTorus d ≤ rootBorel d := Subgroup.comap_mono le_sup_right

theorem suzukiElement_positive_mem_borel (d : LocalBlockInput m)
    (C : SuzukiCoordinates d) (t u : CoefficientField m) :
    C.element true t u ∈ rootBorel d :=
  (Subgroup.comap_mono (le_sup_left : splitUnipotent m ≤ splitBorel m))
    (simpleBlock_positive_le d .suzuki (C.element_mem true t u))

private theorem root_inv (r : F4Chevalley.Root) (t : CoefficientField m) :
    (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r t := by
  apply Subtype.ext
  simp [F4Chevalley.rootCurve_inv, CharTwo.neg_eq]

private theorem weyl_one_inv (i : Fin 4) :
    (weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ = weylWord m (typeF4SimpleRootIndex i) 1 := by
  simp only [weylWord, mul_inv_rev, root_inv, mul_assoc]

@[simp] theorem suzukiPanelWeyl_inv (d : LocalBlockInput m) :
    (suzukiPanelWeyl d)⁻¹ = suzukiPanelWeyl d := by
  apply Subtype.ext
  have h := sideWord_fixed m .suzuki
  rw [reeTwist_simpleWord] at h
  change simpleWord m [2, 1, 2, 1] = simpleWord m [1, 2, 1, 2] at h
  change (simpleWord m [1, 2, 1, 2])⁻¹ = simpleWord m [1, 2, 1, 2]
  simpa only [simpleWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_inv_rev, weyl_one_inv, mul_assoc] using h

@[simp] theorem suzukiPanelWeyl_mul_self (d : LocalBlockInput m) :
    suzukiPanelWeyl d * suzukiPanelWeyl d = 1 := by
  simpa only [suzukiPanelWeyl_inv] using inv_mul_cancel (suzukiPanelWeyl d)

private theorem simple_weyl_conj (i : Fin 4) (r : F4Chevalley.Root) (t : CoefficientField m) :
    weylWord m (typeF4SimpleRootIndex i) 1 * rootGeneratorInGroup m r t *
      (weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ =
      rootGeneratorInGroup m (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  apply Subtype.ext
  have hw : (weylWord m (typeF4SimpleRootIndex i) 1).val =
      ReeF4.WordRelations.titsUnit [typeF4RootPairing_baseEquiv i] := by
    simp [weylWord, ReeF4.WordRelations.titsUnit_cons, ReeF4.WordRelations.titsUnit_nil,
      typeF4RootPairing_baseEquiv_val]
  change (weylWord m (typeF4SimpleRootIndex i) 1).val * F4Chevalley.rootCurve r t *
    ((weylWord m (typeF4SimpleRootIndex i) 1).val)⁻¹ = _
  rw [hw]
  exact PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
    (typeF4RootPairing_baseEquiv i) r t

/-- Reflection at nodes 2, 1, 2, 1, in the order acting on a root. -/
def suzukiPanelReflection : Equiv.Perm F4Chevalley.Root :=
  typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) *
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) *
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) *
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)

/-- The Weyl word acts on every split root with unchanged field parameter. -/
theorem suzukiPanelWeyl_conj_root (d : LocalBlockInput m) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    (suzukiPanelWeyl d).val * rootGeneratorInGroup m r t * (suzukiPanelWeyl d).val⁻¹ =
      rootGeneratorInGroup m (suzukiPanelReflection r) t := by
  change simpleWord m [1, 2, 1, 2] * _ * (simpleWord m [1, 2, 1, 2])⁻¹ = _
  simp only [simpleWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  let a := weylWord m (typeF4SimpleRootIndex 1) 1
  let b := weylWord m (typeF4SimpleRootIndex 2) 1
  change (a * (b * (a * b))) * rootGeneratorInGroup m r t * (a * (b * (a * b)))⁻¹ = _
  calc
    _ = a * (b * (a * (b * rootGeneratorInGroup m r t * b⁻¹) * a⁻¹) * b⁻¹) * a⁻¹ := by group
    _ = _ := by dsimp only [a, b]; rw [simple_weyl_conj, simple_weyl_conj, simple_weyl_conj, simple_weyl_conj]; rfl

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val - (typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i)) •
        typeF4SimpleRoot i := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4RootPairing_root, typeF4RootPairing_root,
    typeF4SimpleRootIndex_val]

private theorem neg_val (r : F4Chevalley.Root) : (-r).val = -r.val := by
  change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
  rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]

private theorem reflection_suzukiRoots (i : Fin 4) :
    suzukiPanelReflection (suzukiRoots true i) = suzukiRoots false i := by
  rw [show suzukiRoots false i = -(suzukiRoots true i) by fin_cases i <;> rfl]
  apply Subtype.ext
  rw [neg_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [suzukiPanelReflection, Equiv.Perm.mul_apply, suzukiRoots, signedRoot,
      reflection_val, neg_val, typeF4SimpleRootIndex_val, typeF4CorootScale_simpleRoot,
      typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The four-root positive Suzuki word maps to its literal negative word. -/
theorem suzukiPanelWeyl_conj_positive (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (t u : CoefficientField m) :
    suzukiPanelWeyl d * C.element true t u * (suzukiPanelWeyl d)⁻¹ = C.element false t u := by
  apply Subtype.ext
  change (MulAut.conj (suzukiPanelWeyl d).val) (suzukiWord m true t u) = suzukiWord m false t u
  simp only [suzukiWord, map_mul]
  change ((suzukiPanelWeyl d).val * rootGeneratorInGroup m (suzukiRoots true 0) t * (suzukiPanelWeyl d).val⁻¹) *
    ((suzukiPanelWeyl d).val * rootGeneratorInGroup m (suzukiRoots true 1) (theta m t) * (suzukiPanelWeyl d).val⁻¹) *
    ((suzukiPanelWeyl d).val * rootGeneratorInGroup m (suzukiRoots true 2) u * (suzukiPanelWeyl d).val⁻¹) *
    ((suzukiPanelWeyl d).val * rootGeneratorInGroup m (suzukiRoots true 3) (t * theta m t + theta m u) * (suzukiPanelWeyl d).val⁻¹) = _
  simp only [suzukiPanelWeyl_conj_root, reflection_suzukiRoots]

/-- The inverse exchange also holds for all negative Suzuki coordinates. -/
theorem suzukiPanelWeyl_conj_negative (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (t u : CoefficientField m) :
    suzukiPanelWeyl d * C.element false t u * (suzukiPanelWeyl d)⁻¹ = C.element true t u := by
  calc
    _ = (suzukiPanelWeyl d)⁻¹ *
        (suzukiPanelWeyl d * C.element true t u * (suzukiPanelWeyl d)⁻¹) * suzukiPanelWeyl d := by
      rw [suzukiPanelWeyl_conj_positive, suzukiPanelWeyl_inv]
    _ = _ := by group

/-- The missing local inversion law on the nonzero affine Suzuki coordinates.
This only concerns a single Weyl word times one negative block word. -/
def SuzukiGauss (d : LocalBlockInput m) (C : SuzukiCoordinates d) : Prop :=
  ∀ t u : CoefficientField m, t ≠ 0 ∨ u ≠ 0 →
    ∃ v w : CoefficientField m,
      (C.element false v w)⁻¹ * suzukiPanelWeyl d * C.element false t u ∈ rootBorel d

/-- One nonzero instance of the inversion law puts the Weyl representative in
the root parabolic. No fixed-join identity is used. -/
theorem suzukiPanelWeyl_mem_of_gauss (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (hG : SuzukiGauss d C) : suzukiPanelWeyl d ∈ rootParabolic d .suzuki := by
  obtain ⟨v, w, hvw⟩ := hG 0 1 (Or.inr one_ne_zero)
  have hx : C.element false 0 1 ∈ rootParabolic d .suzuki :=
    (le_sup_right : simpleBlock d .suzuki false ≤ rootParabolic d .suzuki)
      (C.element_mem false 0 1)
  have hy : C.element false v w ∈ rootParabolic d .suzuki :=
    (le_sup_right : simpleBlock d .suzuki false ≤ rootParabolic d .suzuki)
      (C.element_mem false v w)
  have hb : (C.element false v w)⁻¹ * suzukiPanelWeyl d * C.element false 0 1 ∈
      rootParabolic d .suzuki := (le_sup_left : rootBorel d ≤ rootParabolic d .suzuki) hvw
  convert (rootParabolic d .suzuki).mul_mem
    ((rootParabolic d .suzuki).mul_mem hy hb) ((rootParabolic d .suzuki).inv_mem hx) using 1
  group

/-- The representative in the actual parabolic, after the local inversion calculation. -/
def suzukiPanelRepresentative (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (hG : SuzukiGauss d C) : rootParabolic d .suzuki :=
  ⟨suzukiPanelWeyl d, suzukiPanelWeyl_mem_of_gauss d C hG⟩

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
end
