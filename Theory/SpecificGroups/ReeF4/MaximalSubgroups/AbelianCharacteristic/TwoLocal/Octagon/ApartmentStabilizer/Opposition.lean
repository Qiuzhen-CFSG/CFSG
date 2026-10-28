module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.Torus
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits

/-!
# Concrete opposition and the intersection of opposite Ree Borels

The word `(linear * suzuki)^4` negates every F₄ root. The root-coordinate
calculation adapts the coordinates in `DerivedTits/BruhatBound/Geometry.lean`;
the general-field root-conjugation theorem in `WeylGeometry/Orbits.lean`
transports every root parameter, so no binary matrix identification is used.

Write an element in the two Borels as positive-unipotent times torus, and as
the opposite conjugate of torus times positive-unipotent. Uniqueness of the
middle normalizer matrix identifies the torus factors. The remaining positive
factor lies in the negative root closure, so the proved disjointness makes
it trivial. This proves torus containment in the full exceptional fixed group.

Source: GLS3 2.3.4–5 and 2.3.8(b,c), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.ApartmentStabilizer
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry SectionGeometry.BNPair
open LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open LocalBlockInput LocalBlockInput.PairNormalization
open scoped Pointwise
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The actual fixed word carrying the standard chamber to its opposite. -/
@[expose] def opposition (m : ℕ) : Model m := (weylLift m .linear * weylLift m .suzuki)^4
private def rotationWord : List (Fin 4) := sideWord .linear ++ sideWord .suzuki
private def oppositionWord : List (Fin 4) :=
  (rotationWord ++ rotationWord) ++ (rotationWord ++ rotationWord)

/-- Opposition is a word in the two actual fixed relative Weyl representatives. -/
theorem opposition_mem_normalizerWords (m : ℕ) : opposition m ∈ normalizerWords m :=
  (normalizerWords m).pow_mem ((normalizerWords m).mul_mem
    (weylLift_mem_normalizerWords m .linear) (weylLift_mem_normalizerWords m .suzuki)) 4

private theorem opposition_toSplitGroup (m : ℕ) :
    toSplitGroup m (opposition m) = simpleWord m oppositionWord := by
  have happ (l k : List (Fin 4)) : simpleWord m (l ++ k) = simpleWord m l * simpleWord m k := by
    simp [simpleWord]
  simp only [opposition, map_pow, map_mul, toSplitGroup_weylLift, oppositionWord,
    rotationWord, happ]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

private def simpleVector (i : Fin 4) (v : Vec 4) : Vec 4 :=
  ![![v 0, v 2, v 1, v 3],
    ![v 0, v 1, v 3, v 2],
    ![v 0, v 1, v 2, -v 3],
    ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]] i

private theorem simple_reflection_coordinates (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      simpleVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [simpleVector, typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem rotation_squared_coordinates (r : F4Chevalley.Root) :
    (wordAction (rotationWord ++ rotationWord) r).val =
      ![-r.val 2, -r.val 3, r.val 0, r.val 1] := by
  simp only [wordAction, rotationWord, sideWord, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Equiv.Perm.mul_apply, simple_reflection_coordinates]
  ext j
  fin_cases j <;>
    norm_num [simpleVector, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem opposition_root (r : F4Chevalley.Root) : wordAction oppositionWord r = -r := by
  apply Subtype.ext
  have hneg : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [hneg]
  have happ (a b : List (Fin 4)) : wordAction (a ++ b) = wordAction a * wordAction b := by
    simp [wordAction]
  rw [oppositionWord, happ, Equiv.Perm.mul_apply, rotation_squared_coordinates,
    rotation_squared_coordinates]
  ext j
  fin_cases j <;> rfl

/-- Exact opposition on every root curve over every Ree coefficient field. -/
theorem opposition_conj_root (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    toSplitGroup m (opposition m) * rootGeneratorInGroup m r t *
        (toSplitGroup m (opposition m))⁻¹ = rootGeneratorInGroup m (-r) t := by
  rw [opposition_toSplitGroup, simpleWord_conj_root, opposition_root]

/-- Conjugation by the concrete opposition word sends the positive root closure
into the negative root closure. -/
theorem opposition_conj_positive (m : ℕ) {u : SplitGroup m}
    (hu : u ∈ splitUnipotent m) :
    toSplitGroup m (opposition m) * u * (toSplitGroup m (opposition m))⁻¹ ∈
      splitNegativeUnipotent m := by
  have h : splitUnipotent m ≤
      (splitNegativeUnipotent m).comap
        (MulAut.conj (toSplitGroup m (opposition m))).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    change toSplitGroup m (opposition m) * rootGeneratorInGroup m r t *
      (toSplitGroup m (opposition m))⁻¹ ∈ splitNegativeUnipotent m
    rw [opposition_conj_root]
    exact subset_closure ⟨-r, t, fun hn =>
      (RootPairing.Base.IsPos.neg_iff_not _ _).mp hn hr, rfl⟩
  exact h hu

/-- The two concrete opposite split Borels intersect only in the torus.
The proof uses middle-matrix uniqueness and disjoint positive/negative root closures. -/
theorem splitBorel_opposition_intersection (m : ℕ) {x : SplitGroup m}
    (hx : x ∈ splitBorel m)
    (hy : (toSplitGroup m (opposition m))⁻¹ * x * toSplitGroup m (opposition m) ∈
      splitBorel m) : x ∈ splitTorus m := by
  let n := toSplitGroup m (opposition m)
  have hn : n ∈ splitNormalizerWords m := opposition_mem_normalizerWords m
  have hx' : x ∈ (splitUnipotent m : Set (SplitGroup m)) * splitTorus m := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (splitTorus_normalizes_unipotent m)]
    exact hx
  have hy' : n⁻¹ * x * n ∈ (splitTorus m : Set (SplitGroup m)) * splitUnipotent m := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (splitTorus_normalizes_unipotent m), sup_comm]
    exact hy
  obtain ⟨u, hu, t, ht, he⟩ := hx'
  obtain ⟨s, hs, v, hv, hf⟩ := hy'
  have heq : u * (t * n) * 1 = 1 * (n * s) * v := by
    calc
      _ = x * n := by rw [← he]; group
      _ = n * (n⁻¹ * x * n) := by group
      _ = _ := by rw [← hf]; group
  have htn : t * n = n * s := middle_representative_unique_of_unipotent
    hu ((splitNormalizerWords m).mul_mem (splitTorus_le_splitNormalizerWords m ht) hn)
    (splitUnipotent m).one_mem (splitUnipotent m).one_mem
    ((splitNormalizerWords m).mul_mem hn (splitTorus_le_splitNormalizerWords m hs)) hv heq
  have hu' : u = n * (s * v * s⁻¹) * n⁻¹ := by
    rw [htn] at heq
    calc
      u = (u * (n * s) * 1) * s⁻¹ * n⁻¹ := by group
      _ = _ := by rw [heq]; group
  have hpos : s * v * s⁻¹ ∈ splitUnipotent m :=
    (le_normalizer_iff.mp (splitTorus_normalizes_unipotent m)) s hs v hv
  have hneg : u ∈ splitNegativeUnipotent m := hu' ▸ opposition_conj_positive m hpos
  have hu1 : u = 1 := (Subgroup.disjoint_def.mp (splitUnipotent_disjoint_negative m)) hu hneg
  have he' : u * t = x := he
  rw [hu1, one_mul] at he'
  exact he' ▸ ht

/-- Restriction to the full exceptional fixed group preserves the torus bound. -/
theorem borel_opposition_intersection (m : ℕ) {x : Model m}
    (hx : x ∈ borel m)
    (hy : (opposition m)⁻¹ * x * opposition m ∈ borel m) : x ∈ fixedTorus m := by
  apply splitBorel_opposition_intersection m hx
  change toSplitGroup m ((opposition m)⁻¹ * x * opposition m) ∈ splitBorel m at hy
  simpa only [map_mul, map_inv] using hy

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.ApartmentStabilizer
