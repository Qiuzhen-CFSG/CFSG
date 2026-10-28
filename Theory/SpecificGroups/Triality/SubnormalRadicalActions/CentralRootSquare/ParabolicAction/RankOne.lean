module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.CentralMatrix
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries

/-!
# The central pinned SL₂ action on the first triality radical layer

The Cartan row at α₀ and the columns at −α₀ and −(α₀ + α₁) recover the
first two cubic parameters. Grade roots by the sum of their three arm
coefficients. Every radical root has positive degree, and both marked
roots have degree one, so the matrix filtration kills all cross terms.
This retains arbitrary higher radical coordinates.

The central pinned SL₂ fixes that Cartan row. The two opposite-root columns,
in the order above, form one of its natural blocks. Right multiplication
by its inverse therefore gives (d*x + c*y, b*x + a*y) in characteristic
two. The faithful elementary quotient transfers this equality to the
published radical and actor. No additivity hypothesis or field-size
restriction beyond characteristic two is needed.

Source: the root parametrizations and pinned subsystem construction in
GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), for the central
parabolic in Aschbacher–Smith F.1.12(I)(4), printed pp.263–264
(`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open RootPairing.IntegralGeckConstruction
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.RadicalCoordinates.Centers.UnipotentMatrices
namespace Triality.Standard.Parabolics.CentralRootSquare.RankOne
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private def radicalDegree : typeDRootSpan 4 →+ ℝ where
  toFun x := 2 * x.val 0 + x.val 1 + x.val 2
  map_zero' := by simp
  map_add' x y := by simp only [Submodule.coe_add, Pi.add_apply]; ring

private theorem radicalDegree_rootIndex (i : Fin 12) :
    radicalDegree ((typeDRootPairing 2).root (rootIndex i)) =
      ![1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3] i := by
  fin_cases i <;>
    norm_num [radicalDegree, rootIndex, difference, sumRoot,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      basisVector, Pi.single_apply, Fin.ext_iff]

/-- Degree one entries of an arbitrary central radical root product. -/
private theorem product_layer_entry (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) (hv : v 3 = 0) (j : Fin 2) :
    matrixHom P (orderedProduct P v) (.inl 0) (.inr (![2,6] j)) = v (![0,4] j) := by
  let d := fun k => radicalDegree (Injectivity.rootWeight (b := typeDRootPairing_base 2) k)
  let c : LatticeIndex := .inl (typeDRootPairing_baseEquiv 2 0)
  let r : LatticeIndex := .inr (rootEnumeration (![2,6] j))
  let A (i : Fin 12) := (curve P i (v i)).val.val
  have hraise (i : Fin 12) : Injectivity.Raises d 1 (A i - 1) := by
    by_cases hi : i = 3
    · subst i
      have hz : A 3 = 1 := by simp [A, hv, curve_zero]
      rw [hz, sub_self]
      exact Injectivity.raises_zero d 1
    · have hpos : 1 ≤ radicalDegree ((typeDRootPairing 2).root (rootIndex i)) := by
        rw [radicalDegree_rootIndex]
        fin_cases i <;> first | exact (hi rfl).elim | norm_num
      exact (Injectivity.rootMatrix_raises radicalDegree (rootIndex i) (rootIndex_positive i)
        (by linarith) (v i)).mono d hpos
  have he := Injectivity.prod_entry_eq_sum d 1 (by norm_num)
    (List.ofFn A) (by intro B hB; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB; exact hraise i)
    c r (by
      simp only [d, c, r, Injectivity.rootWeight, Sum.elim_inl, Sum.elim_inr, map_zero]
      change 0 ≤ 1 + (2 * (((typeDRootPairing 2).root (rootEnumeration (![2,6] j)) : Vec 4) 0) +
        (((typeDRootPairing 2).root (rootEnumeration (![2,6] j)) : Vec 4) 1) +
        (((typeDRootPairing 2).root (rootEnumeration (![2,6] j)) : Vec 4) 2))
      simp only [rootCoords_spec]
      have hdeg : ∀ j : Fin 2,
          2 * rootCoords (![2,6] j) 0 + rootCoords (![2,6] j) 1 +
            rootCoords (![2,6] j) 2 = -1 := by decide +kernel
      have hd := congrArg (fun z : ℤ => (z : ℝ)) (hdeg j)
      push_cast at hd
      linarith)
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have hentry (i : Fin 12) : (A i - 1) c r =
      if i = ![0,4] j then v i else 0 := by
    change matrixHom P (curve P i (v i)) (.inl 0) (.inr (![2,6] j)) -
      (1 : Matrix LatticeIndex LatticeIndex (ExtensionField P)) c r = _
    rw [matrixHom_curve P hp]
    simp only [Matrix.one_apply, c, r, Sum.inl_ne_inr, if_false, sub_zero]
    have hcoeff : ∀ (i : Fin 12) (j : Fin 2),
        linearCoefficient (positiveIndex i) (.inl 0) (.inr (![2,6] j)) =
          (if i = ![0,4] j then 1 else 0) ∧
        quadraticCoefficient (positiveIndex i) (.inl 0) (.inr (![2,6] j)) = 0 := by
      decide +kernel
    obtain ⟨hl, hq⟩ := hcoeff i j
    simp only [matrixCurve, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.mapMatrix_apply, Matrix.map_apply, hl, hq, map_zero, mul_zero, add_zero,
      Matrix.one_apply, Sum.inl_ne_inr, if_false, zero_add]
    split_ifs <;> simp
  have hsum : (((List.ofFn A).map (fun B => B - 1)).sum :
      Matrix LatticeIndex LatticeIndex (ExtensionField P)) c r = v (![0,4] j) := by
    rw [List.map_ofFn]
    change (∑ i : Fin 12, (A i - 1)) c r = _
    simp only [Matrix.sum_apply, hentry]
    simp
  have hprod : matrixHom P (orderedProduct P v) (.inl 0) (.inr (![2,6] j)) =
      (List.ofFn A).prod c r := by
    change ((Units.coeHom _).comp (RootPairing.SimpleGeckGroup.subgroup
      (typeDRootPairing_base 2) (ExtensionField P)).subtype) (orderedProduct P v) c r = _
    simp only [orderedProduct, map_list_prod, List.map_ofFn]
    rfl
  rw [hprod, he, hsum]
  simp [c, r]

private def blockCoordinates (P : Parameters) :
    SplitGroup P →* Matrix BlockIndex BlockIndex (ExtensionField P) :=
  (Matrix.reindexRingEquiv (ExtensionField P) (latticeEquiv 1).symm).toMonoidHom.comp
    ((Units.coeHom _).comp (RootPairing.SimpleGeckGroup.subgroup
      (typeDRootPairing_base 2) (ExtensionField P)).subtype)

private theorem blockCoordinates_pinned (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) :
    blockCoordinates P ((pinnedRankOneMaps P hp).hom 1 A) = blockMatrix 1 A := by
  let := rankOneExtensionCharTwo P hp
  ext r s
  change (ambientHom 1 A).val (latticeEquiv 1 r) (latticeEquiv 1 s) = _
  exact ambientHom_entry 1 A r s

/-- The actual root-string orientation: −α₀ is the upper block coordinate. -/
private theorem blockCoordinates_layer (P : Parameters) (g : SplitGroup P) (j : Fin 2) :
    blockCoordinates P g (.inl (.inl 0)) (.inr (.inl (j,1))) =
      matrixHom P g (.inl 0) (.inr (![2,6] j)) := by
  fin_cases j <;> rfl

variable {F : Type*} [CommRing F]

private theorem block_row (A : SL(2, F)) (r : BlockIndex) :
    blockMatrix 1 A (.inl (.inl 0)) r =
      (1 : Matrix BlockIndex BlockIndex F) (.inl (.inl 0)) r := by
  rcases r with ((k | k) | (k | k)) <;>
    simp [blockMatrix, specialBlock, Matrix.one_apply]

private theorem block_column (A : SL(2, F)) (s : Fin 2) (r : BlockIndex) :
    blockMatrix 1 A r (.inr (.inl (s,1))) =
      (if r = .inr (.inl (0,1)) then A 0 s else 0) +
      (if r = .inr (.inl (1,1)) then A 1 s else 0) := by
  rcases r with (k | (⟨i,k⟩ | k))
  · simp [blockMatrix]
  · fin_cases i <;> by_cases hk : k = 1 <;>
      simp [blockMatrix, Matrix.blockDiagonal, hk, Prod.ext_iff]
  · simp [blockMatrix]

private theorem block_left_entry (A : SL(2, F)) (M : Matrix BlockIndex BlockIndex F)
    (r : BlockIndex) :
    (blockMatrix 1 A * M) (.inl (.inl 0)) r = M (.inl (.inl 0)) r := by
  simp only [Matrix.mul_apply, block_row]
  exact congrFun₂ (Matrix.one_mul M) _ _

private theorem block_right_entry (A : SL(2, F)) (M : Matrix BlockIndex BlockIndex F)
    (j : Fin 2) :
    (M * blockMatrix 1 A) (.inl (.inl 0)) (.inr (.inl (j,1))) =
      M (.inl (.inl 0)) (.inr (.inl (0,1))) * A 0 j +
      M (.inl (.inl 0)) (.inr (.inl (1,1))) * A 1 j := by
  simp only [Matrix.mul_apply, block_column, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem pinned_conjugation_entry (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) (g : SplitGroup P) (j : Fin 2) :
    matrixHom P ((pinnedRankOneMaps P hp).hom 1 A * g *
      ((pinnedRankOneMaps P hp).hom 1 A)⁻¹) (.inl 0) (.inr (![2,6] j)) =
    matrixHom P g (.inl 0) (.inr 2) * A⁻¹ 0 j +
      matrixHom P g (.inl 0) (.inr 6) * A⁻¹ 1 j := by
  have hinv : blockCoordinates P (((pinnedRankOneMaps P hp).hom 1 A)⁻¹) =
      blockMatrix 1 A⁻¹ :=
    (congrArg (blockCoordinates P) (((pinnedRankOneMaps P hp).hom 1).map_inv A).symm).trans
      (blockCoordinates_pinned P hp A⁻¹)
  have hmul : blockCoordinates P ((pinnedRankOneMaps P hp).hom 1 A * g) =
      blockMatrix 1 A * blockCoordinates P g :=
    ((blockCoordinates P).map_mul _ _).trans
      (congrArg (· * blockCoordinates P g) (blockCoordinates_pinned P hp A))
  have hm : blockCoordinates P ((pinnedRankOneMaps P hp).hom 1 A * g *
      ((pinnedRankOneMaps P hp).hom 1 A)⁻¹) =
      blockMatrix 1 A * blockCoordinates P g * blockMatrix 1 A⁻¹ :=
    ((blockCoordinates P).map_mul _ _).trans (congrArg₂ (· * ·) hmul hinv)
  have he := congrFun₂ hm (.inl (.inl 0)) (.inr (.inl (j,1)))
  have hc := (block_right_entry A⁻¹ (blockMatrix 1 A * blockCoordinates P g) j).trans
    (congrArg₂ (· + ·)
      (congrArg (· * A⁻¹ 0 j) (block_left_entry A _ _))
      (congrArg (· * A⁻¹ 1 j) (block_left_entry A _ _)))
  exact (blockCoordinates_layer P _ j).symm.trans (he.trans (hc.trans
    (congrArg₂ (· + ·)
      (congrArg (· * A⁻¹ 0 j) (blockCoordinates_layer P g 0))
      (congrArg (· * A⁻¹ 1 j) (blockCoordinates_layer P g 1)))))



end Triality.Standard.Parabolics.CentralRootSquare.RankOne

open Triality.Standard.RadicalCoordinates
namespace Triality.Standard.Parabolics.CentralRootSquare
open RankOne

/-- The genuine pinned central SL₂ acts on the marked first layer by the
specified natural operator, for every radical element and including q = 2. -/
theorem firstLayer_centralActor (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, GaloisField P.prime P.exponent)) (r : radical P .central) :
    firstLayer P hp (conjugation P (centralActor P hp A) r) =
      centralLinear P A (firstLayer P hp r) := by
  let v := expand P (extendOrbit P .central ((coordinates P hp).symm r))
  let w := expand P (extendOrbit P .central
    ((coordinates P hp).symm (conjugation P (centralActor P hp A) r)))
  have hv : v 3 = 0 := rfl
  have hw : w 3 = 0 := rfl
  have hc : orderedProduct P w =
      elementaryInclusion P (centralElementary P hp A) * orderedProduct P v *
        (elementaryInclusion P (centralElementary P hp A))⁻¹ :=
    conjugation_coordinates_split P hp (centralElementary P hp A)
      (centralActor P hp A).property r
  have he : orderedProduct P w =
      (pinnedRankOneMaps P hp).hom 1 (sl2BaseEmbedding P A) * orderedProduct P v *
        ((pinnedRankOneMaps P hp).hom 1 (sl2BaseEmbedding P A))⁻¹ :=
    hc.trans (congrArg (fun x : SplitGroup P => x * orderedProduct P v * x⁻¹)
      (centralElementary_val P hp A))
  have hj (j : Fin 2) : w (![0,4] j) =
      v 0 * (sl2BaseEmbedding P A)⁻¹ 0 j + v 4 * (sl2BaseEmbedding P A)⁻¹ 1 j := by
    have hm := congrArg (fun g : SplitGroup P => matrixHom P g (.inl 0) (.inr (![2,6] j))) he
    have hcalc := pinned_conjugation_entry P hp (sl2BaseEmbedding P A) (orderedProduct P v) j
    have hentries := congrArg₂ (· + ·)
      (congrArg (· * (sl2BaseEmbedding P A)⁻¹ 0 j) (product_layer_entry P hp v hv 0))
      (congrArg (· * (sl2BaseEmbedding P A)⁻¹ 1 j) (product_layer_entry P hp v hv 1))
    exact (product_layer_entry P hp w hw j).symm.trans (hm.trans (hcalc.trans hentries))
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have hinv : ((sl2BaseEmbedding P A)⁻¹).val =
      !![baseFieldEmbedding P (A 1 1), baseFieldEmbedding P (A 0 1);
         baseFieldEmbedding P (A 1 0), baseFieldEmbedding P (A 0 0)] := by
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [CharTwo.neg_eq]
    rfl
  have h0 := hj 0
  have h1 := hj 1
  change w 0 = v 0 * ((sl2BaseEmbedding P A)⁻¹).val 0 0 +
    v 4 * ((sl2BaseEmbedding P A)⁻¹).val 1 0 at h0
  change w 4 = v 0 * ((sl2BaseEmbedding P A)⁻¹).val 0 1 +
    v 4 * ((sl2BaseEmbedding P A)⁻¹).val 1 1 at h1
  rw [hinv] at h0 h1
  change w 0 = v 0 * baseFieldEmbedding P (A 1 1) + v 4 * baseFieldEmbedding P (A 1 0) at h0
  change w 4 = v 0 * baseFieldEmbedding P (A 0 1) + v 4 * baseFieldEmbedding P (A 0 0) at h1
  apply Prod.ext
  · change w 0 = baseFieldEmbedding P (A 1 1) * v 0 + baseFieldEmbedding P (A 1 0) * v 4
    exact h0.trans (congrArg₂ (· + ·) (mul_comm _ _) (mul_comm _ _))
  · change w 4 = baseFieldEmbedding P (A 0 1) * v 0 + baseFieldEmbedding P (A 0 0) * v 4
    exact h1.trans (congrArg₂ (· + ·) (mul_comm _ _) (mul_comm _ _))

end Triality.Standard.Parabolics.CentralRootSquare

end
