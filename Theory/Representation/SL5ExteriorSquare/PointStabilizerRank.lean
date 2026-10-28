module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Representation.BinaryNaturalDual.Transport
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification

/-!
# Three-rank of the binary SL₅ exterior point stabilizers

The two nonzero bivector orbits have stabilizers of three-rank at least two.
For a decomposable point, its 2+3 parabolic quotient contains one cubic in
each diagonal block, and quotienting by the two-core preserves three-rank.
For a nondecomposable point, the existing split Sp₄(2) section contains the
two independent cubics of A₆. Conjugation transports these bounds throughout
both orbits. The complementary-basis map and inverse transpose transfer the
bound to the exterior cube. The ten-dimensional irreducible classification
then covers every irreducible representation of that dimension.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 12.5.5,
printed p.819; I.1.6(7), printed p.408; and the stabilizer-rank argument
in 13.7.6(1–2), printed pp.938–939.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare.PointStabilizerRank
open SL5TenDimensional

private def cubicTwo (a : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  if a = 0 then 1 else if a = 1 then !![0,1;1,1] else !![1,1;1,0]
private theorem cubicTwo_det : ∀ a, (cubicTwo a).det = 1 := by decide
private theorem cubicTwo_add : ∀ a b, cubicTwo (a+b) = cubicTwo a * cubicTwo b := by decide
private theorem cubicTwo_inj : Function.Injective cubicTwo := by decide
private def cubicTwoHom : Multiplicative (ZMod 3) →* SL(2, ZMod 2) where
  toFun a := ⟨cubicTwo a.toAdd, cubicTwo_det _⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext (cubicTwo_add _ _)

private def cubicThree (a : ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if a = 0 then 1 else if a = 1 then !![0,1,0;1,1,0;0,0,1] else !![1,1,0;1,0,0;0,0,1]
private theorem cubicThree_det : ∀ a, (cubicThree a).det = 1 := by decide
private theorem cubicThree_add : ∀ a b, cubicThree (a+b) = cubicThree a * cubicThree b := by decide
private theorem cubicThree_inj : Function.Injective cubicThree := by decide
private def cubicThreeHom : Multiplicative (ZMod 3) →* SL(3, ZMod 2) where
  toFun a := ⟨cubicThree a.toAdd, cubicThree_det _⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext (cubicThree_add _ _)

private theorem two_rank : 1 ≤ primeRank 3 SL(2, ZMod 2) := by
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative (ZMod 3))
    (fun a => congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 a.toAdd))
    (by simp [Nat.card_eq_fintype_card]) cubicTwoHom
  intro a b h
  exact congrArg Multiplicative.ofAdd (cubicTwo_inj (congrArg Subtype.val h))

private theorem three_rank : 1 ≤ primeRank 3 SL(3, ZMod 2) := by
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative (ZMod 3))
    (fun a => congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 a.toAdd))
    (by simp [Nat.card_eq_fintype_card]) cubicThreeHom
  intro a b h
  exact congrArg Multiplicative.ofAdd (cubicThree_inj (congrArg Subtype.val h))

/-- The decomposable bivector has the 2+3 parabolic stabilizer. -/
theorem decomposable_stabilizer_eq_parabolic : vectorStabilizer decomposable = parabolic 2 := by
  rw [vectorStabilizer_eq_exteriorStabilizer_point]
  have he : Submodule.span (ZMod 2) {decomposable} = V₁ := by
    simp [V₁, coordinateSpan, decomposable]
  rw [he, exteriorStabilizer_V₁_eq_parabolic]

/-- The two cubic Levi factors survive the two-core of the decomposable stabilizer. -/
theorem two_le_decomposable_stabilizer : 2 ≤ primeRank 3 (vectorStabilizer decomposable) := by
  rw [decomposable_stabilizer_eq_parabolic,
    ← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 (parabolic 2)) pCore_isPGroup,
    primeRank_equiv 3 parabolicTwoQuotientEquiv, primeRank_prod_eq_add]
  exact Nat.add_le_add two_rank three_rank

/-- The split Sp₄(2) section supplies two independent cubic elements. -/
theorem two_le_nondecomposable_stabilizer : 2 ≤ primeRank 3 nondecomposableStabilizer := by
  have hr := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F := ZMod 2)
  have hi : Function.Injective nondecomposableSymplecticSection := by
    intro a b h
    have hh := congrArg nondecomposableToSymplectic h
    simpa only [nondecomposableToSymplectic_section] using hh
  exact hr.trans ((Theory.GroupTheory.primeRank_le_of_injective 3 _ (commutator _).subtype_injective).trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 nondecomposableSymplecticSection hi))

private theorem rank_orbit {v w : V} (h : InExteriorOrbit v w) :
    primeRank 3 (vectorStabilizer v) ≤ primeRank 3 (vectorStabilizer w) := by
  obtain ⟨g,rfl⟩ := h
  have hi : exteriorAction 2 g⁻¹ (exteriorAction 2 g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  let f : vectorStabilizer v →* vectorStabilizer (exteriorAction 2 g v) :=
    ((MulAut.conj g).toMonoidHom.comp (vectorStabilizer v).subtype).codRestrict _ (by
      intro a
      change exteriorAction 2 (g * a.val * g⁻¹) (exteriorAction 2 g v) = _
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hi, a.property])
  apply Theory.GroupTheory.primeRank_le_of_injective 3 f
  intro a b h
  apply Subtype.ext
  apply (MulAut.conj g).injective
  change (f a).val = (f b).val
  exact congrArg (fun x : vectorStabilizer (exteriorAction 2 g v) => (x : Group)) h

/-- Every nonzero point of Λ²(F₂⁵) has a stabilizer of three-rank at least two. -/
theorem two_le_vectorStabilizer (v : V) (hv : v ≠ 0) :
    2 ≤ primeRank 3 (vectorStabilizer v) := by
  rcases exterior_orbits_exhaustive v hv with h | h
  · exact two_le_decomposable_stabilizer.trans (rank_orbit h)
  · exact two_le_nondecomposable_stabilizer.trans (rank_orbit h)

/-- The same rank bound in the uniform representation-stabilizer convention. -/
theorem two_le_square_stabilizer (v : ExteriorModule 2) (hv : v ≠ 0) :
    2 ≤ primeRank 3 (BinaryNaturalDual.VectorStabilizers.representationStabilizer
      (exteriorAction 2) v) := two_le_vectorStabilizer v hv

/-- The complementary-basis map transports the bound to the exterior cube,
with the actual inverse-transpose automorphism on the actor. -/
theorem two_le_cube_stabilizer (v : ExteriorModule 3) (hv : v ≠ 0) :
    2 ≤ primeRank 3 (BinaryNaturalDual.VectorStabilizers.representationStabilizer
      (exteriorAction 3) v) := by
  rw [primeRank_equiv 3 (BinaryNaturalDual.Transport.stabilizerEquiv
    (exteriorAction 3) (exteriorAction 2) Duality.graph Duality.hodge Duality.hodge_action v)]
  apply two_le_square_stabilizer
  exact fun h => hv (Duality.hodge.injective (h.trans (map_zero _).symm))

/-- The actual classification of ten-dimensional irreducibles discharges the
choice between the square and cube; neither a model nor a rank premise remains. -/
theorem two_le_irreducible_ten_stabilizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) [Representation.IsIrreducible ρ]
    (hdim : Module.finrank (ZMod 2) W = 10) (v : W) (hv : v ≠ 0) :
    2 ≤ primeRank 3 (BinaryNaturalDual.VectorStabilizers.representationStabilizer ρ v) := by
  rcases SL5TenDimensional.Classification.identification_of_finrank_ten ρ hdim with hs | hc
  · obtain ⟨e⟩ := hs
    rw [primeRank_equiv 3 (BinaryNaturalDual.Transport.stabilizerEquiv
      ρ (exteriorAction 2) (MulEquiv.refl Group) e.toLinearEquiv
      (fun g w => LinearMap.congr_fun (e.isIntertwining' g) w) v)]
    exact two_le_square_stabilizer (e v) (fun h => hv (e.injective (h.trans (map_zero e).symm)))
  · obtain ⟨e⟩ := hc
    rw [primeRank_equiv 3 (BinaryNaturalDual.Transport.stabilizerEquiv
      ρ (exteriorAction 3) (MulEquiv.refl Group) e.toLinearEquiv
      (fun g w => LinearMap.congr_fun (e.isIntertwining' g) w) v)]
    exact two_le_cube_stabilizer (e v) (fun h => hv (e.injective (h.trans (map_zero e).symm)))

end Representation.SL5ExteriorSquare.PointStabilizerRank
