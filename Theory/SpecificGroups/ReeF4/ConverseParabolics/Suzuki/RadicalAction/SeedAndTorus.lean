module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.RadicalAction.EndCoordinate
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.RootCapture.Generation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.TorusScaling

/-!
# The actual Suzuki seed and its commuting complementary torus

The fixed middle-node Levi embeds in the full Levi. The diagonal matrices
`torusElement b 1` give an injective complementary torus. The signed Suzuki
coordinate formulas show that this torus centralizes the entire fixed seed
Levi, using the proved generation by both signed blocks.

A paired middle-node torus word belongs to that seed Levi and scales the
end-root curve by a nonidentity inverse square when m is positive. The
end-coordinate calculation therefore proves that the seed acts nontrivially
on the radical abelianization. All actors here are actual fixed matrices.

Source: GLS3, Table 2.4(V), Theorem 2.6.5(e–g), and §3.2; the Suzuki local
factor in Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
namespace ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
open LargeLocalSeeds Parabolics
open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery
open FixedCollection.SeedGeneration FullLeviRepresentation
open Parabolics.OuterLocal.SuzukiCommutators
variable {m : ℕ}

/-- Inclusion of the actual fixed middle-node Levi into the full Levi. -/
def seedHom (m : ℕ) : fixedLevi (canonicalLocalBlockInput m) .suzuki →* fullLevi m :=
  ((canonicalLocalBlockInput m).modelEquiv.toMonoidHom.comp
    (fixedLevi (canonicalLocalBlockInput m) .suzuki).subtype).codRestrict (fullLevi m) (by
      intro x
      change toSplitGroup m ((canonicalLocalBlockInput m).modelEquiv x.val) ∈ splitFullLevi m
      rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
      exact mem_sup_left x.property)

theorem seedHom_injective (m : ℕ) : Function.Injective (seedHom m) := by
  intro x y h
  exact Subtype.ext ((canonicalLocalBlockInput m).modelEquiv.injective
    (congrArg Subtype.val h))

/-- The complementary torus with first character b and second character one. -/
def complementHom (m : ℕ) : (CoefficientField m)ˣ →* fullLevi m :=
  ((torusHom m).comp (MonoidHom.inl _ _)).codRestrict (fullLevi m)
    (fun b => fixedTorus_le_fullLevi m (torusElement_mem b 1))

theorem complementHom_injective (m : ℕ) : Function.Injective (complementHom m) := by
  intro b c h
  exact congrArg Prod.fst (torusHom_injective m (congrArg Subtype.val h))

theorem seedHom_val (x : fixedLevi (canonicalLocalBlockInput m) .suzuki) :
    (seedHom m x).val = (canonicalLocalBlockInput m).modelEquiv x.val := by rfl

theorem complementHom_val (b : (CoefficientField m)ˣ) :
    (complementHom m b).val = torusElement b 1 := by rfl

private def matrixHom (m : ℕ) : Model m →* MatrixUnits m :=
  (SplitGroup m).subtype.comp (toSplitGroup m)

private theorem matrixHom_injective (m : ℕ) : Function.Injective (matrixHom m) :=
  Subtype.val_injective.comp (toSplitGroup_injective m)

private theorem matrixHom_torus (b c : (CoefficientField m)ˣ) :
    matrixHom m (torusElement b c) = (torusMatrix (blockTorus b c))⁻¹ :=
  torusElement_matrix b c

private theorem matrixHom_modelEquiv (d : LocalBlockInput m) (x : d.fixedGroup) :
    matrixHom m (d.modelEquiv x) = x.val.val := by
  change (toSplitGroup m (d.modelEquiv x)).val = _
  rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]

private theorem torusElement_conj_suzuki (b c : (CoefficientField m)ˣ) (p : Bool)
    (t u : CoefficientField m) :
    torusElement b c * (canonicalLocalBlockInput m).modelEquiv
        ((suzukiCoordinates (canonicalLocalBlockInput m)).element p t u) * (torusElement b c)⁻¹ =
      (canonicalLocalBlockInput m).modelEquiv
        ((suzukiCoordinates (canonicalLocalBlockInput m)).element p
          ((signedScale c p : CoefficientField m) * t)
          ((signedScale (centralScale c) p : CoefficientField m) * u)) := by
  apply matrixHom_injective m
  simp only [map_mul, map_inv, matrixHom_torus, matrixHom_modelEquiv,
    SuzukiCoordinates.element_word, inv_inv]
  exact blockTorus_suzukiWord b c p t u

/-- The complementary torus centralizes both signed Suzuki blocks and hence the fixed seed Levi. -/
theorem seed_commutes_complement
    (x : fixedLevi (canonicalLocalBlockInput m) .suzuki) (b : (CoefficientField m)ˣ) :
    Commute (seedHom m x) (complementHom m b) := by
  apply Subtype.ext
  let d := canonicalLocalBlockInput m
  let C := (centralizer {torusElement b 1}).comap d.modelEquiv.toMonoidHom
  have hblock (p : Bool) : simpleBlock d .suzuki p ≤ C := by
    intro y hy
    obtain ⟨t, u, rfl⟩ := (suzukiCoordinates d).element_cover p hy
    apply mem_centralizer_singleton_iff.mpr
    have h := torusElement_conj_suzuki b 1 p t u
    have hs : (signedScale (1 : (CoefficientField m)ˣ) p : CoefficientField m) = 1 := by
      cases p <;> simp [signedScale]
    simp only [centralScale, map_one, one_mul, one_pow, hs] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hx : x.val ∈ C :=
    (sup_le (hblock true) (hblock false))
      (Parabolics.ThreeSylowContainment.RootCapture.suzuki_fixedLevi_le_signed d x.property)
  exact mem_centralizer_singleton_iff.mp hx

end ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction

namespace ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
open LargeLocalSeeds Parabolics
open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery
open FixedCollection.SeedGeneration FullLeviRepresentation
open Parabolics.OuterLocal.SuzukiCommutators
variable {m : ℕ}

private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem middleTorusWord_mem_levi (a : (CoefficientField m)ˣ) :
    middleTorusWord m a ∈ splitLevi m .suzuki := by
  have hw (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (t : CoefficientField m) :
      Parabolics.weylWord m (typeF4SimpleRootIndex i) t ∈ splitLevi m .suzuki := by
    have hp (v : CoefficientField m) :
        rootGeneratorInGroup m (typeF4SimpleRootIndex i) v ∈ splitLevi m .suzuki :=
      mem_sup_left (subset_closure ⟨_, _, isSimpleBlockRoot_simple .suzuki i hi, rfl⟩)
    have hn (v : CoefficientField m) :
        rootGeneratorInGroup m (-typeF4SimpleRootIndex i) v ∈ splitLevi m .suzuki :=
      mem_sup_right (subset_closure ⟨_, _, isSimpleBlockRoot_neg_simple .suzuki i hi, rfl⟩)
    exact mul_mem (mul_mem (hp _) (hn _)) (hp _)
  have ht (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (v : (CoefficientField m)ˣ) :
      Parabolics.torusWord m (typeF4SimpleRootIndex i) v ∈ splitLevi m .suzuki :=
    mul_mem (hw i hi _) (hw i hi _)
  exact mul_mem (ht 1 (by simp [leviNodes]) _) (ht 2 (by simp [leviNodes]) _)

/-- The seed already acts nontrivially on the actual radical abelianization. -/
theorem exists_seed_mover (hm : 1 ≤ m) :
    ∃ s : fixedLevi (canonicalLocalBlockInput m) .suzuki,
      ¬ ActsTriviallyOnRadicalAbelianization m (seedHom m s).val := by
  let d := canonicalLocalBlockInput m
  have hcard : 2 < Nat.card (CoefficientField m) := by
    rw [field_card]
    have h := Nat.pow_lt_pow_right (a := 2) (by omega) (show 1 < 2 * m + 1 by omega)
    simpa using h
  have : Nontrivial (CoefficientField m)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]
    omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : (CoefficientField m)ˣ)
  let s : fixedLevi d .suzuki :=
    ⟨⟨middleTorusWord m u, middleTorusWord_fixed d u⟩, middleTorusWord_mem_levi u⟩
  refine ⟨s, ?_⟩
  intro h
  have hscale (t : CoefficientField m) :
      (seedHom m s).val * endCurve m t * (seedHom m s).val⁻¹ =
        endCurve m (((u : CoefficientField m) ^ 2)⁻¹ * t) := by
    have he := congrArg (fun x : standardSeed d .suzuki => d.modelEquiv x.val)
      (middleTorusElement_scaling d u t)
    have hsval : (seedHom m s).val = d.modelEquiv (middleTorusElement d u).val := rfl
    rw [hsval]
    simpa only [endCurve, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using he
  have hs := scalar_eq_one_of_actsTrivially _ _ h hscale
  apply hu
  apply Units.ext
  have hs' : (u : CoefficientField m) ^ 2 = 1 := inv_eq_one.mp hs
  rcases sq_eq_one_iff.mp hs' with he | he
  · exact he
  · simpa only [CharTwo.neg_eq, Units.val_one] using he

end ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
