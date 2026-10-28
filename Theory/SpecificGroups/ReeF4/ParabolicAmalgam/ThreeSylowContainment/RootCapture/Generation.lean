module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm


/-!
# Generation of the actual fixed Ree seeds by signed blocks

The existing restricted B₂ Bruhat form retains the entire fixed Levi torus.
That torus normalizes both signed blocks. Their join contains the prescribed
Weyl representative, which inverts the torus; conjugating this representative
by a torus element therefore puts the square of that element in the join.
Surjectivity of Frobenius in the finite characteristic-two field supplies
square roots, giving the full fixed torus without an ambient Gauss identity.
The two fixed Bruhat cells then give the whole Suzuki Levi.

The established end-node SL₂ comparison gives the linear Levi. In both cases,
uniqueness of the twist-stable Levi–radical factors descends generation to
the actual fixed seed. No passage of fixed points through a join is assumed.

Source: GLS3 2.3.4–8, Table 2.4 types V and VI, and 2.6.2–5,
`refs/KGroup/GLS3/chapter2.tex`, for the local subgroups underlying
Aschbacher–Smith F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.ThreeSylowContainment.RootCapture
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
open LargeLocalSeeds Binary.FixedGeometry
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
variable {m : ℕ}

private theorem torus_normalizes_block (s : Side) (p : Bool) :
    splitTorus m ≤ normalizer (splitSimpleBlock m s p) := by
  rw [splitTorus_eq_diagonalTorus]
  unfold splitSimpleBlock
  rw [le_normalizer_closure_iff]
  intro z hz x hx
  change z.val ∈ (diagonalTorusHom m).range at hz
  obtain ⟨u, hu⟩ := hz
  obtain ⟨r, t, hr, rfl⟩ := hx
  apply Subgroup.subset_closure
  refine ⟨r, ((integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r :
    (CoefficientField m)ˣ) : CoefficientField m) * t, hr, ?_⟩
  apply Subtype.ext
  change z.val * F4Chevalley.rootCurve r t * z.val⁻¹ = _
  rw [← hu]
  have he := F4Chevalley.rootCurve_torus_conjugation u⁻¹ r t
  simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe] using he

private theorem weyl_torus (a b : (CoefficientField m)ˣ) :
    simpleWord m (sideWord .suzuki) * SuzukiNormalizer.torus a b =
      SuzukiNormalizer.torus a⁻¹ b⁻¹ * simpleWord m (sideWord .suzuki) := by
  have he : simpleWord m (sideWord .suzuki) =
      simpleWord m [1] * (simpleWord m [2] * (simpleWord m [1] * simpleWord m [2])) := by
    simp [simpleWord, sideWord]
  have h1 (a b : (CoefficientField m)ˣ) :
      (MulAut.conj (simpleWord m [1])) (SuzukiNormalizer.torus a b) =
        SuzukiNormalizer.torus (a⁻¹ * b^2) b := by
    simp only [MulAut.conj_apply]
    rw [SuzukiNormalizer.simple_one_torus, mul_inv_cancel_right]
  have h2 (a b : (CoefficientField m)ˣ) :
      (MulAut.conj (simpleWord m [2])) (SuzukiNormalizer.torus a b) =
        SuzukiNormalizer.torus a (b⁻¹ * a) := by
    simp only [MulAut.conj_apply]
    rw [SuzukiNormalizer.simple_two_torus, mul_inv_cancel_right]
  have hc : (MulAut.conj (simpleWord m (sideWord .suzuki))) (SuzukiNormalizer.torus a b) =
      (MulAut.conj (simpleWord m [1])) ((MulAut.conj (simpleWord m [2]))
        ((MulAut.conj (simpleWord m [1])) ((MulAut.conj (simpleWord m [2]))
          (SuzukiNormalizer.torus a b)))) := by
    simp only [MulAut.conj_apply, he]
    group
  rw [h2, h1, h2, h1] at hc
  have ha : (a⁻¹ * (b⁻¹ * a)^2)⁻¹ *
      ((b⁻¹ * a)⁻¹ * (a⁻¹ * (b⁻¹ * a)^2))^2 = a⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  have hb : (b⁻¹ * a)⁻¹ * (a⁻¹ * (b⁻¹ * a)^2) = b⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  rw [ha, hb] at hc
  exact (mul_inv_eq_iff_eq_mul).mp hc

private def fixedTorusFactor (d : LocalBlockInput m) (t : (CoefficientField m)ˣ) :
    d.fixedGroup := ⟨torusFactor t, SuzukiNormalizer.torusFactor_fixed d t⟩

private theorem fixedTorusFactor_mul (d : LocalBlockInput m) (a b : (CoefficientField m)ˣ) :
    fixedTorusFactor d a * fixedTorusFactor d b = fixedTorusFactor d (a * b) := by
  apply Subtype.ext
  change SuzukiNormalizer.torus _ _ * SuzukiNormalizer.torus _ _ = _
  rw [SuzukiNormalizer.torus_mul]
  change SuzukiNormalizer.torus _ _ = SuzukiNormalizer.torus _ _
  rw [map_mul]

private theorem weyl_fixedTorusFactor (d : LocalBlockInput m) (t : (CoefficientField m)ˣ) :
    relativeWeyl d .suzuki * fixedTorusFactor d t =
      (fixedTorusFactor d t)⁻¹ * relativeWeyl d .suzuki := by
  apply Subtype.ext
  change simpleWord m (sideWord .suzuki) * SuzukiNormalizer.torus _ _ = _
  rw [weyl_torus]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  change SuzukiNormalizer.torus _ _ * SuzukiNormalizer.torus _ _ = 1
  rw [SuzukiNormalizer.torus_mul]
  simp

private theorem torusFactor_mem_signed (d : LocalBlockInput m) (t : (CoefficientField m)ˣ) :
    fixedTorusFactor d t ∈ simpleBlock d .suzuki true ⊔ simpleBlock d .suzuki false := by
  let K := simpleBlock d .suzuki true ⊔ simpleBlock d .suzuki false
  have hw : relativeWeyl d .suzuki ∈ K := relativeWeyl_mem_simpleBlock_sup d .suzuki
  have hs (a : (CoefficientField m)ˣ) : fixedTorusFactor d a ∈ normalizer K := by
    apply normalizer_inf_normalizer_le_normalizer_sup _ _
    constructor <;>
      apply (Subgroup.le_normalizer_comap d.fixedGroup.subtype)
    · exact torus_normalizes_block .suzuki true (torusFactor_mem a)
    · exact torus_normalizes_block .suzuki false (torusFactor_mem a)
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective (frobenius_inj (CoefficientField m) 2) (t : CoefficientField m)
  have ha' : a ^ 2 = (t : CoefficientField m) := ha
  have ha0 : a ≠ 0 := by
    intro h
    exact t.ne_zero (by simpa [h] using ha'.symm)
  let u : (CoefficientField m)ˣ := Units.mk0 a ha0
  have huu : u * u = t := Units.ext (by simpa only [u, Units.val_mul, Units.val_mk0, pow_two] using ha')
  have hconj : fixedTorusFactor d u * relativeWeyl d .suzuki * (fixedTorusFactor d u)⁻¹ ∈ K :=
    (mem_normalizer_iff.mp (hs u) _).mp hw
  have he : fixedTorusFactor d u * relativeWeyl d .suzuki * (fixedTorusFactor d u)⁻¹ *
      (relativeWeyl d .suzuki)⁻¹ = fixedTorusFactor d t := by
    have hc := weyl_fixedTorusFactor d u
    have hi : relativeWeyl d .suzuki * (fixedTorusFactor d u)⁻¹ =
        fixedTorusFactor d u * relativeWeyl d .suzuki := by
      calc
        _ = fixedTorusFactor d u *
            (relativeWeyl d .suzuki * fixedTorusFactor d u) * (fixedTorusFactor d u)⁻¹ := by
              rw [hc]; group
        _ = _ := by group
    calc
      _ = fixedTorusFactor d u * (relativeWeyl d .suzuki * (fixedTorusFactor d u)⁻¹) *
          (relativeWeyl d .suzuki)⁻¹ := by group
      _ = fixedTorusFactor d u * fixedTorusFactor d u := by rw [hi]; group
      _ = _ := by rw [fixedTorusFactor_mul, huu]
  rw [← he]
  exact mul_mem hconj (inv_mem hw)

/-- Both signed fixed blocks generate the entire fixed middle-node Levi,
including its fixed torus. -/
theorem suzuki_fixedLevi_le_signed (d : LocalBlockInput m) :
    fixedLevi d .suzuki ≤ simpleBlock d .suzuki true ⊔ simpleBlock d .suzuki false := by
  intro g hg
  obtain ⟨a, ha, b, hb, t, e, he⟩ := suzukiLeviBruhatCover_of_normalForms d
    (suzukiSplitLeviNormalForm m) (suzuki_fixedNormalizerForm d) g hg
  have heq : g = a * fixedTorusFactor d t * (if e then relativeWeyl d .suzuki else 1) * b := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, apply_ite, Subgroup.coe_one, fixedTorusFactor] using he
  rw [heq]
  refine mul_mem (mul_mem (mul_mem (mem_sup_left ha) (torusFactor_mem_signed d t)) ?_)
    (mem_sup_left hb)
  cases e
  · exact one_mem _
  · exact relativeWeyl_mem_simpleBlock_sup d .suzuki

/-- Fixed Levi–radical factorization gives fixed seed generation; this is not
a comap of the corresponding split join. -/
theorem fixedSeed_le_positive_sup_negative (hm : 1 ≤ m) (d : LocalBlockInput m) (s : Side) :
    standardSeed d s ≤ standardUnipotent d ⊔ simpleBlock d s false := by
  rw [standardSeed_eq_fixedLevi_sup_radical]
  refine sup_le ?_ ((standardRadical_le_unipotent d s).trans le_sup_left)
  apply le_trans (b := simpleBlock d s true ⊔ simpleBlock d s false) ?_
    (sup_le_sup_right (simpleBlock_positive_le d s) _)
  cases s
  · exact suzuki_fixedLevi_le_signed d
  · exact fixedLevi_linear_le_signed_of_longRootMap d (linearLongRootMap m hm)

end ReeF4.Parabolics.ThreeSylowContainment.RootCapture
