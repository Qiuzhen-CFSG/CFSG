module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm.Geometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm.Collection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.NegativeSimple.Reflection

/-!
# Multiplying a B₂ cell by a simple reflection

Collect the reflecting root last inside the four-root positive block.
The simple reflection keeps the other factors positive. After transport across
the middle word, the last root is either positive, or its opposite is positive.
In the latter nonzero case, the rank-one identity supplies a new middle word.
Its negative-root representative is a conjugate of an allowed positive-simple
representative, so every middle factor remains in the prescribed normalizer.

This is the subsystem version of `SplitCoverage/NegativeSimple`, with support
and opposite-root preservation supplied by `Geometry`; no ambient coverage is
used. Source: GLS3 1.11.5, 1.12.1, and 2.3.5,
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Subgroup LargeLocalSeeds BlockParameters.FieldRecovery.SuzukiChart
open PairNormalization.OppositionCell PairNormalization.OppositionCell.FixedBruhatCover
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
namespace SuzukiSplitNormalForm
variable {m : ℕ}

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem root_add (m : ℕ) (r : F4Chevalley.Root) (a b : CoefficientField m) :
    rootGeneratorInGroup m r a * rootGeneratorInGroup m r b =
      rootGeneratorInGroup m r (a + b) :=
  Subtype.ext (F4Chevalley.rootCurve_add r a b).symm

private theorem root_self (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    rootGeneratorInGroup m r t * rootGeneratorInGroup m r t = 1 := by
  rw [root_add, CharTwo.add_self_eq_zero, root_zero]

private theorem root_inv (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r t := by
  apply Subtype.ext
  exact (F4Chevalley.rootCurve_inv r t).trans (congrArg _ (CharTwo.neg_eq t))

private theorem positive_simple (m : ℕ) (i : Fin 4)
    (hi : i ∈ leviNodes .suzuki) (t : CoefficientField m) :
    rootGeneratorInGroup m (typeF4SimpleRootIndex i) t ∈ splitSimpleBlock m .suzuki true :=
  subset_closure ⟨_, t, isSimpleBlockRoot_simple .suzuki i hi, rfl⟩

abbrev simpleRep (m : ℕ) (i : Fin 4) : SplitGroup m :=
  rankOneRepresentative m (typeF4SimpleRootIndex i) 1

private theorem simpleRep_def (m : ℕ) (i : Fin 4) :
    simpleRep m i = rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 *
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1 *
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 := by
  simp [simpleRep, rankOneRepresentative, CharTwo.neg_eq]

theorem simpleRep_inv (m : ℕ) (i : Fin 4) : (simpleRep m i)⁻¹ = simpleRep m i := by
  simp only [simpleRep_def, mul_inv_rev, root_inv, mul_assoc]

theorem simpleRep_conj_positive (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    simpleRep m i * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t *
      (simpleRep m i)⁻¹ = rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t :=
  rankOneRepresentative_one_conj_root m i (typeF4SimpleRootIndex i) t

private theorem simpleRep_conj_negative (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    simpleRep m i * rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t *
      (simpleRep m i)⁻¹ = rootGeneratorInGroup m (typeF4SimpleRootIndex i) t := by
  have h := simpleRep_conj_positive m i t
  calc
    _ = simpleRep m i * (simpleRep m i *
        rootGeneratorInGroup m (typeF4SimpleRootIndex i) t * (simpleRep m i)⁻¹) *
        (simpleRep m i)⁻¹ := by rw [h]
    _ = rootGeneratorInGroup m (typeF4SimpleRootIndex i) t := by
      have hs : simpleRep m i * simpleRep m i = 1 := by
        simpa only [simpleRep_inv] using inv_mul_cancel (simpleRep m i)
      rw [simpleRep_inv]
      calc
        _ = (simpleRep m i * simpleRep m i) *
          rootGeneratorInGroup m (typeF4SimpleRootIndex i) t *
          (simpleRep m i * simpleRep m i) := by group
        _ = _ := by rw [hs]; simp


private theorem representative_mem (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
    (t : (CoefficientField m)ˣ) :
    rankOneRepresentative m (typeF4SimpleRootIndex i) t ∈ splitSuzukiNormalizer m :=
  subset_closure ⟨i, hi, t, rfl⟩

private theorem negativeRepresentative_mem (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
    (t : (CoefficientField m)ˣ) :
    rankOneRepresentative m (-typeF4SimpleRootIndex i) t ∈ splitSuzukiNormalizer m := by
  have he : simpleRep m i * rankOneRepresentative m (typeF4SimpleRootIndex i) t *
      (simpleRep m i)⁻¹ = rankOneRepresentative m (-typeF4SimpleRootIndex i) t := by
    dsimp only [rankOneRepresentative]
    calc
      _ = (simpleRep m i * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t *
            (simpleRep m i)⁻¹) *
          (simpleRep m i * rootGeneratorInGroup m (-typeF4SimpleRootIndex i)
            (-(t⁻¹ : (CoefficientField m)ˣ)) * (simpleRep m i)⁻¹) *
          (simpleRep m i * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t *
            (simpleRep m i)⁻¹) := by group
      _ = _ := by rw [simpleRep_conj_positive, simpleRep_conj_negative]; simp only [neg_neg]
  rw [← he]
  exact mul_mem (mul_mem (representative_mem i hi 1) (representative_mem i hi t))
    (inv_mem (representative_mem i hi 1))

private def rootSubgroup (m : ℕ) (r : F4Chevalley.Root) : Subgroup (SplitGroup m) where
  carrier := Set.range (rootGeneratorInGroup m r)
  one_mem' := ⟨0, root_zero m r⟩
  mul_mem' := by
    rintro a b ⟨t, rfl⟩ ⟨v, rfl⟩
    exact ⟨t + v, (root_add m r t v).symm⟩
  inv_mem' := by
    rintro a ⟨t, rfl⟩
    exact ⟨t, (root_inv m r t).symm⟩

private theorem simple_positive_factorization {m : ℕ} (i : Fin 4) (hi : i ∈ leviNodes .suzuki) {u : SplitGroup m} (hu : u ∈ splitSimpleBlock m .suzuki true) :
    ∃ a ∈ splitSimpleBlock m .suzuki true,
      simpleRep m i * a * (simpleRep m i)⁻¹ ∈ splitSimpleBlock m .suzuki true ∧
      ∃ t : CoefficientField m, u = a * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t := by
  let A := splitSimpleBlock m .suzuki true ⊓
    (splitSimpleBlock m .suzuki true).comap (MulAut.conj (simpleRep m i)).toMonoidHom
  have hpartition (j : Fin 4) :
      (∀ t, rootGeneratorInGroup m (roots j) t ∈ A) ∨
      (∀ t, rootGeneratorInGroup m (roots j) t ∈ rootSubgroup m (typeF4SimpleRootIndex i)) := by
    by_cases hr : roots j = typeF4SimpleRootIndex i
    · exact Or.inr (fun t => ⟨t, by rw [hr]⟩)
    · refine Or.inl (fun t => ⟨subset_closure ⟨roots j, t, (simpleBlockRoot_iff _).mpr ⟨j, rfl⟩, rfl⟩, ?_⟩)
      change simpleRep m i * rootGeneratorInGroup m (roots j) t * (simpleRep m i)⁻¹ ∈ splitSimpleBlock m .suzuki true
      rw [rankOneRepresentative_one_conj_root]
      exact subset_closure ⟨_, t,
        ⟨reflection_supported i hi ((simpleBlockRoot_iff _).mpr ⟨j, rfl⟩).1,
          (positive j).reflectionPerm (typeF4RootPairing_baseEquiv i).property hr⟩, rfl⟩
  obtain ⟨a, ha, b, hb, he⟩ := positive_factorization
    A (rootSubgroup m (typeF4SimpleRootIndex i)) hpartition hu
  obtain ⟨t, rfl⟩ := hb
  exact ⟨a, ha.1, ha.2, t, he⟩

/-- One simple representative multiplies a normalizer cell into another such cell.
The nonzero branch keeps its additional rank-one representative in the middle. -/
theorem simpleRepresentative_cell_exchange {m : ℕ} (i : Fin 4) (hi : i ∈ leviNodes .suzuki) {u : SplitGroup m} (hu : u ∈ splitSimpleBlock m .suzuki true)
    {n : SplitGroup m} (hn : n ∈ splitSuzukiNormalizer m) :
    ∃ a ∈ splitSimpleBlock m .suzuki true, ∃ n' ∈ splitSuzukiNormalizer m, ∃ c ∈ splitSimpleBlock m .suzuki true,
      rankOneRepresentative m (typeF4SimpleRootIndex i) 1 * u * n = a * n' * c := by
  obtain ⟨a, ha, hsa, t, rfl⟩ := simple_positive_factorization i hi hu
  obtain ⟨rt⟩ := transport ((splitSuzukiNormalizer m).inv_mem hn)
  have hs : simpleRep m i ∈ splitSuzukiNormalizer m := representative_mem i hi 1
  have hconj (r : F4Chevalley.Root) (v : CoefficientField m) :
      n⁻¹ * rootGeneratorInGroup m r v * n =
        rootGeneratorInGroup m (rt.perm r) ((rt.scale r : CoefficientField m) * v) := by
    simpa only [MulAut.conj_apply, inv_inv] using rt.conj_root r v
  by_cases hp : typeF4RootPairing_base.IsPos (rt.perm (typeF4SimpleRootIndex i))
  · refine ⟨simpleRep m i * a * (simpleRep m i)⁻¹, hsa,
      simpleRep m i * n, (splitSuzukiNormalizer m).mul_mem hs hn,
      rootGeneratorInGroup m (rt.perm (typeF4SimpleRootIndex i))
        ((rt.scale (typeF4SimpleRootIndex i) : CoefficientField m) * t),
      subset_closure ⟨_, _, ⟨rt.supported _
        (isSimpleBlockRoot_simple .suzuki i hi).1, hp⟩, rfl⟩, ?_⟩
    calc
      _ = (simpleRep m i * a * (simpleRep m i)⁻¹) * (simpleRep m i * n) *
        (n⁻¹ * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t * n) := by group
      _ = _ := by rw [hconj]
  · by_cases ht : t = 0
    · refine ⟨simpleRep m i * a * (simpleRep m i)⁻¹, hsa,
        simpleRep m i * n, (splitSuzukiNormalizer m).mul_mem hs hn,
        1, (splitSimpleBlock m .suzuki true).one_mem, ?_⟩
      rw [ht, root_zero]
      group
    · have hneg : typeF4RootPairing_base.IsPos (rt.perm (-typeF4SimpleRootIndex i)) := by
        rw [rt.neg]
        exact (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hp
      let v : (CoefficientField m)ˣ := (Units.mk0 t ht)⁻¹
      let b := rootGeneratorInGroup m (-typeF4SimpleRootIndex i) (v : CoefficientField m)
      let w := rankOneRepresentative m (-typeF4SimpleRootIndex i) v
      have hsplit : rootGeneratorInGroup m (typeF4SimpleRootIndex i) t = b * w * b := by
        have hw : w = b * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t * b := by
          simp only [w, b, rankOneRepresentative, neg_neg, v, inv_inv,
            Units.val_mk0, CharTwo.neg_eq]
        rw [hw]
        calc
          _ = (b * b) * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t *
            (b * b) := by rw [show b * b = 1 from root_self _ _ _]; simp
          _ = b * (b * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t * b) * b := by group
      have hsb : simpleRep m i * b =
          rootGeneratorInGroup m (typeF4SimpleRootIndex i) (v : CoefficientField m) *
            simpleRep m i :=
        (mul_inv_eq_iff_eq_mul).mp (simpleRep_conj_negative m i (v : CoefficientField m))
      refine ⟨(simpleRep m i * a * (simpleRep m i)⁻¹) *
          rootGeneratorInGroup m (typeF4SimpleRootIndex i) (v : CoefficientField m),
        (splitSimpleBlock m .suzuki true).mul_mem hsa (positive_simple m i hi _),
        (simpleRep m i * w) * n,
        (splitSuzukiNormalizer m).mul_mem
          ((splitSuzukiNormalizer m).mul_mem hs (negativeRepresentative_mem i hi v)) hn,
        rootGeneratorInGroup m (rt.perm (-typeF4SimpleRootIndex i))
          ((rt.scale (-typeF4SimpleRootIndex i) : CoefficientField m) * (v : CoefficientField m)),
        subset_closure ⟨_, _, ⟨rt.supported _
          (supported_neg (isSimpleBlockRoot_simple .suzuki i hi).1), hneg⟩, rfl⟩, ?_⟩
      calc
        _ = (simpleRep m i * a * (simpleRep m i)⁻¹) *
            (simpleRep m i * b) * w * b * n := by rw [hsplit]; group
        _ = ((simpleRep m i * a * (simpleRep m i)⁻¹) *
              rootGeneratorInGroup m (typeF4SimpleRootIndex i) (v : CoefficientField m)) *
            ((simpleRep m i * w) * n) * (n⁻¹ * b * n) := by rw [hsb]; group
        _ = _ := by rw [hconj]


end SuzukiSplitNormalForm
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
