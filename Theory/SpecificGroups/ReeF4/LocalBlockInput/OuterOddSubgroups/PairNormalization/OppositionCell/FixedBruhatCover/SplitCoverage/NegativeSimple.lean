module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.RootConditions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.Collection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.NegativeSimple.Reflection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition.Matrix

/-!
# Negative-simple multiplication of split F₄ cells

Collect the reflecting positive simple root last. The parameter-one simple
representative preserves the remaining positive factors. If the transported
simple root is positive, move its final root factor across the normalizer
word. Otherwise, for a nonzero parameter, rewrite that factor with the actual
opposite-root rank-one word; keep that word in the middle subgroup, retaining
its torus contribution.

The sign alternative follows from the matrices: the two parameter-one simple
root elements have a nonidentity product of order three, so their conjugates
cannot both lie in the negative unipotent two-group. The latter property is
transferred from the proved positive two-group property using the explicit
matrix that exchanges opposite root curves. No preservation of negation by
`RootTransport.perm` is assumed. Finally, conjugate the positive simple curve
by its parameter-one representative and apply cell exchange twice.

The only input relations are positive-root exchange and the supplied exact
root transport for normalizer words. This proves the local step towards GLS3
1.11.5 from the root identities of 1.12.1; it assumes no global coverage.
Sources: `refs/KGroup/GLS3/Chapter1.tex`, §§1.11–1.12; the fixed-point
application is §2.3.5 in `refs/KGroup/GLS3/chapter2.tex`. The collection
strategy extends the existing binary `SplitCoverage/Exchange` argument.
-/

public section
noncomputable section
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.RadicalCoordinates LargeLocalSeeds Subgroup
open RootPairing.IntegralGeckConstruction
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

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

private theorem positive_simple (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    rootGeneratorInGroup m (typeF4SimpleRootIndex i) t ∈ splitUnipotent m :=
  subset_closure ⟨_, t, typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property, rfl⟩

private abbrev simpleRep (m : ℕ) (i : Fin 4) : SplitGroup m :=
  rankOneRepresentative m (typeF4SimpleRootIndex i) 1

private theorem simpleRep_def (m : ℕ) (i : Fin 4) :
    simpleRep m i = rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 *
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1 *
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 := by
  simp [simpleRep, rankOneRepresentative, CharTwo.neg_eq]

private theorem simpleRep_inv (m : ℕ) (i : Fin 4) : (simpleRep m i)⁻¹ = simpleRep m i := by
  simp only [simpleRep_def, mul_inv_rev, root_inv, mul_assoc]

private theorem simpleRep_conj_positive (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
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

private theorem simple_pair_cube (m : ℕ) (i : Fin 4) :
    (rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 *
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1) ^ 3 = 1 := by
  let x := rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1
  let y := rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1
  have hxx : x * x = 1 := root_self _ _ _
  have hyy : y * y = 1 := root_self _ _ _
  have h : simpleRep m i * x = y * simpleRep m i := by
    have hc := simpleRep_conj_positive m i 1
    exact (mul_inv_eq_iff_eq_mul).mp hc
  rw [simpleRep_def] at h
  have hb : x * y * x = y * x * y := by
    have he := congrArg (fun z => z * x) h
    change (x * y * x * x) * x = (y * (x * y * x)) * x at he
    simpa only [mul_assoc, hxx, mul_one] using he
  change (x * y) ^ 3 = 1
  calc
    (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (y * x * y) * (y * x * y) := by rw [hb]
    _ = (y * x) * (y * y) * (x * y) := by group
    _ = y * (x * x) * y := by rw [hyy]; group
    _ = 1 := by rw [hxx, mul_one, hyy]

private theorem root_one_ne_one (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 1 ≠ 1 := by
  intro h
  have he : rootGeneratorInGroup m r 1 = rootGeneratorInGroup m r 0 :=
    h.trans (root_zero m r).symm
  apply one_ne_zero (α := CoefficientField m)
  apply rootElement_injective (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) (k := CoefficientField m) r
  simp only [rootElement, rootMorphismFamily, rootMorphism_apply]
  congr 1
  change Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r 1) =
    Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r 0)
  exact congrArg Matrix.GeneralLinearGroup.toLin (congrArg Subtype.val he)

private theorem simple_pair_ne_one (m : ℕ) (i : Fin 4) :
    rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 *
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1 ≠ 1 := by
  intro h
  have he : rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1 =
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 := by
    rw [← root_inv]
    exact ((mul_eq_one_iff_eq_inv).mp h).symm
  have hp := typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property
  have hn : rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1 ∈
      splitNegativeUnipotent m := subset_closure ⟨_, 1,
    (fun hn => ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base _).mp hn) hp), rfl⟩
  apply root_one_ne_one m (typeF4SimpleRootIndex i)
  exact (Subgroup.disjoint_def.mp (splitUnipotent_disjoint_negative m))
    (positive_simple m i 1) (he ▸ hn)

private theorem negative_isPGroup (m : ℕ) : IsPGroup 2 (splitNegativeUnipotent m) := by
  let f : SplitGroup m →* MatrixUnits m :=
    (MulAut.conj (WordRelations.Faithfulness.Adjoint.omegaUnit
      (K := CoefficientField m))).toMonoidHom.comp (SplitGroup m).subtype
  have hf : Function.Injective f := (MulAut.conj _).injective.comp Subtype.val_injective
  let A := (splitUnipotent m).map (SplitGroup m).subtype
  have hle : splitNegativeUnipotent m ≤ A.comap f := by
    apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    change WordRelations.Faithfulness.Adjoint.omegaUnit * F4Chevalley.rootCurve r t *
      WordRelations.Faithfulness.Adjoint.omegaUnit⁻¹ ∈ A
    rw [WeylOpposition.omega_conj_rootCurve]
    exact ⟨rootGeneratorInGroup m (-r) t, subset_closure ⟨_, t,
      (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr, rfl⟩, rfl⟩
  have hP : IsPGroup 2 (A.comap f) :=
    ((splitUnipotent_isPGroup m).map (SplitGroup m).subtype).comap_of_injective f hf
  exact hP.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

/-- The exact transported rank-one pair cannot lie wholly in the negative two-group.
Only this sign alternative, not preservation of root negation, is needed below. -/
private theorem transported_simple_sign {m : ℕ} {n : SplitGroup m} (a : RootTransport n)
    (i : Fin 4) :
    typeF4RootPairing_base.IsPos (a.perm (typeF4SimpleRootIndex i)) ∨
      typeF4RootPairing_base.IsPos (a.perm (-typeF4SimpleRootIndex i)) := by
  by_contra h
  obtain ⟨hp, hn⟩ := not_or.mp h
  let z := (MulAut.conj n) (rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 *
    rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1)
  have hz : z ∈ splitNegativeUnipotent m := by
    dsimp only [z]
    rw [map_mul, a.conj_root, a.conj_root]
    exact (splitNegativeUnipotent m).mul_mem
      (subset_closure ⟨_, _, hp, rfl⟩) (subset_closure ⟨_, _, hn, rfl⟩)
  have h3 : z ^ 3 = 1 := by
    dsimp only [z]
    rw [← map_pow, simple_pair_cube, map_one]
  have hz1 : z = 1 := by
    by_contra hne
    have hne' : (⟨z, hz⟩ : splitNegativeUnipotent m) ≠ 1 :=
      fun he => hne (congrArg Subtype.val he)
    have hdiv := (negative_isPGroup m).dvd_orderOf hne'
    have ho : orderOf (⟨z, hz⟩ : splitNegativeUnipotent m) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext h3)
    have : 2 ∣ 3 := hdiv.trans ho
    norm_num at this
  exact simple_pair_ne_one m i ((MulAut.conj n).injective (hz1.trans (map_one _).symm))

private def rootSubgroup (m : ℕ) (r : F4Chevalley.Root) : Subgroup (SplitGroup m) where
  carrier := Set.range (rootGeneratorInGroup m r)
  one_mem' := ⟨0, root_zero m r⟩
  mul_mem' := by
    rintro a b ⟨t, rfl⟩ ⟨v, rfl⟩
    exact ⟨t + v, (root_add m r t v).symm⟩
  inv_mem' := by
    rintro a ⟨t, rfl⟩
    exact ⟨t, (root_inv m r t).symm⟩

private theorem simple_positive_factorization {m : ℕ} (hswap : PositiveRootExchanges m)
    (i : Fin 4) {u : SplitGroup m} (hu : u ∈ splitUnipotent m) :
    ∃ a ∈ splitUnipotent m,
      simpleRep m i * a * (simpleRep m i)⁻¹ ∈ splitUnipotent m ∧
      ∃ t : CoefficientField m, u = a * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t := by
  let A := splitUnipotent m ⊓
    (splitUnipotent m).comap (MulAut.conj (simpleRep m i)).toMonoidHom
  have hpartition (r : Root .positive) :
      (∀ t, rootGeneratorInGroup m r.val t ∈ A) ∨
      (∀ t, rootGeneratorInGroup m r.val t ∈ rootSubgroup m (typeF4SimpleRootIndex i)) := by
    by_cases hr : r.val = typeF4SimpleRootIndex i
    · exact Or.inr (fun t => ⟨t, by rw [hr]⟩)
    · refine Or.inl (fun t => ⟨subset_closure ⟨r.val, t, r.property, rfl⟩, ?_⟩)
      change simpleRep m i * rootGeneratorInGroup m r.val t * (simpleRep m i)⁻¹ ∈ splitUnipotent m
      rw [rankOneRepresentative_one_conj_root]
      exact subset_closure ⟨_, t,
        r.property.reflectionPerm (typeF4RootPairing_baseEquiv i).property hr, rfl⟩
  obtain ⟨a, ha, b, hb, he⟩ := positive_factorization_of_root_partition m hswap
    A (rootSubgroup m (typeF4SimpleRootIndex i)) hpartition hu
  obtain ⟨t, rfl⟩ := hb
  exact ⟨a, ha.1, ha.2, t, he⟩

/-- One simple representative multiplies a normalizer cell into another such cell.
The nonzero branch keeps its additional rank-one representative in the middle. -/
theorem simpleRepresentative_cell_exchange {m : ℕ} (hswap : PositiveRootExchanges m)
    (htransport : ∀ n ∈ splitNormalizerWords m, Nonempty (RootTransport n))
    (i : Fin 4) {u : SplitGroup m} (hu : u ∈ splitUnipotent m)
    {n : SplitGroup m} (hn : n ∈ splitNormalizerWords m) :
    ∃ a ∈ splitUnipotent m, ∃ n' ∈ splitNormalizerWords m, ∃ c ∈ splitUnipotent m,
      rankOneRepresentative m (typeF4SimpleRootIndex i) 1 * u * n = a * n' * c := by
  obtain ⟨a, ha, hsa, t, rfl⟩ := simple_positive_factorization hswap i hu
  obtain ⟨rt⟩ := htransport n⁻¹ ((splitNormalizerWords m).inv_mem hn)
  have hs : simpleRep m i ∈ splitNormalizerWords m := rankOneRepresentative_mem _ _ _
  have hconj (r : F4Chevalley.Root) (v : CoefficientField m) :
      n⁻¹ * rootGeneratorInGroup m r v * n =
        rootGeneratorInGroup m (rt.perm r) ((rt.scale r : CoefficientField m) * v) := by
    simpa only [MulAut.conj_apply, inv_inv] using rt.conj_root r v
  by_cases hp : typeF4RootPairing_base.IsPos (rt.perm (typeF4SimpleRootIndex i))
  · refine ⟨simpleRep m i * a * (simpleRep m i)⁻¹, hsa,
      simpleRep m i * n, (splitNormalizerWords m).mul_mem hs hn,
      rootGeneratorInGroup m (rt.perm (typeF4SimpleRootIndex i))
        ((rt.scale (typeF4SimpleRootIndex i) : CoefficientField m) * t),
      subset_closure ⟨_, _, hp, rfl⟩, ?_⟩
    calc
      _ = (simpleRep m i * a * (simpleRep m i)⁻¹) * (simpleRep m i * n) *
        (n⁻¹ * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t * n) := by group
      _ = _ := by rw [hconj]
  · by_cases ht : t = 0
    · refine ⟨simpleRep m i * a * (simpleRep m i)⁻¹, hsa,
        simpleRep m i * n, (splitNormalizerWords m).mul_mem hs hn,
        1, (splitUnipotent m).one_mem, ?_⟩
      rw [ht, root_zero]
      group
    · have hneg := (transported_simple_sign rt i).resolve_left hp
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
        (splitUnipotent m).mul_mem hsa (positive_simple m i _),
        (simpleRep m i * w) * n,
        (splitNormalizerWords m).mul_mem
          ((splitNormalizerWords m).mul_mem hs (rankOneRepresentative_mem _ _ _)) hn,
        rootGeneratorInGroup m (rt.perm (-typeF4SimpleRootIndex i))
          ((rt.scale (-typeF4SimpleRootIndex i) : CoefficientField m) * (v : CoefficientField m)),
        subset_closure ⟨_, _, hneg, rfl⟩, ?_⟩
      calc
        _ = (simpleRep m i * a * (simpleRep m i)⁻¹) *
            (simpleRep m i * b) * w * b * n := by rw [hsplit]; group
        _ = ((simpleRep m i * a * (simpleRep m i)⁻¹) *
              rootGeneratorInGroup m (typeF4SimpleRootIndex i) (v : CoefficientField m)) *
            ((simpleRep m i * w) * n) * (n⁻¹ * b * n) := by rw [hsb]; group
        _ = _ := by rw [hconj]

/-- Positive collection and exact normalizer root transport imply negative-simple
cell multiplication, including all nonzero field parameters and torus factors. -/
theorem negativeSimpleExchange_of_positive_exchanges (m : ℕ) (_hm : 1 ≤ m)
    (hswap : PositiveRootExchanges m)
    (htransport : ∀ n ∈ splitNormalizerWords m, Nonempty (RootTransport n)) :
    NegativeSimpleExchange m := by
  intro i t u hu n hn
  obtain ⟨a, ha, n', hn', c, hc, he⟩ :=
    simpleRepresentative_cell_exchange hswap htransport i hu hn
  obtain ⟨b, hb, n'', hn'', d, hd, he'⟩ :=
    simpleRepresentative_cell_exchange hswap htransport i
      ((splitUnipotent m).mul_mem (positive_simple m i t) ha) hn'
  have hnegative : rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t =
      simpleRep m i * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t * simpleRep m i := by
    simpa only [simpleRep_inv] using (simpleRep_conj_positive m i t).symm
  refine ⟨b, hb, n'', hn'', d * c, (splitUnipotent m).mul_mem hd hc, ?_⟩
  calc
    _ = simpleRep m i * rootGeneratorInGroup m (typeF4SimpleRootIndex i) t *
      (simpleRep m i * u * n) := by rw [hnegative]; group
    _ = (simpleRep m i * (rootGeneratorInGroup m (typeF4SimpleRootIndex i) t * a) * n') * c := by
      rw [he]
      group
    _ = b * n'' * (d * c) := by rw [he']; group

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
