module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldGeometry.Unipotent
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldGeometry.Torus
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Contracts
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.Bruhat
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Factorization

/-!
# Descent through the restricted split Bruhat normal form

Coefficient embeddings preserve root words, positive and negative unipotent subgroups,
and normalizer words. Applying the smaller Frobenius power to a restricted
Bruhat expression and using uniqueness fixes all three factors. The positive
factors descend by their unique root coordinates. For the middle factor, a
torus-times-simple-word expression reduces descent to the diagonal torus;
the simple word is already defined over the prime field. The resulting
preimage lies in the smaller root-generated split group. Naturality and
injectivity then impose the smaller exceptional fixed equation, giving the
full Ree descent contract.

The only remaining inputs are the normalizer's genuine Weyl-monomial action
and its triangular torus kernel, as recorded by
`subfieldDescent_of_normalizerWords`. No exhaustion, ambient simplicity, or
identification of the desired fixed subgroup is assumed.

Source: GLS3 1.11.5 and 1.12.1, `refs/KGroup/GLS3/Chapter1.tex`, and Malle,
J. Algebra 139 (1991), 52–69, DOI 10.1016/0021-8693(91)90283-E;
arXiv:0910.4758, proof of Theorem 5, case 10.
-/

@[expose] public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4 ReeF4.Subfield ReeF4.LargeLocalSeeds ReeF4.Parabolics
open ReeF4.Parabolics.Binary.FixedGeometry
open ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover

namespace ReeF4.Subfield
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Split normalizer words factor into the coroot torus and a prime-field Weyl word. -/
def NormalizerTorusFactorization : Prop :=
  ∀ (m : ℕ) (n : SplitGroup m), n ∈ splitNormalizerWords m →
    ∃ t ∈ splitTorus m, ∃ l : List (Fin 4), n = t * simpleWord m l

theorem splitMap_weylWord {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (r : F4Chevalley.Root)
    (a : CoefficientField k) :
    splitMap f (weylWord k r a) = weylWord m r (f a) := by
  simp only [weylWord, map_mul, splitMap_rootGenerator, map_neg, map_inv₀]

theorem splitMap_simpleWord {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (l : List (Fin 4)) :
    splitMap f (simpleWord k l) = simpleWord m l := by
  induction l with
  | nil => simp [simpleWord]
  | cons i l ih =>
    simpa only [simpleWord, List.map_cons, List.prod_cons, map_mul,
      splitMap_weylWord, map_one] using congrArg
        (fun x => weylWord m (typeF4SimpleRootIndex i) 1 * x) ih

theorem splitMap_mem_negative {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {x : SplitGroup k}
    (hx : x ∈ LocalBlockInput.splitNegativeUnipotent k) :
    splitMap f x ∈ LocalBlockInput.splitNegativeUnipotent m := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    rw [splitMap_rootGenerator]
    exact Subgroup.subset_closure ⟨r, f t, hr, rfl⟩
  | one => simpa only [map_one] using (LocalBlockInput.splitNegativeUnipotent m).one_mem
  | mul x y _ _ hx hy =>
    simpa only [map_mul] using (LocalBlockInput.splitNegativeUnipotent m).mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using (LocalBlockInput.splitNegativeUnipotent m).inv_mem hx

theorem splitMap_mem_normalizerWords {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {x : SplitGroup k}
    (hx : x ∈ splitNormalizerWords k) : splitMap f x ∈ splitNormalizerWords m := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, rfl⟩ := hx
    have he : splitMap f (rankOneRepresentative k r t) =
        rankOneRepresentative m r (Units.map f.toMonoidHom t) := by
      simp only [rankOneRepresentative, map_mul, splitMap_rootGenerator, map_neg,
        Units.val_inv_eq_inv_val, map_inv₀, Units.coe_map]
      rfl
    rw [he]
    exact rankOneRepresentative_mem m r _
  | one => simpa only [map_one] using (splitNormalizerWords m).one_mem
  | mul x y _ _ hx hy => simpa only [map_mul] using (splitNormalizerWords m).mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using (splitNormalizerWords m).inv_mem hx

theorem splitMap_mem_rightUnipotent {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {n x : SplitGroup k}
    (hx : x ∈ rightUnipotent n) :
    splitMap f x ∈ rightUnipotent (splitMap f n) := by
  refine ⟨splitMap_mem_unipotent f hx.1, ?_⟩
  change splitMap f n * splitMap f x * (splitMap f n)⁻¹ ∈
    LocalBlockInput.splitNegativeUnipotent m
  have hn := splitMap_mem_negative f hx.2
  change splitMap f (n * x * n⁻¹) ∈ LocalBlockInput.splitNegativeUnipotent m at hn
  simpa only [map_mul, map_inv] using hn

/-- A normalizer matrix with smaller-field entries descends once its torus factor exists. -/
theorem normalizer_mem_range_of_factorization (hfactor : NormalizerTorusFactorization)
    {k m : ℕ} (f : CoefficientField k →+* CoefficientField m) {n : SplitGroup m}
    (hn : n ∈ splitNormalizerWords m) (hx : ∀ i j, n.val.val i j ∈ Set.range f) :
    n ∈ (splitMap f).range := by
  obtain ⟨t, ht, l, he⟩ := hfactor m n hn
  have hfix := splitMap_frobenius_fixed_of_entries f hx
  rw [he, map_mul, splitMap_simpleWord] at hfix
  have htfix := mul_right_cancel hfix
  have htrange := torus_mem_range_of_entries f ht
    (entries_mem_range_of_splitMap_frobenius_fixed f htfix)
  rw [he]
  exact (splitMap f).range.mul_mem htrange ⟨simpleWord k l, splitMap_simpleWord f l⟩

/-- Descent into the actual smaller root-generated group, using all three Bruhat factors. -/
theorem split_mem_range_of_factorization (hfactor : NormalizerTorusFactorization)
    {k m : ℕ} (f : CoefficientField k →+* CoefficientField m) (g : SplitGroup m)
    (hx : ∀ i j, g.val.val i j ∈ Set.range f) : g ∈ (splitMap f).range := by
  obtain ⟨u, hu, n, hn, v, hv, he⟩ := Overlap.exists_split_normal_form m g
  let F := iterateFrobenius (CoefficientField m) 2 (2*k+1)
  have hfix := splitMap_frobenius_fixed_of_entries f hx
  have hprod : splitMap F u * splitMap F n * splitMap F v = u * n * v := by
    rw [← map_mul, ← map_mul, ← he]
    exact hfix
  have hnfix : splitMap F n = n := middle_representative_unique
    (splitMap_mem_unipotent F hu) (splitMap_mem_normalizerWords F hn)
    (splitMap_mem_rightUnipotent F hv) hu hn hv hprod
  have hv' : splitMap F v ∈ rightUnipotent n := hnfix ▸ splitMap_mem_rightUnipotent F hv
  rw [hnfix] at hprod
  obtain ⟨hufix, hvfix⟩ := unipotent_factors_unique
    (splitMap_mem_unipotent F hu) hv' hu hv hprod
  rw [he]
  exact (splitMap f).range.mul_mem
    ((splitMap f).range.mul_mem
      (unipotent_mem_range_of_entries f hu
        (entries_mem_range_of_splitMap_frobenius_fixed f hufix))
      (normalizer_mem_range_of_factorization hfactor f hn
        (entries_mem_range_of_splitMap_frobenius_fixed f hnfix)))
    (unipotent_mem_range_of_entries f hv.1
      (entries_mem_range_of_splitMap_frobenius_fixed f hvfix))

end
end ReeF4.Subfield

namespace ReeF4.MaximalSubgroups.SimpleNormal

/-- The split-group preimage satisfies the smaller exceptional fixed equation. -/
theorem subfieldDescent_of_normalizer_factorization
    (hfactor : NormalizerTorusFactorization) : SubfieldDescent := by
  intro m k hdiv f
  apply le_antisymm (reeMap_range_le hdiv f)
  intro x hx
  obtain ⟨y, hy⟩ := split_mem_range_of_factorization hfactor f (toSplitGroup m x)
    (fun i j => (coefficient_mem_range_iff f _).mpr
      (entry_pow_eq_of_mem_fixedSubfield hx i j))
  have hyfix : reeTwist k y = y := by
    apply splitMap_injective f
    rw [reeTwist_eq_pow, splitMap_exceptional_pow, hy]
    exact hx
  refine ⟨⟨y, (mem_fixedSubgroup k y).mpr hyfix⟩, ?_⟩
  apply toSplitGroup_injective m
  rw [toSplitGroup_reeMap, toSplitGroup_apply]
  exact hy

open NormalizerGeometry in
/-- Full Ree descent follows from the two intrinsic normalizer-word calculations.
These inputs remain to be supplied before asserting unconditional descent. -/
theorem subfieldDescent_of_normalizerWords
    (hweyl : ∀ (m : ℕ) (n : SplitGroup m), n ∈ splitNormalizerWords m →
      ∃ (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ),
        RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c)
    (hkernel : ∀ (m : ℕ) (n : SplitGroup m), n ∈ splitNormalizerWords m →
      Overlap.IsHeightTriangular n → n ∈ diagonalTorus m) : SubfieldDescent := by
  apply subfieldDescent_of_normalizer_factorization
  intro m n hn
  exact SectionGeometry.BNPair.QuotientGeometry.exists_torus_mul_simpleWord m
    (hweyl m) (hkernel m) hn

end ReeF4.MaximalSubgroups.SimpleNormal
