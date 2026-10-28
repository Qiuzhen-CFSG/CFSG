module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Factorization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.NormalizerWords
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders

/-!
# Exact counting through the fixed Ree Bruhat normal form

Split Bruhat uniqueness makes all three factors of a fixed matrix fixed.
Multiplication is therefore a bijection from the dependent family of actual
positive, normalizer and right inversion factors onto `Model m`. The fixed
normalizer is itself the unique product of the fixed torus and the subgroup
of constant-parameter Weyl matrices: their root-monomial actions prove trivial
intersection, and fixed Weyl descent proves coverage.

A left torus factor preserves the right inversion subgroup because diagonal
conjugation preserves every negative root curve. These bijections give
`|Model m| = q^12 |T| ∑ w, |U_w|`, using the established positive subgroup order.
No order formula, simplicity or auxiliary model comparison is assumed. The
remaining torus and inversion-subgroup counts are separate geometric results.
The proof includes `m = 0`, where the carrier is the full binary Ree group,
not its Tits derived subgroup.

Source: GLS3, 2.3.4–2.3.8, in `refs/KGroup/GLS3/chapter2.tex`.
Here `q = 2^(2*m+1)` is the square of GLS3's half-integer parameter.
-/

@[expose] public section
noncomputable section
open Subgroup
local instance (m : ℕ) (H : Subgroup (ReeF4.Model m)) : Fintype H := Fintype.ofFinite _

namespace ReeF4.CentralCovers.OddPrimary.Order
open LargeLocalSeeds Parabolics SectionGeometry.BNPair
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover

/-- The fixed intersection U ∩ n⁻¹U⁻n, with left conjugation by n. -/
def fixedRightUnipotent {m : ℕ} (n : Model m) : Subgroup (Model m) :=
  (rightUnipotent (toSplitGroup m n)).comap (toSplitGroup m)

/-- Multiplication of the actual restricted fixed Bruhat factors. -/
def normalFormMap (m : ℕ) :
    (Σ n : normalizerWords m, unipotent m × fixedRightUnipotent n.val) → Model m :=
  fun x => x.2.1.val * x.1.val * x.2.2.val

/-- Unique split normal forms descend to unique fixed normal forms. -/
theorem normalFormMap_bijective (m : ℕ) : Function.Bijective (normalFormMap m) := by
  constructor
  · rintro ⟨n, u, v⟩ ⟨n', u', v'⟩ he
    have hs := congrArg (toSplitGroup m) he
    change toSplitGroup m (u.val * n.val * v.val) =
      toSplitGroup m (u'.val * n'.val * v'.val) at hs
    simp only [map_mul] at hs
    have hn : n = n' := Subtype.ext (toSplitGroup_injective m
      (middle_representative_unique u.property n.property v.property
        u'.property n'.property v'.property hs))
    subst n'
    obtain ⟨hu, hv⟩ := unipotent_factors_unique u.property v.property
      u'.property v'.property hs
    have hu' : u = u' := Subtype.ext (toSplitGroup_injective m hu)
    have hv' : v = v' := Subtype.ext (toSplitGroup_injective m hv)
    subst u'
    subst v'
    rfl
  · intro g
    let d := canonicalLocalBlockInput m
    obtain ⟨u, hu, n, hn, v, hv, he⟩ := Overlap.exists_split_normal_form m (toSplitGroup m g)
    have hg : d.twist (toSplitGroup m g) = toSplitGroup m g := by
      simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] using
        reeTwist_toSplitGroup m g
    have hproduct : d.twist u * d.twist n * d.twist v = u * n * v := by
      rw [← map_mul, ← map_mul, ← he, hg, he]
    have hnfix : d.twist n = n := middle_representative_unique
      (twist_mem_splitUnipotent d hu) (twist_mem_splitNormalizerWords d hn)
      (twist_mem_rightUnipotent d hv) hu hn hv hproduct
    obtain ⟨hufix, hvfix⟩ := fixed_unipotent_factors d hg hnfix hu hv he
    have hfixed {x : SplitGroup m} (hx : d.twist x = x) : x ∈ ReeF4.fixedSubgroup m := by
      apply (mem_fixedSubgroup m x).mpr
      simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] using hx
    let u₀ : Model m := ⟨u, hfixed hufix⟩
    let n₀ : Model m := ⟨n, hfixed hnfix⟩
    let v₀ : Model m := ⟨v, hfixed hvfix⟩
    have hn₀ : n₀ ∈ normalizerWords m := by
      change toSplitGroup m n₀ ∈ splitNormalizerWords m
      simpa only [toSplitGroup_apply] using hn
    have hu₀ : u₀ ∈ unipotent m := by
      change toSplitGroup m u₀ ∈ splitUnipotent m
      simpa only [toSplitGroup_apply] using hu
    have hv₀ : v₀ ∈ fixedRightUnipotent n₀ := by
      change toSplitGroup m v₀ ∈ rightUnipotent (toSplitGroup m n₀)
      simpa only [toSplitGroup_apply] using hv
    refine ⟨⟨⟨n₀, hn₀⟩, ⟨u₀, hu₀⟩, ⟨v₀, hv₀⟩⟩, ?_⟩
    apply toSplitGroup_injective m
    simpa only [normalFormMap, map_mul, toSplitGroup_apply] using he.symm

private theorem card_mul_sum_of_bijective {G U I : Type*} [Finite U] [Fintype I]
    {R : I → Type*} [∀ i, Finite (R i)] (f : (Σ i, U × R i) → G)
    (hf : Function.Bijective f) :
    Nat.card G = Nat.card U * ∑ i, Nat.card (R i) := by
  calc
    Nat.card G = Nat.card (Σ i, U × R i) := (Nat.card_eq_of_bijective f hf).symm
    _ = ∑ i, Nat.card (U × R i) := Nat.card_sigma
    _ = Nat.card U * ∑ i, Nat.card (R i) := by
      simp only [Nat.card_prod, Finset.mul_sum]

/-- Count all fixed normal forms, retaining the torus in the middle factor. -/
theorem card_model_sum_normalizer (m : ℕ) :
    Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 *
      ∑ n : normalizerWords m, Nat.card (fixedRightUnipotent n.val) := by
  calc
    Nat.card (Model m) = Nat.card (unipotent m) *
        ∑ n : normalizerWords m, Nat.card (fixedRightUnipotent n.val) :=
      card_mul_sum_of_bijective (normalFormMap m) (normalFormMap_bijective m)
    _ = _ := congrArg (fun c => c *
      ∑ n : normalizerWords m, Nat.card (fixedRightUnipotent n.val)) (card_unipotent m)

end ReeF4.CentralCovers.OddPrimary.Order

namespace ReeF4.CentralCovers.OddPrimary.Order
open LargeLocalSeeds Parabolics SectionGeometry.BNPair
open Parabolics.Binary.FixedGeometry SectionGeometry.BNPair.QuotientGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

private theorem weyl_word (m : ℕ) {w : Model m} (hw : w ∈ weylSubgroup m) :
    ∃ l : List (Fin 4), toSplitGroup m w = simpleWord m l := by
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨[], map_one _⟩
  | mul_right x hx y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨l, hl⟩ := ih
    exact ⟨l ++ sideWord s, by rw [map_mul, hl, toSplitGroup_weylLift, simpleWord_append]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    have hi : (weylLift m s)⁻¹ = weylLift m s :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weylLift_sq m s)
    rw [hi]
    obtain ⟨l, hl⟩ := ih
    exact ⟨l ++ sideWord s, by rw [map_mul, hl, toSplitGroup_weylLift, simpleWord_append]⟩

/-- The constant-parameter Weyl matrices meet the fixed diagonal torus trivially. -/
theorem fixedTorus_disjoint_weylSubgroup (m : ℕ) :
    Disjoint (fixedTorus m) (weylSubgroup m) := by
  apply Subgroup.disjoint_def.mpr
  intro w ht hw
  obtain ⟨l, hl⟩ := weyl_word m hw
  obtain ⟨c, hc⟩ := torus_rootMonomial ht
  rw [hl] at hc
  have hp := monomial_perm_unique (simpleWord_rootMonomial m l) hc
  have hr : rootWord l = rootWord [] := weyl_perm_injective hp
  apply toSplitGroup_injective m
  exact ((simpleWord_eq_iff m l []).mpr hr ▸ hl).trans (map_one _).symm

private theorem weyl_le_normalizer (m : ℕ) : weylSubgroup m ≤ normalizerWords m := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s, rfl⟩
  exact weylLift_mem_normalizerWords m s

/-- The actual normalizer factor splits into a fixed torus element and a fixed Weyl word. -/
theorem exists_torus_weyl (m : ℕ) {n : Model m} (hn : n ∈ normalizerWords m) :
    ∃ t ∈ fixedTorus m, ∃ w ∈ weylSubgroup m, n = t * w := by
  obtain ⟨t, ht, l, he⟩ := exists_torus_mul_simpleWord m
    (fun _ hn => Overlap.normalizerWords_weylMonomial (splitTorus_eq_diagonalTorus m) hn)
    (fun _ hn htri => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) hn htri) hn
  have hf := simpleWord_fixed_of_torus_mul m ht he
  obtain ⟨w, hw, hval⟩ := fixed_simpleWord_mem_map m l hf
  refine ⟨n * w⁻¹, ?_, w, hw, ?_⟩
  · change toSplitGroup m (n * w⁻¹) ∈ splitTorus m
    rw [map_mul, map_inv, hval, he, mul_inv_cancel_right]
    exact ht
  · group

/-- Multiplication gives unique fixed torus and Weyl factors in the normalizer. -/
def normalizerProduct (m : ℕ) :
    fixedTorus m × weylSubgroup m → normalizerWords m :=
  fun x => ⟨x.1.val * x.2.val, by
    exact (normalizerWords m).mul_mem
      (fixedTorus_le_normalizerWords m x.1.property) (weyl_le_normalizer m x.2.property)⟩

/-- The torus–Weyl product has neither repetitions nor missing normalizer matrices. -/
theorem normalizerProduct_bijective (m : ℕ) : Function.Bijective (normalizerProduct m) := by
  constructor
  · intro x y he
    exact Subgroup.mul_injective_of_disjoint (fixedTorus_disjoint_weylSubgroup m)
      (congrArg Subtype.val he)
  · intro n
    obtain ⟨t, ht, w, hw, he⟩ := exists_torus_weyl m n.property
    exact ⟨⟨⟨t, ht⟩, ⟨w, hw⟩⟩, Subtype.ext he.symm⟩

private theorem torus_normalizes_negative (m : ℕ) :
    splitTorus m ≤ normalizer (LocalBlockInput.splitNegativeUnipotent m) := by
  rw [splitTorus_eq_diagonalTorus, le_normalizer_iff]
  intro z hz x hx
  obtain ⟨u, hu⟩ := hz
  change diagonalTorusHom m u = z.val at hu
  change (MulAut.conj z) x ∈ _
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨r, ((integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r :
      (CoefficientField m)ˣ) : CoefficientField m) * t, hr, ?_⟩
    apply Subtype.ext
    change z.val * F4Chevalley.rootCurve r t * z.val⁻¹ = _
    rw [← hu]
    have he := F4Chevalley.rootCurve_torus_conjugation u⁻¹ r t
    simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe] using he
  | one => simpa only [map_one] using (one_mem _)
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using inv_mem hx

/-- A left torus factor does not change the literal right inversion subgroup. -/
theorem fixedRightUnipotent_torus_mul {m : ℕ} {t : Model m}
    (ht : t ∈ fixedTorus m) (w : Model m) :
    fixedRightUnipotent (t * w) = fixedRightUnipotent w := by
  ext v
  change (toSplitGroup m v ∈ splitUnipotent m ∧
      toSplitGroup m (t * w) * toSplitGroup m v * (toSplitGroup m (t * w))⁻¹ ∈
        LocalBlockInput.splitNegativeUnipotent m) ↔
    (toSplitGroup m v ∈ splitUnipotent m ∧
      toSplitGroup m w * toSplitGroup m v * (toSplitGroup m w)⁻¹ ∈
        LocalBlockInput.splitNegativeUnipotent m)
  have ht' := Subgroup.mem_normalizer_iff.mp (torus_normalizes_negative m ht)
    (toSplitGroup m w * toSplitGroup m v * (toSplitGroup m w)⁻¹)
  simp only [map_mul, mul_inv_rev]
  simpa only [mul_assoc] using and_congr_right (fun _ => ht'.symm)

private theorem sum_product_of_bijective {N T W : Type*}
    [Fintype N] [Fintype T] [Fintype W]
    (f : T × W → N) (hf : Function.Bijective f) (a : N → ℕ) (b : W → ℕ)
    (hab : ∀ t w, a (f (t, w)) = b w) :
    ∑ n, a n = Nat.card T * ∑ w, b w := by
  classical
  rw [← (Equiv.ofBijective f hf).sum_comp a, Fintype.sum_prod_type]
  simp only [Equiv.ofBijective_apply, hab, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

/-- Exact counting from the genuine restricted Bruhat normal form. -/
theorem card_model_torus_weyl_sum (m : ℕ) :
    Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 * Nat.card (fixedTorus m) *
      ∑ w : weylSubgroup m, Nat.card (fixedRightUnipotent w.val) := by
  rw [card_model_sum_normalizer]
  have hs := sum_product_of_bijective (normalizerProduct m) (normalizerProduct_bijective m)
    (fun n => Nat.card (fixedRightUnipotent n.val))
    (fun w => Nat.card (fixedRightUnipotent w.val))
    (fun t w => congrArg (fun H : Subgroup (Model m) => Nat.card H)
      (fixedRightUnipotent_torus_mul t.property w.val))
  rw [hs]
  exact (mul_assoc _ _ _).symm
end ReeF4.CentralCovers.OddPrimary.Order
