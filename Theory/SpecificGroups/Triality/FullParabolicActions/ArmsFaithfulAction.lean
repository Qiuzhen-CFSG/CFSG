module

public import Theory.SpecificGroups.Triality.FullParabolicActions.Definitions
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Faithfulness of the full arms Levi on the triality radical

The full Levi splits into the subsystem Levi and its centralizing torus, and
uniqueness makes the two factors graph-field fixed. A kernel element fixes the
highest-root subgroup, which the subsystem already centralizes. The highest-root
character and the three arm-simple characters force its central torus factor to
be identity in characteristic two.

The remaining subsystem is the actual PSL₂(q³). It is simple since q³ ≥ 8, and
its radical action is nontrivial: a Frobenius-moved field parameter gives a
nonidentity weight on the short-root orbit (4,5,6). The Geck action formulas and
faithful positive coordinates prove this also at q = 2. All descent uses the
elementary subgroup and the injectivity of its own central quotient.

This proves the arms full-Levi input to the parabolic centralizer reduction.
Source: GLS3 Theorem 2.6.5(e–g) (`refs/KGroup/GLS3/chapter2.tex`), and the
triality case of Aschbacher–Smith F.1.12(I)(4), pp.263–264 (`refs/quasithin.pdf`).
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open scoped MatrixGroups Pointwise
namespace Triality.Standard.Parabolics
open RadicalCoordinates ConcreteBruhat TorusCoordinates PositiveCoordinates
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
noncomputable section

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

private theorem positiveRoot_injective (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    Function.Injective (positiveRoot P i) := by
  intro s t he
  have h := (pinnedRankOneMaps P hp).injective i
    (((pinnedRankOneMaps P hp).positive i s).trans
      (he.trans ((pinnedRankOneMaps P hp).positive i t).symm))
  have hh := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ExtensionField P) =>
    A.val 0 1) h
  simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection] using hh

private theorem shortSplit_one_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (shortSplit P 1) := by
  intro s t h
  have hs (u : ExtensionField P) :
      orderedProduct P (expand P (extendOrbit P .central
        (Function.update 0 1 u, 0))) = shortSplit P 1 u :=
    shortElementary_val P hp 1 u
  have he := orderedProduct_injective P ((hs s).trans (h.trans (hs t).symm))
  have hh := congrFun he 4
  simpa [PositiveCoordinates.expand, extendOrbit] using hh

private theorem exists_moving_arms_weight (P : Parameters) (hp : P.prime = 2) :
    ∃ t : (ExtensionField P)ˣ,
      t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) ≠ 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  obtain ⟨t, ht⟩ := ElementaryCentralKernel.exists_frobenius_moved P
  have ht0 : t ≠ 0 := by rintro rfl; exact ht (map_zero _)
  refine ⟨Units.mk0 t ht0, ?_⟩
  intro he
  have he' : t = fieldFrobenius P t * fieldFrobenius P (fieldFrobenius P t) :=
    (div_eq_one_iff_eq (mul_ne_zero ((map_ne_zero _).mpr ht0)
      ((map_ne_zero _).mpr ((map_ne_zero _).mpr ht0)))).mp he
  -- A trivial weight would make t² a norm and therefore Frobenius fixed.
  have hsq : t ^ 2 = (cubicNorm P t).val := by
    change t ^ 2 = t * fieldFrobenius P t * fieldFrobenius P (fieldFrobenius P t)
    calc
      t ^ 2 = t * t := pow_two t
      _ = t * (fieldFrobenius P t * fieldFrobenius P (fieldFrobenius P t)) :=
        congrArg (t * ·) he'
      _ = _ := (mul_assoc _ _ _).symm
  apply ht
  apply CharTwo.sq_injective
  calc
    (fieldFrobenius P t) ^ 2 = fieldFrobenius P (t ^ 2) := (map_pow _ _ _).symm
    _ = t ^ 2 := by rw [hsq]; exact (cubicNorm P t).property

private theorem levi_arms_simple (P : Parameters) (hp : P.prime = 2) :
    IsSimpleGroup (levi P .arms) := by
  let : IsSimpleGroup PSL(2, ExtensionField P) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [card_extensionField]
      exact (by decide : 4 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left P.q_ge_two 3))
  exact (leviArmsEquivPSL2 P hp).isSimpleGroup

private theorem highest_pairing (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex 11) (typeDSimpleRootIndex 2 i) =
      if i = 1 then 1 else 0 := by
  change (typeDRootPairing 2).pairingIn ℤ (sumRoot 0 1 (by decide))
    (typeDSimpleRootIndex 2 i) = _
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = ((if i = 1 then 1 else 0 : ℤ) : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing]
  fin_cases i <;>
    norm_num [rootIndex, difference, sumRoot, typeDSimpleRootIndex,
      typeDRootEmbedding, typeDRootVector, basisVector, dot, Fin.sum_univ_succ]
  all_goals norm_num [Pi.single_apply, Fin.ext_iff]

private theorem product_highest (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.Coordinates P) (u : ExtensionField P) :
    product P a * curve P 11 u * (product P a)⁻¹ = curve P 11 ((a 1).val * u) := by
  simp only [product, conjugate_product, torusWord_curve_conjugate P hp, highest_pairing]
  simp

private theorem splitCentralTorus_eq_one_of_highest (P : Parameters) (hp : P.prime = 2)
    (t : SplitGroup P) (ht : t ∈ splitCentralTorus P .arms)
    (hc : Commute t (curve P 11 1)) : t = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  obtain ⟨a, rfl⟩ := (show t ∈ Set.range (product P) by
    rw [range_product P hp]; exact ht.1)
  have hconj : product P a * curve P 11 1 * (product P a)⁻¹ = curve P 11 1 := by
    exact (mul_inv_eq_iff_eq_mul).mpr hc.eq
  -- The highest-root character is the central coroot coordinate.
  have h1 : (a 1).val = 1 := by
    rw [product_highest P hp, mul_one] at hconj
    exact highestCurve_injective P hconj
  -- Centralizing the three simple arm curves determines the other coordinates.
  have hs (i : Fin 4) (hi : i ≠ 1) :
      (a 0).val ^ (typeDCartanMatrix 2 i 0) *
        ((a 2).val ^ (typeDCartanMatrix 2 i 2) *
          ((a 3).val ^ (typeDCartanMatrix 2 i 3) *
            ((a 1).val ^ (typeDCartanMatrix 2 i 1) * 1))) = 1 := by
    apply positiveRoot_injective P hp i
    have hcom : Commute (product P a) (positiveRoot P i 1) :=
      (Subgroup.mem_centralizer_iff.mp ht.2 _
        (Subgroup.subset_closure ⟨i, hi, 1, Or.inl rfl⟩)).symm
    have he : product P a * positiveRoot P i 1 * (product P a)⁻¹ =
        positiveRoot P i 1 := (mul_inv_eq_iff_eq_mul).mpr hcom.eq
    simpa only [product, conjugate_product, torusWord_positiveRoot_conjugate_cartan P hp]
      using he
  have h0 : (a 0).val ^ 2 = 1 := by simpa [typeDCartanMatrix, h1] using hs 0 (by decide)
  have h2 : (a 2).val ^ 2 = 1 := by simpa [typeDCartanMatrix, h1] using hs 2 (by decide)
  have h3 : (a 3).val ^ 2 = 1 := by simpa [typeDCartanMatrix, h1] using hs 3 (by decide)
  have ha : a = 1 := by
    funext i
    apply Units.ext
    fin_cases i
    · exact CharTwo.sq_injective (h0.trans (one_pow 2).symm)
    · exact h1
    · exact CharTwo.sq_injective (h2.trans (one_pow 2).symm)
    · exact CharTwo.sq_injective (h3.trans (one_pow 2).symm)
  rw [ha, product_one P hp]

private theorem arms_levi_not_centralizes (P : Parameters) (hp : P.prime = 2) :
    ¬ levi P .arms ≤ Subgroup.centralizer (radical P .arms : Set (Carrier P)) := by
  intro h
  obtain ⟨t, ht⟩ := exists_moving_arms_weight P hp
  have hr : short P hp 1 1 ∈ radical P .arms := by
    rw [radical_eq_descendedRootSubgroup P hp]
    exact short_mem P hp .arms 1 (by decide : (1 : Fin 3) ≠ 0) 1
  have hc : Commute (torusActor P hp .arms t) (short P hp 1 1) :=
    (Subgroup.mem_centralizer_iff.mp (h (torusActor_mem_levi P hp .arms t)) _ hr).symm
  have he : torusElementary P hp .arms t * shortElementary P hp 1 1 =
      shortElementary P hp 1 1 * torusElementary P hp .arms t := by
    apply ElementaryCentralKernel.toCarrier_injective P hp
    simpa only [MonoidHom.map_mul, torusActor, short] using hc.eq
  have hs : elementaryInclusion P (torusElementary P hp .arms t) * shortSplit P 1 1 =
      shortSplit P 1 1 * elementaryInclusion P (torusElementary P hp .arms t) := by
    simpa only [MonoidHom.map_mul, shortElementary_val] using congrArg (elementaryInclusion P) he
  have ha := torus_arms_short_one_conjugate P hp t 1
  have hcomm := hs.symm.trans ((mul_inv_eq_iff_eq_mul).mp ha)
  have hi := shortSplit_one_injective P hp (mul_right_cancel hcomm)
  exact ht (by simpa only [mul_one] using hi.symm)

private theorem arms_levi_centralizer_eq_one (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (hg : g ∈ levi P .arms)
    (hc : g ∈ Subgroup.centralizer (radical P .arms : Set (Carrier P))) : g = 1 := by
  let : IsSimpleGroup (levi P .arms) := levi_arms_simple P hp
  have hle : levi P .arms ≤ fullLevi P .arms := descendSubgroup_mono P le_sup_left
  let f := (fullLeviRadicalAction P .arms).comp (Subgroup.inclusion hle)
  have hker (x : levi P .arms) : x ∈ f.ker ↔
      x.val ∈ Subgroup.centralizer (radical P .arms : Set (Carrier P)) := by
    change Subgroup.inclusion hle x ∈ (fullLeviRadicalAction P .arms).ker ↔ _
    rw [fullLeviRadicalAction_ker]
    rfl
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have hm := (hker ⟨g, hg⟩).mpr hc
    rw [hb] at hm
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hm)
  · exfalso
    apply arms_levi_not_centralizes P hp
    intro x hx
    apply (hker ⟨x, hx⟩).mp
    rw [ht]
    trivial

private theorem fullLevi_arms_centralizer_eq_one (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (hg : g ∈ fullLevi P .arms)
    (hc : g ∈ Subgroup.centralizer (radical P .arms : Set (Carrier P))) : g = 1 := by
  obtain ⟨e, he, rfl⟩ := hg
  have he' : elementaryInclusion P e ∈
      (splitLevi P .arms : Set (SplitGroup P)) * splitCentralTorus P .arms :=
    (Set.ext_iff.mp (splitFullLevi_eq_mul_centralTorus P hp .arms)
      (elementaryInclusion P e)).mp he
  obtain ⟨l, hl, t, ht, hlt⟩ := he'
  have hfix : graphFieldAutomorphism P (l * t) = l * t :=
    (congrArg (graphFieldAutomorphism P) hlt).trans (e.val.property.trans hlt.symm)
  have htf := (splitFullLevi_central_factors_fixed P hp .arms l t hl ht hfix).2
  let te : ElementaryGroup P :=
    ⟨⟨t, htf⟩, fixedTorus_le_elementary P hp ht.1⟩
  let le : ElementaryGroup P := e * te⁻¹
  have hle : elementaryInclusion P le = l := by
    change elementaryInclusion P e * t⁻¹ = l
    rw [← hlt, mul_inv_cancel_right]
  have hlL : toCarrier P le ∈ levi P .arms := by
    refine ⟨le, ?_, rfl⟩
    change elementaryInclusion P le ∈ splitLevi P .arms
    rw [hle]
    exact hl
  let z := elementaryHighestHom P hp (Multiplicative.ofAdd (1 : fixedField P))
  have hz : toCarrier P z ∈ highestRoot P :=
    ⟨z, ⟨Multiplicative.ofAdd (1 : ExtensionField P), rfl⟩, rfl⟩
  have hzR : toCarrier P z ∈ radical P .arms :=
    (le_of_eq (radical_eq_descendedRootSubgroup P hp .arms).symm)
      (highestRoot_le_descendedRootSubgroup P .arms hz)
  have hez : Commute e z := by
    change e * z = z * e
    apply ElementaryCentralKernel.toCarrier_injective P hp
    exact ((toCarrier P).map_mul e z).trans
      (((Subgroup.mem_centralizer_iff.mp hc _ hzR).symm).trans
        ((toCarrier P).map_mul z e).symm)
  have hlz : Commute le z := by
    change le * z = z * le
    apply ElementaryCentralKernel.toCarrier_injective P hp
    exact ((toCarrier P).map_mul le z).trans
      (((Subgroup.mem_centralizer_iff.mp
        (levi_le_centralizer_highestRoot P hp hlL) _ hz).symm).trans
        ((toCarrier P).map_mul z le).symm)
  have htz : Commute te z := by
    have htprod : le⁻¹ * e = te := by dsimp only [le]; group
    exact htprod ▸ hlz.inv_left.mul_left hez
  have ht1 : t = 1 := by
    apply splitCentralTorus_eq_one_of_highest P hp t ht
    change elementaryInclusion P te * elementaryInclusion P z =
      elementaryInclusion P z * elementaryInclusion P te
    exact ((elementaryInclusion P).map_mul te z).symm.trans
      ((congrArg (elementaryInclusion P) htz.eq).trans
        ((elementaryInclusion P).map_mul z te))
  apply arms_levi_centralizer_eq_one P hp _ _ hc
  refine ⟨e, ?_, rfl⟩
  change elementaryInclusion P e ∈ splitLevi P .arms
  have htL : t ∈ splitLevi P .arms := ht1.symm ▸ (splitLevi P .arms).one_mem
  exact hlt ▸ (splitLevi P .arms).mul_mem hl htL

/-- The full arms Levi acts faithfully on its genuine root radical, including q = 2. -/
theorem fullLeviRadicalAction_injective_arms (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (fullLeviRadicalAction P .arms) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply fullLevi_arms_centralizer_eq_one P hp g.val g.property
  rw [fullLeviRadicalAction_ker] at hg
  exact hg

end
end Triality.Standard.Parabolics
