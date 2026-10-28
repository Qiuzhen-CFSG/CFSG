module
public import Theory.SpecificGroups.Triality.FullParabolicActions.Definitions
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Multiplication

/-!
# Central-torus square rigidity in the arms parabolic

A full Levi element centralizing the actual arms subsystem lifts to its
centralizing split torus. Indeed, the unique subsystem/central-torus factors
are graph-field fixed and elementary; the subsystem factor lies in the center
of the genuine PSL₂(q³), which is trivial by its characteristic-two SL₂ model.

Centralizing the three simple arm curves forces the torus coordinates to be
(s, s², s, s), and graph-field fixedness puts s in the actual fixed field.
The long radical roots at positions 3 and 10 both have weight s. The checked
arms multiplication law shows that the displacement of their product has
square with highest-root parameter (1+s)². Faithful descent through the
elementary group's own central quotient forces s = 1. This includes q = 2.

This is the pointwise root calculation used in the arms subnormal-actor
argument; it assumes only subsystem centralization and displacement squares.
Sources: the root and torus relations in GLS3 §§2.4 and 2.6
(`refs/KGroup/GLS3/chapter2.tex`), and the special triality radical in
Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, printed pp.262–264).
-/

open Theory.AlgebraicGroup.StandardRootSystem
open scoped MatrixGroups Pointwise commutatorElement
namespace Triality.Standard.Parabolics
open RadicalCoordinates ConcreteBruhat TorusCoordinates PositiveCoordinates
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
noncomputable section

private theorem levi_center_element (P : Parameters) (hp : P.prime = 2)
    (x : levi P .arms) (hx : x ∈ Subgroup.center (levi P .arms)) : x = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let e := (leviArmsEquivPSL2 P hp).trans (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm
  have he : e x ∈ Subgroup.center SL(2, ExtensionField P) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hx z)
  rw [Theory.PSL2.sl2_center_eq_bot, Subgroup.mem_bot] at he
  exact e.injective (he.trans e.map_one.symm)

private theorem fullLevi_lift (P : Parameters) (g : Carrier P) (hg : g ∈ fullLevi P .arms) :
    ∃ e : ElementaryGroup P, elementaryInclusion P e ∈ splitFullLevi P .arms ∧
      toCarrier P e = g := by
  exact Subgroup.mem_map.mp hg

private theorem torus_parameters (P : Parameters) (hp : P.prime = 2)
    (t : SplitGroup P) (ht : t ∈ splitTorus P) :
    ∃ a : TorusCoordinates.Coordinates P, product P a = t := by
  have hh : t ∈ Set.range (product P) := by rw [range_product P hp]; exact ht
  exact hh

private theorem central_torus_descends (P : Parameters) (t : ElementaryGroup P)
    (ht : elementaryInclusion P t ∈ splitCentralTorus P .arms) :
    toCarrier P t ∈ Subgroup.centralizer (levi P .arms : Set (Carrier P)) := by
  apply Subgroup.mem_centralizer_iff.mpr
  rintro x ⟨xe, hxe, rfl⟩
  have hc : xe * t = t * xe := by
    apply elementaryInclusion_injective P
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp ht.2
      (elementaryInclusion P xe) hxe
  exact (map_mul (toCarrier P) xe t).symm.trans
    ((congrArg (toCarrier P) hc).trans (map_mul (toCarrier P) t xe))

private theorem central_factor_eq (P : Parameters) (hp : P.prime = 2)
    (l t g : Carrier P) (hl : l ∈ levi P .arms)
    (ht : t ∈ Subgroup.centralizer (levi P .arms : Set (Carrier P)))
    (hg : g ∈ Subgroup.centralizer (levi P .arms : Set (Carrier P)))
    (hprod : l * t = g) : t = g := by
  have hlc : (⟨l, hl⟩ : levi P .arms) ∈ Subgroup.center (levi P .arms) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hm : l ∈ Subgroup.centralizer (levi P .arms : Set (Carrier P)) := by
      have hh := (Subgroup.centralizer (levi P .arms : Set (Carrier P))).mul_mem hg
        ((Subgroup.centralizer _).inv_mem ht)
      rwa [← hprod, mul_inv_cancel_right] at hh
    exact Subgroup.mem_centralizer_iff.mp hm x.val x.property
  have hl1 : l = 1 := congrArg Subtype.val (levi_center_element P hp _ hlc)
  simpa only [hl1, one_mul] using hprod

private theorem centralizer_lift (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (hgF : g ∈ fullLevi P .arms)
    (hg : g ∈ Subgroup.centralizer (levi P .arms : Set (Carrier P))) :
    ∃ e : ElementaryGroup P, toCarrier P e = g ∧
      elementaryInclusion P e ∈ splitCentralTorus P .arms := by
  -- Keep the representative fixed while splitting its two elementary factors.
  let e := (fullLevi_lift P g hgF).choose
  have he : elementaryInclusion P e ∈ splitFullLevi P .arms := (fullLevi_lift P g hgF).choose_spec.1
  have heq : toCarrier P e = g := (fullLevi_lift P g hgF).choose_spec.2
  have he' : elementaryInclusion P e ∈
      (splitLevi P .arms : Set (SplitGroup P)) * splitCentralTorus P .arms :=
    (Set.ext_iff.mp (splitFullLevi_eq_mul_centralTorus P hp .arms)
      (elementaryInclusion P e)).mp he
  obtain ⟨l, hl, t, ht, hlt⟩ := he'
  have hfix : graphFieldAutomorphism P (l * t) = l * t :=
    (congrArg (graphFieldAutomorphism P) hlt).trans (e.val.property.trans hlt.symm)
  have htf := (splitFullLevi_central_factors_fixed P hp .arms l t hl ht hfix).2
  let te : ElementaryGroup P := ⟨⟨t, htf⟩, fixedTorus_le_elementary P hp ht.1⟩
  let le : ElementaryGroup P := e * te⁻¹
  have hle : elementaryInclusion P le = l := by
    change elementaryInclusion P e * t⁻¹ = l
    rw [← hlt, mul_inv_cancel_right]
  have hlL : toCarrier P le ∈ levi P .arms := by
    refine ⟨le, ?_, rfl⟩
    change elementaryInclusion P le ∈ splitLevi P .arms
    rw [hle]
    exact hl
  have hprod : toCarrier P le * toCarrier P te = g :=
    (map_mul (toCarrier P) le te).symm.trans
      ((congrArg (toCarrier P) (inv_mul_cancel_right e te)).trans heq)
  exact ⟨te, central_factor_eq P hp _ _ _ hlL (central_torus_descends P te ht) hg hprod, ht⟩

private theorem positiveRoot_injective (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    Function.Injective (positiveRoot P i) := by
  intro s t he
  have h := (pinnedRankOneMaps P hp).injective i
    (((pinnedRankOneMaps P hp).positive i s).trans
      (he.trans ((pinnedRankOneMaps P hp).positive i t).symm))
  have hh := congrArg (fun A : SL(2, ExtensionField P) => A.val 0 1) h
  simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection] using hh

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

private theorem central_coordinates (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.Coordinates P)
    (ht : product P a ∈ splitCentralTorus P .arms)
    (hf : product P a ∈ fixedSubgroup P) :
    ∃ s : (fixedField P)ˣ, a = ![fixedUnit P s, fixedUnit P s ^ 2,
      fixedUnit P s, fixedUnit P s] := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
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
  -- The three simple-arm characters equate their squares to the central coordinate.
  have hsq (i : Fin 4) (hi : i ≠ 1) : (a i).val ^ 2 = (a 1).val := by
    have hh : (a i).val ^ 2 * (a 1).val⁻¹ = 1 := by
      fin_cases i
      · simpa [typeDCartanMatrix] using hs 0 (by decide)
      · exact False.elim (hi rfl)
      · simpa [typeDCartanMatrix] using hs 2 (by decide)
      · simpa [typeDCartanMatrix] using hs 3 (by decide)
    exact (mul_inv_eq_one₀ (Units.ne_zero (a 1))).mp hh
  have h2 : a 2 = a 0 := Units.ext (CharTwo.sq_injective
    ((hsq 2 (by decide)).trans (hsq 0 (by decide)).symm))
  have h3 : a 3 = a 0 := Units.ext (CharTwo.sq_injective
    ((hsq 3 (by decide)).trans (hsq 0 (by decide)).symm))
  have h1 : a 1 = a 0 ^ 2 := Units.ext (hsq 0 (by decide)).symm
  have hfixed := (twist_eq_self_iff P a).mp ((product_mem_fixedSubgroup_iff P hp a).mp hf) 0
  have hF : frobenius P (a 0) = a 0 := by
    simpa only [typeD4DiagramPermutation, Equiv.coe_fn_mk, Matrix.cons_val_zero, h2] using hfixed.symm
  refine ⟨restrictUnit P (a 0) hF, ?_⟩
  rw [fixedUnit_restrictUnit]
  funext i
  fin_cases i <;> simp [h1, h2, h3]

private theorem long_zero_pairing (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex 3) (typeDSimpleRootIndex 2 i) =
      if i = 1 then 2 else -1 := by
  change (typeDRootPairing 2).pairingIn ℤ (difference 1 2 (by decide))
    (typeDSimpleRootIndex 2 i) = _
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = ((if i = 1 then 2 else -1 : ℤ) : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing]
  fin_cases i <;>
    norm_num [difference, sumRoot, typeDSimpleRootIndex,
      typeDRootEmbedding, typeDRootVector, basisVector, dot, Fin.sum_univ_succ]
  all_goals norm_num [Pi.single_apply, Fin.ext_iff]

private theorem long_one_pairing (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex 10) (typeDSimpleRootIndex 2 i) =
      if i = 1 then -1 else 1 := by
  change (typeDRootPairing 2).pairingIn ℤ (sumRoot 0 2 (by decide))
    (typeDSimpleRootIndex 2 i) = _
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = ((if i = 1 then -1 else 1 : ℤ) : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing]
  fin_cases i <;>
    norm_num [difference, sumRoot, typeDSimpleRootIndex,
      typeDRootEmbedding, typeDRootVector, basisVector, dot, Fin.sum_univ_succ]
  all_goals norm_num [Pi.single_apply, Fin.ext_iff]

private theorem central_long_conjugate (P : Parameters) (hp : P.prime = 2)
    (s : (fixedField P)ˣ) (i : Fin 2) (u : fixedField P) :
    product P ![fixedUnit P s, fixedUnit P s ^ 2, fixedUnit P s, fixedUnit P s] *
      longSplit P i.castSucc u *
        (product P ![fixedUnit P s, fixedUnit P s ^ 2, fixedUnit P s, fixedUnit P s])⁻¹ =
          longSplit P i.castSucc (s.val * u) := by
  have hs : (s.val : ExtensionField P) ≠ 0 := by exact_mod_cast Units.ne_zero s
  change (torusWord P 0 (fixedUnit P s) * torusWord P 2 (fixedUnit P s) *
    torusWord P 3 (fixedUnit P s) * torusWord P 1 (fixedUnit P s ^ 2)) *
    curve P (longPosition i.castSucc) u.val *
    (torusWord P 0 (fixedUnit P s) * torusWord P 2 (fixedUnit P s) *
      torusWord P 3 (fixedUnit P s) * torusWord P 1 (fixedUnit P s ^ 2))⁻¹ =
      curve P (longPosition i.castSucc) (s.val.val * u.val)
  fin_cases i
  · change _ * curve P 3 u.val * _ = curve P 3 (s.val.val * u.val)
    simp only [conjugate_product, torusWord_curve_conjugate P hp, long_zero_pairing]
    norm_num [fixedUnit, Fin.ext_iff]
    congr 1
    field_simp
  · change _ * curve P 10 u.val * _ = curve P 10 (s.val.val * u.val)
    simp only [conjugate_product, torusWord_curve_conjugate P hp, long_one_pairing]
    norm_num [fixedUnit, Fin.ext_iff]
    congr 1
    field_simp

private theorem long_coordinates (P : Parameters) (hp : P.prime = 2)
    (a b c : fixedField P) :
    (armsEquiv P hp (0, ![a, b, c])).val =
      long P hp 0 a * long P hp 1 b * long P hp 2 c := by
  change toCarrier P (rootElement P hp .arms (0, ![a, b, c])) = _
  rw [rootElement_factorization]
  simp [extendOrbit]

private theorem long_inv (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (u : fixedField P) : (long P hp i u)⁻¹ = long P hp i u := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply inv_eq_of_mul_eq_one_right
  rw [← long_add, CharTwo.add_self_eq_zero, long_zero]

private theorem scalar_eq_one_of_squares (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (s : fixedField P)
    (hact : ∀ i : Fin 2, g * long P hp i.castSucc 1 * g⁻¹ = long P hp i.castSucc s)
    (hsq : ∀ r ∈ radical P .arms, ⁅r, g⁆ ^ 2 = 1) : s = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  -- The reversed conjugated long-root factors are collected in the published order.
  let v : ArmsParameters P := (0, ![1, 1, 0])
  let w : ArmsParameters P := (0, ![0, s, 0])
  let z : ArmsParameters P := (0, ![s, 0, 0])
  let d := armsMultiply P v (armsMultiply P w z)
  let r := long P hp 0 1 * long P hp 1 1
  have hr : r ∈ radical P .arms := by
    rw [radical_eq_descendedRootSubgroup P hp]
    exact Subgroup.mul_mem _ (long_mem P hp .arms 0 trivial 1)
      (long_mem P hp .arms 1 trivial 1)
  have hd : (armsEquiv P hp d).val = ⁅r, g⁆ := by
    have h0 := hact 0
    have h1 := hact 1
    change g * long P hp 0 1 * g⁻¹ = long P hp 0 s at h0
    change g * long P hp 1 1 * g⁻¹ = long P hp 1 s at h1
    dsimp only [d]
    rw [armsEquiv_multiply P hp, armsEquiv_multiply P hp]
    simp only [Subgroup.coe_mul]
    simp only [v, w, z, long_coordinates P hp, long_zero, one_mul, mul_one]
    rw [← h0, ← h1, commutatorElement_def]
    dsimp only [r]
    rw [mul_inv_rev, long_inv P hp, long_inv P hp]
    group
  have hc : armsCocycle P d d = (1 + s) ^ 2 := by
    simp [d, v, w, z, armsCocycle, armsMultiply, pow_two]
  have hd1 : armsEquiv P hp d ^ 2 = 1 := by
    apply Subtype.ext
    change (armsEquiv P hp d).val ^ 2 = 1
    rw [hd]
    exact hsq r hr
  rw [armsEquiv_square, hc, armsEquiv_central_eq_one_iff] at hd1
  have he : 1 + s = 0 := (sq_eq_zero_iff).mp hd1
  simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right he)

/-- A full arms Levi element centralizing the subsystem is identity if all its
pointwise radical commutators have square one. This includes q = 2. -/
public theorem arms_fullLevi_centralizer_square_rigidity
    (P : Parameters) (hp : P.prime = 2) (g : fullLevi P .arms)
    (hg : g ∈ Subgroup.centralizer ((levi P .arms).subgroupOf (fullLevi P .arms) :
      Set (fullLevi P .arms)))
    (hsq : ∀ r ∈ radical P .arms, ⁅r, g.val⁆ ^ 2 = 1) : g = 1 := by
  have hg' : g.val ∈ Subgroup.centralizer (levi P .arms : Set (Carrier P)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have hxF : x ∈ fullLevi P .arms := descendSubgroup_mono P le_sup_left hx
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg ⟨x, hxF⟩ hx)
  obtain ⟨e, he, het⟩ := centralizer_lift P hp g.val g.property hg'
  obtain ⟨a, ha⟩ := torus_parameters P hp (elementaryInclusion P e) het.1
  have hat : product P a ∈ splitCentralTorus P .arms := ha.symm ▸ het
  have haf : product P a ∈ fixedSubgroup P := ha.symm ▸ e.val.property
  obtain ⟨s, hs⟩ := central_coordinates P hp a hat haf
  have hval : elementaryInclusion P e =
      product P ![fixedUnit P s, fixedUnit P s ^ 2, fixedUnit P s, fixedUnit P s] :=
    ha.symm.trans (congrArg (product P) hs)
  have hact (i : Fin 2) :
      g.val * long P hp i.castSucc 1 * g.val⁻¹ = long P hp i.castSucc s.val := by
    have hh : e * longElementary P hp i.castSucc 1 * e⁻¹ =
        longElementary P hp i.castSucc s.val := by
      apply elementaryInclusion_injective P
      simpa only [map_mul, map_inv, longElementary_val, hval, mul_one] using
        central_long_conjugate P hp s i 1
    simpa only [map_mul, map_inv, he, long] using congrArg (toCarrier P) hh
  have hs1 : s = 1 := Units.ext (scalar_eq_one_of_squares P hp g.val s.val hact hsq)
  have he1 : elementaryInclusion P e = 1 := by
    rw [hval, hs1]
    have ht : (![fixedUnit P (1 : (fixedField P)ˣ), fixedUnit P (1 : (fixedField P)ˣ) ^ 2,
        fixedUnit P (1 : (fixedField P)ˣ), fixedUnit P (1 : (fixedField P)ˣ)] :
        TorusCoordinates.Coordinates P) = 1 := by
      funext i
      fin_cases i <;> simp
    rw [ht, product_one P hp]
  have hee : e = 1 := elementaryInclusion_injective P (he1.trans (map_one _).symm)
  apply Subtype.ext
  exact he.symm.trans ((congrArg (toCarrier P) hee).trans (map_one _))

end
end Triality.Standard.Parabolics
