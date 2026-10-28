module

public import Theory.SpecificGroups.Triality.StandardTwoRank
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.RootArithmetic

/-!
# Perfectness of the genuine binary triality carrier

The three-arm Levi is perfect over the cubic field, including at q = 2.
Its positive short-root group therefore lies in the carrier's commutator.
The exchange of the first two long-root groups expresses every highest-root
value as a commutator, without a restriction on q. The actual folded Weyl
matrices carry these two root groups to all six positive folded root groups.
The fixed positive normal form then gives the whole unipotent subgroup;
rank-one conjugation and torus words give the Borel and both negative simple
root groups. The proved two-parabolic generation completes perfectness.

Every step uses the original elementary graph-field fixed subgroup and its
central quotient. No simplicity assertion or auxiliary triality carrier is
used. The equivalence at the end is the literal inclusion of the commutator.

Sources: GLS3, Theorem 2.2.7(b) and the root and Bruhat relations in §§2.3–2.6
(`refs/KGroup/GLS3/chapter2.tex`); the smaller-field derived group in
Aschbacher–Smith 16.1.4(4), printed p.1171 (`refs/quasithin.pdf`). Triality at
q = 2 is not one of the eight exceptions in GLS3 2.2.7.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Triality.Standard
open Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.RadicalCoordinates.LeviCommutators
open scoped commutatorElement
noncomputable section
namespace Triality.Standard.TwoRank.Perfectness

private def numbering : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbering_generator (i : Fin 4) :
    numbering (rootWeylGenerator i) = DiagramFixed.reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm ((typeDRootPairing 2).reflectionPerm
    (typeDSimpleRootIndex 2 i) (rootEnumeration r)) = reflectionTable i r
  rw [← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma representative_numbered (w : DihedralGroup 6) (r : Fin 24) :
    (rootRepresentative w).val (rootEnumeration r) =
      rootEnumeration (DiagramFixed.representativeTable w r) := by
  have h : numbering (rootRepresentative w) = DiagramFixed.representative w := by
    cases w <;> simp [rootRepresentative, DiagramFixed.representative, foldedRootReflection,
      map_mul, map_pow, numbering_generator, DiagramFixed.arm]
  have hh := congrFun (congrArg (fun e : Equiv.Perm (Fin 24) => (e : Fin 24 → Fin 24)) h) r
  change rootEnumeration.symm ((rootRepresentative w).val (rootEnumeration r)) = _ at hh
  exact (rootEnumeration.apply_symm_apply _).symm.trans
    (congrArg rootEnumeration (hh.trans (DiagramFixed.representative_apply w r)))

private theorem conjugate_curve (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 12)
    (h : DiagramFixed.representativeTable w (positiveIndex i) = positiveIndex j)
    (t : ExtensionField P) :
    splitRepresentative P hp w * curve P i t * (splitRepresentative P hp w)⁻¹ =
      curve P j t := by
  apply Subtype.ext
  change (splitRepresentative P hp w).val * _ * (splitRepresentative P hp w).val⁻¹ = _
  rw [curve_unit, splitRepresentative_rootCurveUnit_conjugation,
    ← rootEnumeration_positiveIndex, representative_numbered, h, rootEnumeration_positiveIndex]
  rfl

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x*y) * g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem short_one_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    splitRepresentative P hp (.r 2) * shortSplit P 0 t *
      (splitRepresentative P hp (.r 2))⁻¹ = shortSplit P 1 t := by
  simp only [shortSplit, conjugate_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (conjugate_curve P hp (.r 2) 0 4 (by decide) t)
    (conjugate_curve P hp (.r 2) 1 5 (by decide) (fieldFrobenius P t)))
    (conjugate_curve P hp (.r 2) 2 6 (by decide) (fieldFrobenius P (fieldFrobenius P t)))

private theorem short_two_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    splitRepresentative P hp (.r 1) * shortSplit P 0 (fieldFrobenius P t) *
      (splitRepresentative P hp (.r 1))⁻¹ = shortSplit P 2 t := by
  simp only [shortSplit, conjugate_mul]
  calc
    _ = curve P 8 (fieldFrobenius P t) *
        curve P 9 (fieldFrobenius P (fieldFrobenius P t)) *
        curve P 7 (fieldFrobenius P (fieldFrobenius P (fieldFrobenius P t))) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·)
        (conjugate_curve P hp (.r 1) 0 8 (by decide) (fieldFrobenius P t))
        (conjugate_curve P hp (.r 1) 1 9 (by decide) (fieldFrobenius P (fieldFrobenius P t))))
        (conjugate_curve P hp (.r 1) 2 7 (by decide)
          (fieldFrobenius P (fieldFrobenius P (fieldFrobenius P t))))
    _ = _ := by
      rw [fieldFrobenius_three]
      exact ((shortSplit_curves_commute P 2 0 1 t (fieldFrobenius P t)).mul_right
        (shortSplit_curves_commute P 2 0 2 t (fieldFrobenius P (fieldFrobenius P t)))).eq.symm.trans
          (mul_assoc _ _ _).symm

private def longWeyl : Fin 3 → DihedralGroup 6 := ![.r 1, .r 5, .r 0]

private theorem long_conjugate (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : fixedField P) :
    splitRepresentative P hp (longWeyl i) * longSplit P 2 t *
      (splitRepresentative P hp (longWeyl i))⁻¹ = longSplit P i t := by
  apply conjugate_curve
  fin_cases i <;> decide

private theorem long_two_mem_commutator (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) : long P hp 2 t ∈ commutator (Carrier P) := by
  have he := long_zero_one_exchange P hp t 1
  rw [mul_one] at he
  have hz : long P hp 2 t = ⁅(long P hp 0 t)⁻¹, (long P hp 1 1)⁻¹⁆ := by
    apply mul_left_cancel (a := long P hp 1 1 * long P hp 0 t)
    rw [← he]
    simp only [commutatorElement_def]
    group
  rw [hz]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)


private theorem carrier_conjugate (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (x y : ElementaryGroup P)
    (h : splitRepresentative P hp w * elementaryInclusion P x *
      (splitRepresentative P hp w)⁻¹ = elementaryInclusion P y) :
    weylRepresentative P hp w * toCarrier P x * (weylRepresentative P hp w)⁻¹ =
      toCarrier P y := by
  have he : weylElementary P hp w * x * (weylElementary P hp w)⁻¹ = y := by
    apply elementaryInclusion_injective P
    exact (by simpa only [map_mul, map_inv, splitRepresentative] using h)
  exact (by simpa only [map_mul, map_inv, weylRepresentative] using congrArg (toCarrier P) he)

private theorem shortSplit_zero (P : Parameters) (t : ExtensionField P) :
    shortSplit P 0 t = positiveRoot P 0 t * positiveRoot P 2 (fieldFrobenius P t) *
      positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t)) := by
  change curve P (simplePosition 0) t * curve P (simplePosition 2) (fieldFrobenius P t) *
    curve P (simplePosition 3) (fieldFrobenius P (fieldFrobenius P t)) = _
  rw [curve_simple, curve_simple, curve_simple]

private theorem short_zero_mem_commutator (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) : short P hp 0 t ∈ commutator (Carrier P) := by
  have hle : levi P .arms ≤ commutator (Carrier P) := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact armsLevi_le_commutator n hn
  apply hle
  refine ⟨shortElementary P hp 0 t, ?_, rfl⟩
  change elementaryInclusion P _ ∈ splitLevi P .arms
  rw [shortElementary_val, shortSplit_zero]
  have hpos (i : Fin 4) (hi : i ≠ 1) (u : ExtensionField P) :
      positiveRoot P i u ∈ splitLevi P .arms :=
    Subgroup.subset_closure ⟨i, hi, u, Or.inl rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (hpos 0 (by decide) _) (hpos 2 (by decide) _)) (hpos 3 (by decide) _)

private theorem short_mem_commutator (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (t : ExtensionField P) : short P hp i t ∈ commutator (Carrier P) := by
  have hconj (w : DihedralGroup 6) (u : ExtensionField P)
      (h : splitRepresentative P hp w * shortSplit P 0 u *
        (splitRepresentative P hp w)⁻¹ = shortSplit P i t) :
      short P hp i t ∈ commutator (Carrier P) := by
    have he := carrier_conjugate P hp w (shortElementary P hp 0 u)
      (shortElementary P hp i t) (by simpa only [shortElementary_val] using h)
    change toCarrier P (shortElementary P hp i t) ∈ _
    rw [← he]
    exact (inferInstance : (commutator (Carrier P)).Normal).conj_mem _
      (short_zero_mem_commutator P hp u) _
  fin_cases i
  · exact short_zero_mem_commutator P hp t
  · exact hconj (.r 2) t (short_one_conjugate P hp t)
  · exact hconj (.r 1) (fieldFrobenius P t) (short_two_conjugate P hp t)

private theorem long_mem_commutator (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (t : fixedField P) : long P hp i t ∈ commutator (Carrier P) := by
  have he := carrier_conjugate P hp (longWeyl i) (longElementary P hp 2 t)
    (longElementary P hp i t) (by simpa only [longElementary_val] using long_conjugate P hp i t)
  change toCarrier P (longElementary P hp i t) ∈ _
  rw [← he]
  exact (inferInstance : (commutator (Carrier P)).Normal).conj_mem _
    (long_two_mem_commutator P hp t) _

private theorem positive_range (P : Parameters) (hp : P.prime = 2) :
    Set.range (orderedProduct P) = (positiveSubgroup P : Set (SplitGroup P)) := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact range_orderedProduct_binary n hn

private theorem positive_twist (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) :
    graphFieldAutomorphism P (orderedProduct P v) = orderedProduct P (twist P v) := by
  revert v
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact graphField_orderedProduct_binary n hn

private theorem exists_positive_parameters (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hg : g ∈ positiveSubgroup P) (hfixed : g ∈ fixedSubgroup P) :
    ∃ v : PositiveCoordinates.OrbitParameters P, orderedProduct P (expand P v) = g := by
  obtain ⟨v, hv⟩ : ∃ v, orderedProduct P v = g := by
    rw [← Set.mem_range, positive_range P hp]
    exact hg
  have hfix : twist P v = v := by
    apply orderedProduct_injective P
    rw [← positive_twist P hp, hv]
    exact hfixed
  obtain ⟨u, hu⟩ := (fixedCoordinatesEquiv P).surjective ⟨v, hfix⟩
  exact ⟨u, (congrArg (orderedProduct P) (congrArg Subtype.val hu)).trans hv⟩

private theorem map_comap_le_of_parameters {G E Q A : Type*}
    [Group G] [Group E] [Group Q] (inc : E →* G) (π : E →* Q)
    (U F : Subgroup G) (H : Subgroup Q) (r : A → E) (s : A → G)
    (hi : Function.Injective inc) (hr : ∀ v, inc (r v) = s v)
    (hf : ∀ y, inc y ∈ F)
    (hs : ∀ g, g ∈ U → g ∈ F → ∃ v, s v = g)
    (hmem : ∀ v, π (r v) ∈ H) : (U.comap inc).map π ≤ H := by
  rintro g ⟨x, hx, rfl⟩
  obtain ⟨v, hv⟩ := hs (inc x) hx (hf x)
  have he : r v = x := hi ((hr v).trans hv)
  exact he ▸ hmem v

private def positiveElementary (P : Parameters) (hp : P.prime = 2)
    (v : PositiveCoordinates.OrbitParameters P) : ElementaryGroup P :=
  shortElementary P hp 0 (v.1 0) * longElementary P hp 0 (v.2 0) *
    shortElementary P hp 1 (v.1 1) * shortElementary P hp 2 (v.1 2) *
    longElementary P hp 1 (v.2 1) * longElementary P hp 2 (v.2 2)

private theorem positiveElementary_val (P : Parameters) (hp : P.prime = 2)
    (v : PositiveCoordinates.OrbitParameters P) :
    elementaryInclusion P (positiveElementary P hp v) = orderedProduct P (expand P v) := by
  simp only [positiveElementary, map_mul, shortElementary_val, longElementary_val]
  exact (orderedProduct_expand P v).symm

private theorem positiveElementary_mem_commutator (P : Parameters) (hp : P.prime = 2)
    (v : PositiveCoordinates.OrbitParameters P) :
    toCarrier P (positiveElementary P hp v) ∈ commutator (Carrier P) := by
  simp only [positiveElementary, map_mul]
  change short P hp 0 (v.1 0) * long P hp 0 (v.2 0) * short P hp 1 (v.1 1) *
    short P hp 2 (v.1 2) * long P hp 1 (v.2 1) * long P hp 2 (v.2 2) ∈ commutator (Carrier P)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (short_mem_commutator P hp 0 _) (long_mem_commutator P hp 0 _))
      (short_mem_commutator P hp 1 _)) (short_mem_commutator P hp 2 _))
      (long_mem_commutator P hp 1 _)) (long_mem_commutator P hp 2 _)

private theorem unipotent_le_commutator (P : Parameters) (hp : P.prime = 2) :
    unipotent P ≤ commutator (Carrier P) :=
  map_comap_le_of_parameters (elementaryInclusion P) (toCarrier P)
    (positiveSubgroup P) (fixedSubgroup P) (commutator (Carrier P))
    (positiveElementary P hp) (fun v => orderedProduct P (expand P v))
    (elementaryInclusion_injective P) (positiveElementary_val P hp)
    (fun x => x.val.property) (exists_positive_parameters P hp)
    (positiveElementary_mem_commutator P hp)

private theorem positive_root_mem_commutator (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) :
    ConcreteBruhat.rootElement P hp true a t ∈ commutator (Carrier P) :=
  unipotent_le_commutator P hp (positive_mem_unipotent P hp a t)

private theorem negative_root_mem_commutator (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) :
    ConcreteBruhat.rootElement P hp false a t ∈ commutator (Carrier P) := by
  have hi : (simpleRepresentative P hp a)⁻¹ = simpleRepresentative P hp a :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using simpleRepresentative_sq P hp a)
  have he : simpleRepresentative P hp a * ConcreteBruhat.rootElement P hp true a t *
      (simpleRepresentative P hp a)⁻¹ = ConcreteBruhat.rootElement P hp false a t := by
    rw [hi]
    exact simpleRepresentative_positive P hp a t
  rw [← he]
  exact (inferInstance : (commutator (Carrier P)).Normal).conj_mem _
    (positive_root_mem_commutator P hp a t) _

private theorem torus_le_commutator (P : Parameters) (hp : P.prime = 2) :
    torus P ≤ commutator (Carrier P) := by
  have hw (a : Node) (t : RootField P a) :
      toCarrier P (TorusCoordinates.foldedWeylElementary P hp a t) ∈
        commutator (Carrier P) := by
    simp only [TorusCoordinates.foldedWeylElementary, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (positive_root_mem_commutator P hp a _) (negative_root_mem_commutator P hp a _))
      (positive_root_mem_commutator P hp a _)
  have ht (a : Node) (t : (RootField P a)ˣ) :
      toCarrier P (TorusCoordinates.foldedTorusElementary P hp a t) ∈
        commutator (Carrier P) := by
    simp only [TorusCoordinates.foldedTorusElementary, map_mul]
    exact Subgroup.mul_mem _ (hw a _) (hw a _)
  intro g hg
  obtain ⟨v, hv⟩ := (TorusCoordinates.torusMulEquiv P hp).surjective ⟨g, hg⟩
  have he : toCarrier P (TorusCoordinates.orbitElementary P hp v) = g :=
    congrArg Subtype.val hv
  rw [← he]
  simp only [TorusCoordinates.orbitElementary, map_mul]
  exact Subgroup.mul_mem _ (ht .arms _) (ht .central _)

private theorem borel_le_commutator (P : Parameters) (hp : P.prime = 2) :
    borel P ≤ commutator (Carrier P) := by
  intro g hg
  have hg' := hg
  rw [← SetLike.mem_coe, borel_eq_mul P hp] at hg'
  obtain ⟨u, hu, t, ht, rfl⟩ := hg'
  exact Subgroup.mul_mem _ (unipotent_le_commutator P hp hu) (torus_le_commutator P hp ht)

/-- The genuine characteristic-two carrier is generated by its commutators. -/
theorem commutator_eq_top (P : Parameters) (hp : P.prime = 2) :
    commutator (Carrier P) = ⊤ := by
  apply top_unique
  rw [← parabolic_sup_binary P hp]
  apply sup_le
  all_goals
    rw [← negativeGenerators_generate P hp]
    apply sup_le (borel_le_commutator P hp)
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨t, rfl⟩
    exact negative_root_mem_commutator P hp _ t

/-- Every positive binary exponent gives a perfect triality carrier, including one. -/
instance binaryCarrier_isPerfect (m : ℕ) (hm : 0 < m) :
    Group.IsPerfect (BinaryCarrier m hm) :=
  ⟨commutator_eq_top (binaryParameters m hm) rfl⟩

/-- The commutator is the full binary carrier, with no small-field exclusion. -/
theorem binary_commutator_eq_top (m : ℕ) (hm : 0 < m) :
    commutator (BinaryCarrier m hm) = ⊤ :=
  Group.IsPerfect.commutator_eq_top

/-- The derived group is isomorphic to its actual carrier by the inclusion map. -/
def binaryCommutatorEquiv (m : ℕ) (hm : 0 < m) :
    commutator (BinaryCarrier m hm) ≃* BinaryCarrier m hm :=
  (MulEquiv.subgroupCongr (binary_commutator_eq_top m hm)).trans Subgroup.topEquiv

@[simp] theorem binaryCommutatorEquiv_apply (m : ℕ) (hm : 0 < m)
    (x : commutator (BinaryCarrier m hm)) :
    binaryCommutatorEquiv m hm x = (x : BinaryCarrier m hm) := rfl

end Triality.Standard.TwoRank.Perfectness
