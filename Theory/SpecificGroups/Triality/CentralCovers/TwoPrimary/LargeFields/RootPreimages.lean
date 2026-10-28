module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.HighestLong
public import Theory.GroupTheory.Commutator.ScalarInvariantRoot
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl

/-!
# Abelian root preimages and canonical sections for binary triality

In any central extension of the genuine binary triality carrier, the full
preimage of each of the six positive folded root groups is abelian. For short
root 1, multiply the actual arms torus actor at t by the central actor at its
cubic norm. The published weights multiply to t²; the characteristic-two
Frobenius supplies every nonzero cubic-field scalar. Since this field has at
least eight elements, the scalar-invariant commutator pairing vanishes.

The genuine folded Weyl representatives transport this result to short roots
0 and 2, retaining the Frobenius shift on the latter. They also transport the
proved highest-long-root result to every long root. Thus no lower bound greater
than four on the fixed field is needed. Root-preimage commutation holds even
at q = 2; for q ≥ 4 it discharges the exact premise of the existing unique
torus-normalization construction on the literal universal central cover.

The Weyl calculations adapt the private calculations in
`StandardTwoRank.Perfectness`, using the public D₄ root action and the same
folded coordinates. The independent inter-root exchange calculation and final
kernel exclusion remain with the large-field assembly.

Sources: GLS3 §§2.4 and 6.1, especially the type III parameters of 2.4.1 and
the actual torus action in 2.4.7(f) (`refs/KGroup/GLS3/chapter2.tex` and
`chapter6.tex`); Aschbacher–Smith A.2.4 and I.1.3, PDF pp.44 and 418
(`refs/quasithin.pdf`). This is the individual-root lifting input to that
multiplier argument, not the full source multiplier theorem.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics ConcreteBruhat PositiveCoordinates RadicalCoordinates.LeviCommutators

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


private theorem short_one_carrier (Q : Parameters) (hp : Q.prime = 2)
    (t : ExtensionField Q) :
    weylRepresentative Q hp (.r 2) * short Q hp 0 t *
      (weylRepresentative Q hp (.r 2))⁻¹ = short Q hp 1 t := by
  exact carrier_conjugate Q hp (.r 2) (shortElementary Q hp 0 t)
    (shortElementary Q hp 1 t)
    (by simpa only [shortElementary_val] using short_one_conjugate Q hp t)

private theorem short_two_carrier (Q : Parameters) (hp : Q.prime = 2)
    (t : ExtensionField Q) :
    weylRepresentative Q hp (.r 1) * short Q hp 0 (fieldFrobenius Q t) *
      (weylRepresentative Q hp (.r 1))⁻¹ = short Q hp 2 t := by
  exact carrier_conjugate Q hp (.r 1) (shortElementary Q hp 0 (fieldFrobenius Q t))
    (shortElementary Q hp 2 t)
    (by simpa only [shortElementary_val] using short_two_conjugate Q hp t)

private theorem long_carrier (Q : Parameters) (hp : Q.prime = 2)
    (i : Fin 3) (t : fixedField Q) :
    weylRepresentative Q hp (longWeyl i) * long Q hp 2 t *
      (weylRepresentative Q hp (longWeyl i))⁻¹ = long Q hp i t := by
  exact carrier_conjugate Q hp (longWeyl i) (longElementary Q hp 2 t)
    (longElementary Q hp i t)
    (by simpa only [longElementary_val] using long_conjugate Q hp i t)

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

private theorem cubicNorm_nonzero (P : Parameters) (t : (ExtensionField P)ˣ) :
    cubicNorm P t.val ≠ 0 := by
  intro hz
  have hz' := congrArg (fun x : fixedField P => x.val) hz
  change t.val * fieldFrobenius P t.val *
    fieldFrobenius P (fieldFrobenius P t.val) = 0 at hz'
  exact mul_ne_zero (mul_ne_zero t.ne_zero ((map_ne_zero (fieldFrobenius P)).mpr t.ne_zero))
    ((map_ne_zero (fieldFrobenius P)).mpr ((map_ne_zero (fieldFrobenius P)).mpr t.ne_zero)) hz'

private theorem scalar_square (P : Parameters) (t : (ExtensionField P)ˣ)
    (x : ExtensionField P) :
    t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) *
      ((cubicNorm P t.val).val * x) = t.val ^ 2 * x := by
  have h1 := (map_ne_zero (fieldFrobenius P)).mpr t.ne_zero
  have h2 := (map_ne_zero (fieldFrobenius P)).mpr h1
  change t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) *
    ((t.val * fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) * x) = _
  field_simp

private theorem short_one_square_split (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (x : ExtensionField P) :
    let N : (fixedField P)ˣ := Units.mk0 (cubicNorm P t.val) (cubicNorm_nonzero P t)
    (elementaryInclusion P (torusElementary P hp .arms t) *
      elementaryInclusion P (torusElementary P hp .central N)) * shortSplit P 1 x *
      (elementaryInclusion P (torusElementary P hp .arms t) *
        elementaryInclusion P (torusElementary P hp .central N))⁻¹ =
      shortSplit P 1 (t.val ^ 2 * x) := by
  dsimp only
  let a := elementaryInclusion P (torusElementary P hp .arms t)
  let N : (fixedField P)ˣ := Units.mk0 (cubicNorm P t.val) (cubicNorm_nonzero P t)
  exact (conjugate_product a (elementaryInclusion P (torusElementary P hp .central N))
    (shortSplit P 1 x)).trans
    ((congrArg (fun y : SplitGroup P => a * y * a⁻¹)
      (torus_central_short_one_conjugate P hp N x)).trans
      ((torus_arms_short_one_conjugate P hp t (N.val.val * x)).trans
        (congrArg (shortSplit P 1) (scalar_square P t x))))

private theorem short_one_square_action (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) :
    ∃ g : Carrier P, ∀ x : ExtensionField P,
      g * short P hp 1 x * g⁻¹ = short P hp 1 (t.val ^ 2 * x) := by
  let N : (fixedField P)ˣ := Units.mk0 (cubicNorm P t.val) (cubicNorm_nonzero P t)
  refine ⟨torusActor P hp .arms t * torusActor P hp .central N, ?_⟩
  intro x
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simpa only [map_mul, map_inv, shortElementary_val] using short_one_square_split P hp t x

private theorem short_one_full_scalar (n : ℕ) (hn : 0 < n)
    (c : ExtensionField (binaryParameters n hn)) (hc : c ≠ 0) :
    ∃ g : BinaryCarrier n hn, ∀ x : ExtensionField (binaryParameters n hn),
      g * baseShortHom n hn 1 (.ofAdd x) * g⁻¹ =
        baseShortHom n hn 1 (.ofAdd (c * x)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := rankOneExtensionCharTwo (binaryParameters n hn) rfl
  obtain ⟨t, ht⟩ := (frobeniusEquiv (ExtensionField (binaryParameters n hn)) 2).surjective c
  have ht' : t ^ 2 = c := ht
  have ht0 : t ≠ 0 := by
    intro hz
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at ht'
    exact hc ht'.symm
  obtain ⟨g, hg⟩ := short_one_square_action (binaryParameters n hn) rfl (Units.mk0 t ht0)
  refine ⟨g, ?_⟩
  intro x
  change g * short (binaryParameters n hn) rfl 1 x * g⁻¹ =
    short (binaryParameters n hn) rfl 1 (c * x)
  simpa only [Units.val_mk0, ht'] using hg x

private theorem preimage_commute_of_conjugate
    {A C E G : Type*} [Group A] [Group C] [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (u : A →* G) (v : C →* G)
    (hu : ∀ a b : E, f a ∈ u.range → f b ∈ u.range → Commute a b)
    (g : G) (hg : ∀ x : C, ∃ y : A, g * u y * g⁻¹ = v x)
    {a b : E} (ha : f a ∈ v.range) (hb : f b ∈ v.range) : Commute a b := by
  obtain ⟨z, hz⟩ := hf g
  have hm (e : E) (he : f e ∈ v.range) : f (z⁻¹ * e * z) ∈ u.range := by
    obtain ⟨x, hx⟩ := he
    obtain ⟨y, hy⟩ := hg x
    refine ⟨y, ?_⟩
    rw [map_mul, map_mul, map_inv, hz, ← hx, ← hy]
    group
  have h := hu _ _ (hm a ha) (hm b hb)
  apply Commute.of_map (MulAut.conj z⁻¹).injective
  simpa only [MulAut.conj_apply, inv_inv] using h

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn
variable {E : Type*} [Group E] (f : E →* BinaryCarrier n hn)

private theorem short_one_preimage_commute
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {v w : E} (hv : f v ∈ (baseShortHom n hn 1).range)
    (hw : f w ∈ (baseShortHom n hn 1).range) : Commute v w := by
  let := rankOneExtensionCharTwo P rfl
  have hF : 4 < Nat.card (ExtensionField P) := by
    rw [card_extensionField]
    have hq := Parameters.q_ge_two P
    exact lt_of_lt_of_le (by decide : 4 < 2^3) (Nat.pow_le_pow_left hq 3)
  exact CentralExtension.commute_lifts_of_full_scalar_action hF f hf hk
    (baseShortHom n hn 1) (short_one_full_scalar n hn) hv hw

private theorem short_zero_preimage_commute
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {v w : E} (hv : f v ∈ (baseShortHom n hn 0).range)
    (hw : f w ∈ (baseShortHom n hn 0).range) : Commute v w := by
  refine preimage_commute_of_conjugate f hf (baseShortHom n hn 1)
    (baseShortHom n hn 0) (fun _ _ => short_one_preimage_commute n hn f hf hk)
    (weylRepresentative P rfl (.r 2))⁻¹ ?_ hv hw
  intro x
  refine ⟨x, ?_⟩
  have h := short_one_carrier P rfl x.toAdd
  change (weylRepresentative P rfl (.r 2))⁻¹ * short P rfl 1 x.toAdd *
    ((weylRepresentative P rfl (.r 2))⁻¹)⁻¹ = short P rfl 0 x.toAdd
  change weylRepresentative P rfl (.r 2) * short P rfl 0 x.toAdd *
    (weylRepresentative P rfl (.r 2))⁻¹ = short P rfl 1 x.toAdd at h
  rw [← h]
  group

/-- Every individual short-root preimage is abelian in a central extension. -/
theorem short_preimage_commute
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i : Fin 3) {v w : E} (hv : f v ∈ (baseShortHom n hn i).range)
    (hw : f w ∈ (baseShortHom n hn i).range) : Commute v w := by
  fin_cases i
  · exact short_zero_preimage_commute n hn f hf hk hv hw
  · exact short_one_preimage_commute n hn f hf hk hv hw
  · refine preimage_commute_of_conjugate f hf (baseShortHom n hn 0)
      (baseShortHom n hn 2) (fun _ _ => short_zero_preimage_commute n hn f hf hk)
      (weylRepresentative P rfl (.r 1)) ?_ hv hw
    intro x
    refine ⟨.ofAdd (fieldFrobenius P x.toAdd), ?_⟩
    change weylRepresentative P rfl (.r 1) * short P rfl 0 (fieldFrobenius P x.toAdd) *
      (weylRepresentative P rfl (.r 1))⁻¹ = short P rfl 2 x.toAdd
    exact short_two_carrier P rfl x.toAdd

/-- Genuine Weyl conjugation transports the highest-long-root result to all
three long roots, including over the fixed field of order four. -/
theorem long_preimage_commute
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i : Fin 3) {v w : E} (hv : f v ∈ (baseLongHom n hn i).range)
    (hw : f w ∈ (baseLongHom n hn i).range) : Commute v w := by
  refine preimage_commute_of_conjugate f hf (baseLongHom n hn 2)
    (baseLongHom n hn i) (fun _ _ => long_two_preimage_commute n hn f hf hk)
    (weylRepresentative P rfl (longWeyl i)) ?_ hv hw
  intro x
  refine ⟨x, ?_⟩
  change weylRepresentative P rfl (longWeyl i) * long P rfl 2 x.toAdd *
    (weylRepresentative P rfl (longWeyl i))⁻¹ = long P rfl i x.toAdd
  exact long_carrier P rfl i x.toAdd

/-- All six individual root preimages are abelian. This argument also covers
q = 2; the separate torus-normalization construction requires q ≥ 4. -/
theorem rootPreimagesAbelian
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    RootPreimagesAbelian n hn f :=
  ⟨fun i _ _ => short_preimage_commute n hn f hf hk i,
    fun i _ _ => long_preimage_commute n hn f hf hk i⟩

/-- The root-preimage input is discharged on the literal universal projection. -/
theorem universal_rootPreimagesAbelian :
    RootPreimagesAbelian n hn (PerfectCentralCovering.universalProjection (BinaryCarrier n hn)) :=
  rootPreimagesAbelian n hn _
    (PerfectCentralCovering.universalProjection_surjective _)
    (PerfectCentralCovering.universalProjection_ker_le_center _)

/-- The canonical cover has a unique family of torus-normalized additive root
sections. The independent inter-root exchange premise is not asserted here. -/
theorem universal_existsUnique_torusNormalized (hlarge : 2 ≤ n) :
    ∃! L : RootSections n hn (PerfectCentralCovering.universalProjection (BinaryCarrier n hn)),
      L.TorusNormalized :=
  existsUnique_torusNormalized_of_rootPreimagesAbelian n hn _ hlarge
    (PerfectCentralCovering.universalProjection_surjective _)
    (PerfectCentralCovering.universalProjection_ker_le_center _)
    (universal_rootPreimagesAbelian n hn)

/-- The canonical torus-normalized six-root family in the universal cover. -/
def universalTorusNormalizedRootSections (hlarge : 2 ≤ n) :
    RootSections n hn (PerfectCentralCovering.universalProjection (BinaryCarrier n hn)) :=
  (universal_existsUnique_torusNormalized n hn hlarge).exists.choose

/-- The canonical family satisfies the published normalization for both
actual folded tori and all their scalar actions. -/
theorem universalTorusNormalizedRootSections_torusNormalized (hlarge : 2 ≤ n) :
    (universalTorusNormalizedRootSections n hn hlarge).TorusNormalized :=
  (universal_existsUnique_torusNormalized n hn hlarge).exists.choose_spec

end Triality.Standard.CentralCovers.TwoPrimary
