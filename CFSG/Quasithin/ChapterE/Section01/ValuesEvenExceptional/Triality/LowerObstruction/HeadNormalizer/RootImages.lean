module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.Head
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.RootArithmetic

/-!
# Returning head images generate the triality positive subgroup

The q⁵ actor has folded roots α, 3α+β, 3α+2β. Conjugation by the central
reflection sends these to α+β, 3α+2β, 3α+β. The arm–central product sends
them to 2α+β, 3α+2β, β, with the published Frobenius rotation on the short
parameter. Thus both whole actor images remain positive, and the three
actors supply all six folded root groups. The original fixed positive
coordinate factorization proves generation, including q = 2.

All conjugations are direct (g x g⁻¹), first checked on the actual Geck
curves and then transported through the elementary central quotient.
The consumer is the weak closure of the full head automorphism family.

Source: GLS3 §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`), applied to the
normalizer input for Aschbacher–Smith E.1.14(2), printed p.214, citing
Asc82a, GF(2)-representations of finite groups, Lemma 4.7.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction.HeadNormalizer
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat _root_.Triality.Standard.PositiveCoordinates
open _root_.Triality.Standard.PositiveCoordinates.SumExchangeData
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.Parabolics.CentralRootSquare
open _root_.Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
open _root_.Triality.Standard.Parabolics.RankOneMatrices
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

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
    splitRepresentative P hp (.sr 1) * shortSplit P 0 t *
      (splitRepresentative P hp (.sr 1))⁻¹ = shortSplit P 1 t := by
  simp only [shortSplit, conjugate_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (conjugate_curve P hp (.sr 1) 0 4 (by decide) t)
    (conjugate_curve P hp (.sr 1) 1 5 (by decide) (fieldFrobenius P t)))
    (conjugate_curve P hp (.sr 1) 2 6 (by decide) (fieldFrobenius P (fieldFrobenius P t)))

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


private theorem short_one_image (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    MulAut.conj (weylRepresentative P hp (.sr 1)) (short P hp 0 t) = short P hp 1 t :=
  carrier_conjugate P hp (.sr 1) _ _ (by
    simpa only [shortElementary_val] using short_one_conjugate P hp t)

private theorem short_two_image (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    MulAut.conj (weylRepresentative P hp (.r 1)) (short P hp 0 (fieldFrobenius P t)) =
      short P hp 2 t :=
  carrier_conjugate P hp (.r 1) _ _ (by
    simpa only [shortElementary_val] using short_two_conjugate P hp t)

private theorem long_image (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 3)
    (h : DiagramFixed.representativeTable w (positiveIndex (longPosition i)) =
      positiveIndex (longPosition j)) (t : fixedField P) :
    MulAut.conj (weylRepresentative P hp w) (long P hp i t) = long P hp j t :=
  carrier_conjugate P hp w _ _ (by
    simpa only [longElementary_val, longSplit] using
      conjugate_curve P hp w (longPosition i) (longPosition j) h t.val)

private theorem headHom_eq (P : Parameters) (hp : P.prime = 2)
    (v : Multiplicative (_root_.Triality.Standard.TwoRank.TailParameters P)) :
    headHom P hp v =
      short P hp 0 v.toAdd.1 * long P hp 1 (v.toAdd.2 0) * long P hp 2 (v.toAdd.2 1) := by
  change (coordinates P hp (headParameters P v.toAdd)).val = _
  rw [coordinates_val, rootElement_factorization]
  simp [headParameters, extendOrbit]

private theorem short_head (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    short P hp 0 t ∈ headSubgroup P hp := by
  refine ⟨Multiplicative.ofAdd (t, 0), ?_⟩
  simp [headHom_eq]

private theorem long_head_one (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    long P hp 1 t ∈ headSubgroup P hp := by
  refine ⟨Multiplicative.ofAdd (0, ![t, 0]), ?_⟩
  simp [headHom_eq]

private theorem long_head_two (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    long P hp 2 t ∈ headSubgroup P hp := by
  refine ⟨Multiplicative.ofAdd (0, ![0, t]), ?_⟩
  simp [headHom_eq]

private theorem short_unipotent (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : ExtensionField P) : short P hp i t ∈ unipotent P :=
  descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
    (short_mem P hp .central i (by trivial) t)

private theorem long_unipotent (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : fixedField P) : long P hp i t ∈ unipotent P :=
  descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms)
    (long_mem P hp .arms i (by trivial) t)

private theorem head_image_central_le (P : Parameters) (hp : P.prime = 2) :
    (headSubgroup P hp).map (MulAut.conj (weylRepresentative P hp (.sr 1))).toMonoidHom ≤
      unipotent P := by
  rintro _ ⟨x, ⟨v, rfl⟩, rfl⟩
  change MulAut.conj (weylRepresentative P hp (.sr 1)) (headHom P hp v) ∈ _
  rw [headHom_eq P hp v, map_mul, map_mul, short_one_image,
    long_image P hp (.sr 1) 1 2 (by decide), long_image P hp (.sr 1) 2 1 (by decide)]
  exact (unipotent P).mul_mem ((unipotent P).mul_mem
    (short_unipotent P hp 1 _) (long_unipotent P hp 2 _)) (long_unipotent P hp 1 _)

private theorem head_image_rotation_le (P : Parameters) (hp : P.prime = 2) :
    (headSubgroup P hp).map (MulAut.conj (weylRepresentative P hp (.r 1))).toMonoidHom ≤
      unipotent P := by
  rintro _ ⟨x, ⟨v, rfl⟩, rfl⟩
  change MulAut.conj (weylRepresentative P hp (.r 1)) (headHom P hp v) ∈ _
  have hs : MulAut.conj (weylRepresentative P hp (.r 1)) (short P hp 0 v.toAdd.1) =
      short P hp 2 (fieldFrobenius P (fieldFrobenius P v.toAdd.1)) := by
    simpa only [fieldFrobenius_three] using
      short_two_image P hp (fieldFrobenius P (fieldFrobenius P v.toAdd.1))
  rw [headHom_eq P hp v, map_mul, map_mul, hs,
    long_image P hp (.r 1) 1 2 (by decide), long_image P hp (.r 1) 2 0 (by decide)]
  exact (unipotent P).mul_mem ((unipotent P).mul_mem
    (short_unipotent P hp 2 _) (long_unipotent P hp 2 _)) (long_unipotent P hp 0 _)

private theorem positive_factorization (P : Parameters) (hp : P.prime = 2)
    (x : ElementaryGroup P) (v : OrbitParameters P)
    (hs : orderedProduct P (expand P v) = elementaryInclusion P x) :
    toCarrier P x = short P hp 0 (v.1 0) * long P hp 0 (v.2 0) *
      short P hp 1 (v.1 1) * short P hp 2 (v.1 2) *
        long P hp 1 (v.2 1) * long P hp 2 (v.2 2) := by
  have hx' : x = shortElementary P hp 0 (v.1 0) * longElementary P hp 0 (v.2 0) *
      shortElementary P hp 1 (v.1 1) * shortElementary P hp 2 (v.1 2) *
      longElementary P hp 1 (v.2 1) * longElementary P hp 2 (v.2 2) := by
    apply elementaryInclusion_injective P
    simp only [map_mul, shortElementary_val P hp, longElementary_val P hp]
    exact hs.symm.trans (orderedProduct_expand P v)
  exact (congrArg (toCarrier P) hx').trans (by simp only [map_mul]; rfl)

/-- The head and its two returning Weyl images generate all six positive
folded root groups. This includes the binary endpoint. -/
theorem unipotent_le_of_head_images (f : ℕ) (hf : 0 < f)
    (H : Subgroup (BinaryCarrier f hf))
    (hH : ∀ β : MulAut (BinaryCarrier f hf),
      (headSubgroup (binaryParameters f hf) rfl).map β.toMonoidHom ≤
        unipotent (binaryParameters f hf) →
      (headSubgroup (binaryParameters f hf) rfl).map β.toMonoidHom ≤ H) :
    unipotent (binaryParameters f hf) ≤ H := by
  let P := binaryParameters f hf
  have hseed : headSubgroup P rfl ≤ H := by
    have h := hH (MulEquiv.refl _) (by
      simpa using headSubgroup_le_unipotent P rfl)
    simpa using h
  have hc := hH (MulAut.conj (weylRepresentative P rfl (.sr 1)))
    (head_image_central_le P rfl)
  have hr := hH (MulAut.conj (weylRepresentative P rfl (.r 1)))
    (head_image_rotation_le P rfl)
  have hs (i : Fin 3) (t : ExtensionField P) : short P rfl i t ∈ H := by
    fin_cases i
    · exact hseed (short_head P rfl t)
    · exact hc ⟨short P rfl 0 t, short_head P rfl t, short_one_image P rfl t⟩
    · exact hr ⟨short P rfl 0 (fieldFrobenius P t), short_head P rfl _,
        short_two_image P rfl t⟩
  have hl (i : Fin 3) (t : fixedField P) : long P rfl i t ∈ H := by
    fin_cases i
    · exact hr ⟨long P rfl 2 t, long_head_two P rfl t,
        long_image P rfl (.r 1) 2 0 (by decide) t⟩
    · exact hseed (long_head_one P rfl t)
    · exact hseed (long_head_two P rfl t)
  rintro g ⟨x, hx, rfl⟩
  let e := orbitPositiveEquiv_binary f hf
  let y : (positiveSubgroup P).comap (fixedSubgroup P).subtype := ⟨x.val, hx⟩
  let v := e.symm y
  have hv : orderedProduct P (expand P v) = elementaryInclusion P x :=
    (orbitPositiveEquiv_binary_val f hf v).symm.trans
      (congrArg (fun z => z.val.val) (e.apply_symm_apply y))
  rw [positive_factorization P rfl x v hv]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (hs 0 _) (hl 0 _)) (hs 1 _)) (hs 2 _)) (hl 1 _)) (hl 2 _)

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction.HeadNormalizer
