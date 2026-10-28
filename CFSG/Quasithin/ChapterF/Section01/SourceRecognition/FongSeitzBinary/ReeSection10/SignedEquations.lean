module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.RankOneCentralization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SynchronizedCommutators

/-!
# Supplied reflections on every synchronized signed root

The supplied involutions give a homomorphism from the actual sixteen-element
Weyl group into the source normalizer. Each signed root point is a conjugate
of its synchronized simple-root point by a short Weyl word. The finite
reflection table changes that word either literally or by the perpendicular
reflection. Relation (10.2)(iv) makes the latter centralize the simple root.
This proves the complete signed-root equations on the same quotient and the
same lifts, including the full binary case.

The final consumer applies to any assembled positive charts and Weyl data
whose points and reflections are the synchronized ones. It discharges the
`SourceSigned.Equations` field without a signed-equation premise. Mixed
positive equations and full-torus assembly retain their independent owners.

Source: Fong--Seitz II (1974), (10.2)(iv) and the supplied lift relation
(10.43); GLS3, 2.3.6--8 and Table 2.4.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4 BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

open RootPresentationRecognition

def sourceSimpleReflection (s : Bool) : Q.tits.N :=
  (c.reflections (if s then 1 else 0)).val

theorem sourceSimpleReflection_sq (s : Bool) : sourceSimpleReflection Q split c s ^ 2 = 1 := by
  cases s
  · apply Subtype.ext
    change ((c.reflections 0).val : X ⧸ Q.D) ^ 2 = 1
    simpa only [pow_two] using linearReflection_sq Q split c
  · exact sourceSuzukiReflection_square Q split c

theorem sourceSimpleReflection_mixed :
    (sourceSimpleReflection Q split c false * sourceSimpleReflection Q split c true)^8 = 1 :=
  sourceReflection_product_eight Q split c

def synchronizedWeyl : WeylPresentation.Weyl →* Q.tits.N :=
  WeylPresentation.lift (sourceSimpleReflection Q split c)
    (sourceSimpleReflection_sq Q split c) (sourceSimpleReflection_mixed Q split c)

@[simp] theorem synchronizedWeyl_simple (s : Bool) :
    synchronizedWeyl Q split c (WeylPresentation.simple s) = sourceSimpleReflection Q split c s :=
  WeylPresentation.lift_simple ..

open RootPresentationRecognition WeylPresentation SignedGeometry

def signedRootWord (kind : Bool) (r : Index) : WeylPresentation.Weyl :=
  positiveWord (simple false) (simple true) (if kind then .inr r.2 else .inl r.2) *
    (if r.1 then 1 else opposition)

def perpendicularWord (kind : Bool) : WeylPresentation.Weyl :=
  positiveWord (simple false) (simple true) (if kind then .inr 1 else .inl 3)

def perpendicularReflection (kind : Bool) : WeylPresentation.Weyl :=
  perpendicularWord kind * simple kind * (perpendicularWord kind)⁻¹

private theorem signedRootWord_step (kind s : Bool) (r : Index) :
    signedRootWord kind r * simple s = signedRootWord kind (step kind s r) ∨
    signedRootWord kind r * simple s =
      perpendicularReflection kind * signedRootWord kind (step kind s r) := by
  rcases r with ⟨p,i⟩
  cases kind <;> cases s <;> cases p <;> fin_cases i <;> decide

variable {Y : Type*} [Group Y] (f : WeylPresentation.Weyl →* Y)

def signedWordPoint (kind : Bool) (r : Index) (x : Y) : Y :=
  (f (signedRootWord kind r))⁻¹ * x * f (signedRootWord kind r)

private theorem simple_inv (s : Bool) : (f (simple s))⁻¹ = f (simple s) := by
  rw [← map_inv]
  congr 1
  cases s <;> decide

theorem signedWordPoint_reflection (kind s : Bool) (r : Index) (x : Y)
    (hc : Commute (f (perpendicularReflection kind)) x) :
    f (simple s) * signedWordPoint f kind r x * (f (simple s))⁻¹ =
      signedWordPoint f kind (step kind s r) x := by
  calc
    _ = (f (signedRootWord kind r * simple s))⁻¹ * x *
        f (signedRootWord kind r * simple s) := by
      rw [map_mul, mul_inv_rev, simple_inv]
      unfold signedWordPoint
      group
    _ = _ := by
      rcases signedRootWord_step kind s r with h | h
      · rw [h]
        rfl
      · rw [h,map_mul,mul_inv_rev]
        have hcx : (f (perpendicularReflection kind))⁻¹ * x *
            f (perpendicularReflection kind) = x := by
          rw [hc.inv_left.eq]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
        calc
          _ = (f (signedRootWord kind (step kind s r)))⁻¹ *
              ((f (perpendicularReflection kind))⁻¹ * x *
                f (perpendicularReflection kind)) *
              f (signedRootWord kind (step kind s r)) := by group
          _ = _ := by rw [hcx]; rfl




def synchronizedWeylPoint : WeylPresentation.Weyl →* X ⧸ Q.D :=
  Q.tits.N.subtype.comp (synchronizedWeyl Q split c)

@[simp] theorem synchronizedWeylPoint_simple (s : Bool) :
    synchronizedWeylPoint Q split c (simple s) = (sourceSimpleReflection Q split c s : X ⧸ Q.D) :=
  congrArg Subtype.val (synchronizedWeyl_simple Q split c s)

theorem synchronizedWeylPoint_positiveWord (i : PositiveTables.Root) :
    synchronizedWeylPoint Q split c (positiveWord (simple false) (simple true) i) =
      (positiveLift Q split (pinnedInput Q split c) i : X ⧸ Q.D) := by
  cases i with
  | inl i => fin_cases i <;>
      simp [positiveWord,positiveLift,map_mul,synchronizedWeylPoint_simple,sourceSimpleReflection,pinnedInput]
  | inr i => fin_cases i <;>
      simp [positiveWord,positiveLift,map_mul,synchronizedWeylPoint_simple,sourceSimpleReflection,pinnedInput]

theorem synchronizedPositivePoint_pair_word (i : Fin 4) (a : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inl i) a =
      (synchronizedWeylPoint Q split c (positiveWord (simple false) (simple true) (.inl i)))⁻¹ *
        (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D) *
          synchronizedWeylPoint Q split c (positiveWord (simple false) (simple true) (.inl i)) := by
  rw [synchronizedWeylPoint_positiveWord]
  exact positiveRootEquiv_apply Q split (pinnedInput Q split c) (.inl i) _

theorem synchronizedPositivePoint_quartet_word (i : Fin 4) (a b : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr i) (a,b) =
      (synchronizedWeylPoint Q split c (positiveWord (simple false) (simple true) (.inr i)))⁻¹ *
        (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) *
          synchronizedWeylPoint Q split c (positiveWord (simple false) (simple true) (.inr i)) := by
  rw [synchronizedWeylPoint_positiveWord]
  exact positiveRootEquiv_apply Q split (pinnedInput Q split c) (.inr i) _

private theorem perpendicularReflection_commutes {Y : Type*} [Group Y]
    (f : WeylPresentation.Weyl →* Y) (kind : Bool) (x : Y)
    (hc : Commute (f (simple kind))
      ((f (perpendicularWord kind))⁻¹*x*f (perpendicularWord kind))) :
    Commute (f (perpendicularReflection kind)) x := by
  have h := hc.map (MulAut.conj (f (perpendicularWord kind))).toMonoidHom
  change Commute (f (perpendicularWord kind) * f (simple kind) *
      (f (perpendicularWord kind))⁻¹)
    (f (perpendicularWord kind) *
      ((f (perpendicularWord kind))⁻¹ * x * f (perpendicularWord kind)) *
      (f (perpendicularWord kind))⁻¹) at h
  have he : f (perpendicularWord kind) *
      ((f (perpendicularWord kind))⁻¹ * x * f (perpendicularWord kind)) *
      (f (perpendicularWord kind))⁻¹ = x := by group
  rw [he] at h
  simpa only [perpendicularReflection,map_mul,map_inv] using h

theorem synchronizedLinear_perpendicularReflection (a : CoefficientField m) :
    Commute (synchronizedWeylPoint Q split c (perpendicularReflection false))
      (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D) := by
  apply perpendicularReflection_commutes
  have hc := mem_centralizer_iff.mp
    (rankOne_centralizes_perpendicularLinear Q split c (c.reflections 0).mem_rankOne)
    (synchronizedPositivePoint Q split c (.inl 3) a)
    (synchronizedPositiveChart Q split c (.inl 3) a).property
  rw [synchronizedPositivePoint_pair_word] at hc
  rw [synchronizedWeylPoint_simple]
  change Commute
    (sourceSimpleReflection Q split c false : X ⧸ Q.D)
    (((synchronizedWeylPoint Q split c) (perpendicularWord false))⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D) *
      (synchronizedWeylPoint Q split c) (perpendicularWord false))
  simpa [Commute, SemiconjBy, sourceSimpleReflection, perpendicularWord] using hc.symm

theorem synchronizedSuzuki_perpendicularReflection (a b : CoefficientField m) :
    Commute (synchronizedWeylPoint Q split c (perpendicularReflection true))
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  apply perpendicularReflection_commutes
  have hc := mem_centralizer_iff.mp
    (rankOne_centralizes_perpendicularSuzuki Q split c (c.reflections 1).mem_rankOne)
    (synchronizedPositivePoint Q split c (.inr 1) (a,b))
    (synchronizedPositiveChart Q split c (.inr 1) (a,b)).property
  rw [synchronizedPositivePoint_quartet_word] at hc
  rw [synchronizedWeylPoint_simple]
  change Commute
    (sourceSimpleReflection Q split c true : X ⧸ Q.D)
    (((synchronizedWeylPoint Q split c) (perpendicularWord true))⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) *
      (synchronizedWeylPoint Q split c) (perpendicularWord true))
  simpa [Commute, SemiconjBy, sourceSimpleReflection, perpendicularWord] using hc.symm

private theorem signedWordPoint_eq {Y : Type*} [Group Y]
    (f : WeylPresentation.Weyl →* Y) (kind : Bool) (r : Index) (x : Y) :
    signedWordPoint f kind r x =
      (if r.1 then (1 : MulAut Y) else MulAut.conj (f opposition))
        ((f (positiveWord (simple false) (simple true) (if kind then .inr r.2 else .inl r.2)))⁻¹ *
          x * f (positiveWord (simple false) (simple true) (if kind then .inr r.2 else .inl r.2))) := by
  rcases r with ⟨p,i⟩
  cases p
  · have hi : (f opposition)⁻¹ = f opposition := by
      rw [←map_inv]
      exact congrArg f (by decide)
    change (f (_ * opposition))⁻¹ * x * f (_ * opposition) =
      f opposition * ((f _)⁻¹ * x * f _) * (f opposition)⁻¹
    rw [map_mul, mul_inv_rev]
    simp only [hi, mul_assoc]
  · simp only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,MulAut.one_apply]

variable (d : SourcePositive.Charts Q split m) (T : SourceBorel.TorusData Q split d)
  (W : SourceNormalizer.WeylData Q split d T)
  (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a)
  (hW : ∀ s, W.n s = sourceSimpleReflection Q split c s)

include hW in
theorem sourceSigned_weyl_eq_synchronized :
    SourceSigned.weyl Q split d T W = synchronizedWeylPoint Q split c := by
  apply WeylPresentation.hom_ext
  intro s
  rw [SourceSigned.weyl_simple,synchronizedWeylPoint_simple,hW]

include hd hW in
theorem sourceSigned_pair_eq_word (r : Index) (a : CoefficientField m) :
    SourceSigned.pair Q split d T W r a =
      signedWordPoint (synchronizedWeylPoint Q split c) false r
        (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D) := by
  rw [signedWordPoint_eq]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←synchronizedPositivePoint_pair_word,←hd]
  unfold SourceSigned.pair SourceSigned.signConj
  rw [sourceSigned_weyl_eq_synchronized Q split c d T W hW]

include hd hW in
theorem sourceSigned_quartet_eq_word (r : Index) (a b : CoefficientField m) :
    SourceSigned.quartet Q split d T W r a b =
      signedWordPoint (synchronizedWeylPoint Q split c) true r
        (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  rw [signedWordPoint_eq]
  simp only [↓reduceIte]
  rw [←synchronizedPositivePoint_quartet_word,←hd]
  unfold SourceSigned.quartet SourceSigned.signConj
  rw [sourceSigned_weyl_eq_synchronized Q split c d T W hW]

include hd hW in
/-- The finite signed-root table is proved for these literal synchronized
charts. Only the already constructed chart and reflection identifications
are used; no signed-root equation is a premise. -/
theorem synchronizedSourceSigned_equations : SourceSigned.Equations Q split d T W where
  pair s r a := by
    rw [sourceSigned_pair_eq_word Q split c d T W hd hW,
      sourceSigned_pair_eq_word Q split c d T W hd hW,hW,
      ←synchronizedWeylPoint_simple]
    exact signedWordPoint_reflection _ false s r _ (synchronizedLinear_perpendicularReflection Q split c a)
  quartet s r a b := by
    rw [sourceSigned_quartet_eq_word Q split c d T W hd hW,
      sourceSigned_quartet_eq_word Q split c d T W hd hW,hW,
      ←synchronizedWeylPoint_simple]
    exact signedWordPoint_reflection _ true s r _ (synchronizedSuzuki_perpendicularReflection Q split c a b)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
