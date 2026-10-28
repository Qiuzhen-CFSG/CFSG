module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.Tail
public import Theory.SpecificGroups.Triality.RadicalCoordinates.ParabolicSplitting

/-!
# A full cubic-root actor in the central triality radical

Use the simple short root and the two highest long roots. Their coordinates
are (t,0,0;u,v), with t in GF(q³) and u,v in GF(q). The collected law
restricts to addition, so this is an actual elementary subgroup of order q⁵.
It differs from the existing tail (0,0,t;u,v): retaining the full first
cubic coordinate matters to the proposed E.1.14(2) lower-bound argument.
No claim about conjugates or confinement follows from this construction alone.

Source: GLS3 §§2.4--2.6, especially the root collection law; the prospective
consumer is Aschbacher--Smith E.1.14(2), printed p.214, citing Asc82a 4.7.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.Parabolics.CentralRootSquare
open _root_.Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
open _root_.Triality.Standard.TwoRank

def headParameters (P : Parameters) (v : TailParameters P) :
    RootOrbitParameters P .central := (![v.1, 0, 0], v.2)

theorem headParameters_add (P : Parameters) (v w : TailParameters P) :
    headParameters P (v + w) = multiply P (headParameters P v) (headParameters P w) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [headParameters, multiply, higherCoefficient, -fieldFrobenius_apply]
  · funext i
    fin_cases i <;> simp [headParameters, multiply, higherCoefficient, -fieldFrobenius_apply]

def headRadicalHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (TailParameters P) →* radical P .central where
  toFun v := coordinates P hp (headParameters P v.toAdd)
  map_one' := by
    apply Subtype.ext
    rw [coordinates_val, rootElement_factorization]
    simp [headParameters, extendOrbit]
  map_mul' v w := by
    change coordinates P hp (headParameters P (v.toAdd + w.toAdd)) = _
    rw [headParameters_add, coordinates_multiply]

theorem headRadicalHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (headRadicalHom P hp) := by
  intro v w h
  have he := (coordinates P hp).injective h
  change v.toAdd = w.toAdd
  apply Prod.ext
  · exact congrArg (fun x : RootOrbitParameters P .central => x.1 0) he
  · exact congrArg (fun x : RootOrbitParameters P .central => x.2) he

def headHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (TailParameters P) →* Carrier P :=
  (radical P .central).subtype.comp (headRadicalHom P hp)

theorem headHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (headHom P hp) :=
  Subtype.val_injective.comp (headRadicalHom_injective P hp)

def headSubgroup (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (headHom P hp).range

theorem headSubgroup_elementary (P : Parameters) (hp : P.prime = 2) :
    IsElementaryAbelian 2 (headSubgroup P hp) := by
  refine {
    toIsMulCommutative := inferInstanceAs (IsMulCommutative (headHom P hp).range)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  obtain ⟨a, ha⟩ := x.property
  change x.val ^ 2 = 1
  rw [← ha, ← map_pow, tail_pow_two P hp, map_one]

theorem card_headSubgroup (P : Parameters) (hp : P.prime = 2) :
    Nat.card (headSubgroup P hp) = P.q ^ 5 := by
  change Nat.card (headHom P hp).range = P.q ^ 5
  rw [← Nat.card_congr (MonoidHom.ofInjective (headHom_injective P hp)).toEquiv]
  exact card_tailParameters P

theorem headSubgroup_le_unipotent (P : Parameters) (hp : P.prime = 2) :
    headSubgroup P hp ≤ unipotent P := by
  have hr : radical P .central ≤ unipotent P := by
    rw [radical_eq_descendedRootSubgroup P hp]
    exact descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
  rintro x ⟨v, rfl⟩
  exact hr (headRadicalHom P hp v).property

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
