module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.SourceFourGroup
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.LinearCalculation

/-!
# Assembly of the Sylow-five action and fusion calculation

The actual complement and its faithful conjugation action were constructed
in `SylowAction.Reduction`. Here the two marked linear orbits imply coverage
of every order-five subgroup, after embedding that subgroup in a Sylow
subgroup. A dihedral identification of the conjugation image supplies the
required internal D₁₂ complement, its faithful action, and normalizer order.

The source four-group geometry and the small linear calculation are discharged
in `family`. Thus the preceding root and two-central families imply the final
paragraph of Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261
(PDF p.136). Those two earlier branches remain explicit inputs, produced by
the root-component and two-central tasks and discharged by the five-local
assembly owner. `exists_frame_two_orbits` retains the actual two three-line
orbits, and `normalizer_data` supplies the faithful action and order 300.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction

variable {G : Type*} [Group G] [Finite G]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Once the actual linear calculation is proved, its two orbits give the
source coverage for every line of this particular Sylow subgroup. -/
theorem SourceFrame.coverage {D : Seed G} {t : G} {P : Sylow 5 G}
    (F : SourceFrame D t P) (hF : TwoOrbitConclusion F.frame)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEP : E ≤ (P : Subgroup G)) :
    FiveCentralizing t E ∨ FiveCentralizing D.z E := by
  have hcard : Nat.card (E.subgroupOf (P : Subgroup G)) = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv).trans hE
  have he : lineImage P (E.subgroupOf (P : Subgroup G)) = E :=
    map_subgroupOf_eq_of_le hEP
  rcases hF.coverage _ hcard with h | h
  · exact Or.inl (he ▸ fiveCentralizing_of_lineOrbit P F.root h)
  · exact Or.inr (he ▸ fiveCentralizing_of_lineOrbit P F.twoCentral h)

/-- Conditional assembly from the local four-group and the small linear
calculation. The source specialization `family` discharges both premises. -/
theorem family_of_frames_and_linear_calculation {D : Seed G} {t : G}
    (hG : Nat.card G = 604800) (hB : TwoCentralFiveFamily D t)
    (hframes : ∀ P : Sylow 5 G, Nonempty (SourceFrame D t P))
    (hlinear : ∀ P : Sylow 5 G, IsElementaryAbelian 5 P → Nat.card P = 25 →
      Nat.card (automizer P) ≡ 2 [MOD 5] →
      ∀ F : FourLineFrame (automizer P), TwoOrbitConclusion F) :
    SylowFiveFamily D t := by
  have hcalc (P : Sylow 5 G) (F : FourLineFrame (automizer P)) : TwoOrbitConclusion F :=
    hlinear P (hB.elementary P) (sylow_card hG P)
      (automizer_card_mod hG P (hB.self_centralizing P)) F
  constructor
  · intro P
    obtain ⟨F⟩ := hframes P
    obtain ⟨e⟩ := (hcalc P F.frame).dihedral
    exact ⟨splitWitnessOfAutomizer P (hB.self_centralizing P) e⟩
  · intro E hE
    have hp : IsPGroup 5 E := IsPGroup.of_card (n := 1) (by simpa using hE)
    obtain ⟨P, hEP⟩ := hp.exists_le_sylow
    obtain ⟨F⟩ := hframes P
    exact F.coverage (hcalc P F.frame) E hE hEP
/-- Source specialization of the faithful GL₂(5) order bound. -/
theorem SourceFrame.automizer_card_cases {D : Seed G} {t : G} {P : Sylow 5 G}
    (F : SourceFrame D t P) (hG : Nat.card G = 604800)
    (hB : TwoCentralFiveFamily D t) :
    Nat.card (automizer P) = 12 ∨ Nat.card (automizer P) = 32 := by
  have : IsElementaryAbelian 5 P := hB.elementary P
  exact F.frame.card_cases (sylow_card hG P)
    (automizer_card_mod hG P (hB.self_centralizing P))

/-- The source action model gives the normalizer order and the literal faithful
D₁₂ action, using the already proved consequences of the internal complement. -/
theorem SourceFrame.normalizer_data {D : Seed G} {t : G} {P : Sylow 5 G}
    (F : SourceFrame D t P) (hF : TwoOrbitConclusion F.frame)
    (hG : Nat.card G = 604800) (hB : TwoCentralFiveFamily D t) :
    Nat.card (normalizer (P : Set G)) = 300 ∧
      ∃ W : SylowSplitWitness P, Function.Injective W.dihedralAction := by
  obtain ⟨e⟩ := hF.dihedral
  let W := splitWitnessOfAutomizer P (hB.self_centralizing P) e
  exact ⟨W.normalizer_card hG, W, W.dihedralAction_injective (hB.self_centralizing P)⟩

/-- The preceding source families construct a marked frame whose actual
conjugation orbits have size three and exhaust the six order-five subgroups. -/
theorem exists_frame_two_orbits {D : Seed G} (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) (hB : TwoCentralFiveFamily D S.t)
    (P : Sylow 5 G) : ∃ F : SourceFrame D S.t P, TwoOrbitConclusion F.frame := by
  obtain ⟨F⟩ := SourceFourGroup.exists_sourceFrame hG S hA hB P
  exact ⟨F, F.twoOrbitConclusion hG hB⟩

/-- The Sylow-five branch of 47.2: an actual internal D₁₂ complement and
exhaustive coverage by the root and two-central families. No frame, linear
recognition, splitting or coverage premise remains. -/
theorem family {D : Seed G} (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) (hB : TwoCentralFiveFamily D S.t) :
    SylowFiveFamily D S.t := by
  apply family_of_frames_and_linear_calculation hG hB
    (SourceFourGroup.exists_sourceFrame hG S hA hB)
  intro P hP hcard hmod F
  let : IsElementaryAbelian 5 P := hP
  exact F.twoOrbitConclusion hcard hmod

/-- Source specialization of the order and faithful action consequences of
the constructed complement in the literal normalizer. -/
theorem normalizer_data {D : Seed G} (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) (hB : TwoCentralFiveFamily D S.t)
    (P : Sylow 5 G) : Nat.card (normalizer (P : Set G)) = 300 ∧
      ∃ W : SylowSplitWitness P, Function.Injective W.dihedralAction := by
  obtain ⟨F, hF⟩ := exists_frame_two_orbits hG S hA hB P
  exact F.normalizer_data hF hG hB

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
