module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.LinearCalculation.OrbitCounting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.LinearCalculation.PlaneGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.LinearCalculation.DihedralRecognition

/-!
# Assembly of the finite five-plane calculation

An elementary four-group fixing two nonfused lines in an elementary abelian
group of order 25, inside an actor of order congruent to two modulo five,
forces that actor to be D₁₂ with two three-element orbits on the six lines.
The fixed-point congruence and line-stabilizer bound exclude order 32;
the faithful matrix representation recognizes the remaining order-twelve
actor. Orbit--stabilizer and nonfusion give the two orbits and their coverage.

The result is the linear input consumed by
`SylowAction.family_of_frames_and_linear_calculation`, for the final
paragraph of Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261.
All plane-geometry and recognition premises are discharged here. The source
specialization applies the result to the literal conjugation automizer of
the Sylow subgroup; constructing its source frame remains a separate input.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
variable {E : Type*} [Group E] {H : Subgroup (MulAut E)}

/-- Conditional assembly isolates the plane geometry and order-twelve recognition.
The order-32 exclusion and both actual orbit calculations are discharged here. -/
theorem FourLineFrame.twoOrbitConclusion_of_plane_geometry_and_recognition [Finite E]
    [IsElementaryAbelian 5 E] (F : FourLineFrame H)
    (hE : Nat.card E = 25) (hm : Nat.card H ≡ 2 [MOD 5])
    (h6 : Nat.card {L : Subgroup E // Nat.card L = 5} = 6)
    (hstab : ∀ L : Subgroup E, Nat.card L = 5 → Nat.card (MulAction.stabilizer H L) ∣ 80)
    (hrecognize : Nat.card H = 12 → Nonempty (H ≃* DihedralGroup 6)) :
    TwoOrbitConclusion F := by
  have hH := F.card_eq_twelve_of_stabilizer_dvd hE hm (hstab F.A F.A_card)
  obtain ⟨hA, hB⟩ := F.orbit_cards_of_card_twelve hH (hstab F.A F.A_card) (hstab F.B F.B_card)
  exact ⟨hrecognize hH, h6, hA, hB, F.coverage_of_orbit_cards h6 hA hB⟩

/-- The finite linear calculation: the actual actor is D₁₂, and its two
marked three-element orbits exhaust the six order-five subgroups. -/
theorem FourLineFrame.twoOrbitConclusion [Finite E] [IsElementaryAbelian 5 E]
    (F : FourLineFrame H) (hE : Nat.card E = 25) (hm : Nat.card H ≡ 2 [MOD 5]) :
    TwoOrbitConclusion F := by
  obtain ⟨h6, hstab⟩ := plane_geometry hE H
  exact F.twoOrbitConclusion_of_plane_geometry_and_recognition hE hm h6 hstab
    (F.dihedral_of_card_twelve hE)

/-- Application to the actual Sylow-five conjugation image. This discharges
the linear calculation used by `family_of_frames_and_linear_calculation`
for any supplied source frame. -/
theorem SourceFrame.twoOrbitConclusion {G : Type*} [Group G] [Finite G]
    {D : Seed G} {t : G} {P : Sylow 5 G} (F : SourceFrame D t P)
    (hG : Nat.card G = 604800) (hB : TwoCentralFiveFamily D t) :
    TwoOrbitConclusion F.frame := by
  let : IsElementaryAbelian 5 P := hB.elementary P
  exact F.frame.twoOrbitConclusion (sylow_card hG P)
    (automizer_card_mod hG P (hB.self_centralizing P))

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
