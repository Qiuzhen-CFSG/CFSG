module
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ShortLeading
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.Reduction

/-!
# Moving triality Sylow involutions into the arms radical

The square-coordinate obstruction places a square-one element in one of the
two radicals. In the central radical, its rank-one action makes the first
layer (a,0); the square of the order-three actor then sends that layer to
(0,a). Vanishing of the first short coordinate puts the element in the arms
radical. The actual central-parabolic conjugator is retained for transport
through a marked inclusion amalgam.

Source: Aschbacher--Smith F.4.30--35, printed pp.289--292, and the genuine
triality root conventions of GLS3 Sections 2.4--2.6. The original source
application is EightLargeParabolic.FusionSylow in Chapter 14.
-/

public noncomputable section
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics Parabolics.CentralRootSquare

/-- A central-parabolic conjugation puts a square-one radical element in the
other radical, retaining the actual conjugator and its endpoint. -/
theorem central_square_conjugate_mem_arms (P : Parameters) (hp : P.prime=2)
    (u : radical P .central) (hu : u^2=1) :
    ∃ g : parabolic P .central, (conjugation P g u).val∈radical P .arms := by
  by_cases ha : (firstLayer P hp u).1=0
  · refine ⟨1,?_⟩
    simpa only [map_one, MulAut.one_apply] using mem_armsRadical_of_firstShort_eq_zero P hp u ha
  · obtain ⟨g,hg⟩ := ShortNormalization.exists_firstLayer_normalization P hp u ha hu
    let o := orderThreeActor P hp
    refine ⟨o*o*g,mem_armsRadical_of_firstShort_eq_zero P hp _ ?_⟩
    have hconj : conjugation P (o*o*g) u =
        conjugation P o (conjugation P o (conjugation P g u)) := by
      simp only [map_mul, MulAut.mul_apply]
    rw [hconj]
    change (firstLayer P hp (conjugation P (centralActor P hp (orderThreeMatrix P))
      (conjugation P (centralActor P hp (orderThreeMatrix P)) (conjugation P g u)))).1=0
    rw [firstLayer_centralActor, centralLinear_orderThree P hp, firstLayer_centralActor,
      centralLinear_orderThree P hp,hg]
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
    simp only [add_zero, CharTwo.add_self_eq_zero]

/-- Every square-one element of the genuine unipotent subgroup is moved into
the arms radical by an element of the central parabolic. -/
theorem unipotent_square_conjugate_mem_arms (n : ℕ) (hn : 0<n)
    (u : unipotent (binaryParameters n hn)) (hu : u^2=1) :
    ∃ g : parabolic (binaryParameters n hn) .central,
      g.val*u.val*g.val⁻¹∈radical (binaryParameters n hn) .arms := by
  obtain ha|hc := TwoRank.unipotent_mem_radical_or_radical_of_square_eq_one n hn u hu
  · exact ⟨1,by simpa using ha⟩
  · let v : radical (binaryParameters n hn) .central := ⟨u.val,hc⟩
    have hv : v^2=1 := by
      apply Subtype.ext
      exact congrArg (fun x : unipotent (binaryParameters n hn) => x.val) hu
    obtain ⟨g,hg⟩ := central_square_conjugate_mem_arms (binaryParameters n hn) rfl v hv
    exact ⟨g,by simpa only [conjugation_val] using hg⟩
end Triality.Standard.EvenInvolutionGeometry
