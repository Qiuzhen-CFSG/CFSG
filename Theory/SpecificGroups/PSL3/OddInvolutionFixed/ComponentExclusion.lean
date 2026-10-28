module

public import Theory.SpecificGroups.PSL3Two.CubeKernelObstruction
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner

/-!
# No binary PSL₃ perfect subgroup in an odd PSL₃ involution centralizer

Lift the projective involution to SL₃. Its full centralizer is GL₂, and its
projection surjects onto the actual projective centralizer with kernel of
exponent dividing three. The degree-two cubic-kernel obstruction excludes
any perfect PSL₃(2) subgroup. No rank hypothesis or exclusion of
characteristic three is needed.

Source: the odd linear-three branch in Aschbacher--Smith, proof of 15.3.38,
p.1137, and the centralizer calculation A.3.21(a), p.55.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.OddInvolutionFixed
variable {F K : Type*} [Field F] [Finite F] [Group K] [Group.IsPerfect K]
/-- An odd-characteristic projective involution centralizer contains no
perfect subgroup actually isomorphic to PSL₃(2). -/
theorem no_perfect_psl3_two_in_centralizer (h2 : (2 : F) ≠ 0)
    (t : PSL(3,F)) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set PSL(3,F))) (hj : Function.Injective j)
    (e : K ≃* PSL(3,ZMod 2)) : False := by
  obtain ⟨x, hx, rfl⟩ := PSL3.OddInvolutionFixed.involution_lift t ht
  let f := PSL3.OddInvolutionFixed.centralizerProjection x
  have hf : Function.Surjective f :=
    PSL3.OddInvolutionFixed.centralizerProjection_surjective x (hx ▸ pow_orderOf_eq_one x)
  have hker : ∀ g ∈ f.ker, g ^ 3 = 1 := by
    intro g hg
    have hz : (g : SL(3,F)) ∈ center SL(3,F) := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    have hd := (orderOf_dvd_natCard (⟨g.val,hz⟩ : center SL(3,F))).trans
      (SL3.card_center_dvd_three F)
    apply Subtype.ext
    exact congrArg (fun w : center SL(3,F) => (w : SL(3,F)))
      (orderOf_dvd_iff_pow_eq_one.mp hd)
  let c := SL3.involutionCentralizerEquiv F x hx h2
  exact PSL3Two.CubeKernel.no_perfect_psl3_two h2 f hf hker
    c.toMonoidHom c.injective j hj e
end Matrix.PSL3.OddInvolutionFixed
