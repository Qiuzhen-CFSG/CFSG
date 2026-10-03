module
public import Stellmacher.SectionEight.EightSixCostFourModuleLNormal
public import Stellmacher.SectionEight.EightSixCostFourNativeA4Witness
public import Theory.GroupAction.FixedFreeA4PlaneNormalizer
/-!
# The cost-four normalizer witness

For the original selected cost-four configuration, the canonical subgroup
`W = [closure_E Za, Ea]` is elementary abelian of order 16, normal in the
literal subgroup L, and has a nonsolvable full ambient normalizer.

The native A4 witness supplies two actual automorphisms of W: the initial
fixed-free cubic and an involution from the initial residual core. Their
conjugate relations identify the A4 action; the selected E moves the fixed
plane Za. The finite A4 plane-movement obstruction makes the image of the
full ambient normalizer nonsolvable. Surjectivity of that normalizer action
then gives the required ambient conclusion, while the separate L-normality
producer retains exactly the same canonical W.

This proves the normalizer clause in Stellmacher (8.6)(b3), printed p.44,
using the checked native action rather than the unsupported S4 image
identification in the source argument.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_normalizer_witness
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    ∃ W : Subgroup G, W ≤ L ∧ (W.subgroupOf L).Normal ∧
      IsElementaryAbelianSubgroup 2 W ∧ Nat.card W = 2^4 ∧ IsNonsolvableNormalizer W := by
  classical
  let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
  let W := ⁅U,EAt ctx.Γ ctx.criticalPath.a⁆
  let C := (ZAt ctx.Γ ctx.criticalPath.a).subgroupOf W
  let X := W.normalizerMonoidHom.range
  obtain ⟨helem,hWcard,hCcard,r,t,hr,ht,hrne,hr2,ht3,hff,hcomm,hnorm,hrC,hmove⟩ :=
    eight_six_cost_four_native_a4_witness ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  let _ : IsElementaryAbelian 2 W := helem
  have hnotX : ¬ Group.IsSolvable X :=
    MulAut.not_isSolvable_of_fixed_free_a4_and_plane_move hWcard X r t
      hr ht hrne hr2 ht3 hff hcomm hnorm C hCcard hrC hmove
  have hnot : IsNonsolvableNormalizer W := by
    intro hsolvable
    let _ := hsolvable
    exact hnotX (Group.isSolvable_of_surjective W.normalizerMonoidHom.rangeRestrict_surjective)
  have hWL := eight_six_cost_four_module_l_normal ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  exact ⟨W,hWL.1,hWL.2,helem,by simpa only [show (2:ℕ)^4=16 from by decide] using hWcard,hnot⟩
end Stellmacher.SectionEight
