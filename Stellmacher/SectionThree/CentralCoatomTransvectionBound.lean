module
public import Stellmacher.SectionThree.CentralCoatomInvolutionCard
public import Theory.GroupAction.CardTwoDisplacementInvolution

/-!
# A transvection module with a central actor coatom

For the actual action, two-conjugate generation and central two-subgroup
coatom hypotheses, trivial residual fixed points and cyclic displacement
order two force module order at most four. The statement preserves the
original finite-action interface used in Stellmacher (8.6)(13), printed
p.43 of `refs/files/stellmacher-n-group.pdf`.

An automorphism of an elementary two-group with displacement order two
is an involution. The exact central-coatom involution module count therefore
gives module order 2². This wrapper retains the original bound and all its
hypotheses without imposing faithfulness or trivial actor two-core.
-/

namespace Stellmacher.SectionThree

public theorem central_coatom_transvection_module_card_le_four
    {K V : Type*} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V]
    (action : K →* MulAut V) (A A0 : Subgroup K) (a x : K)
    (hgen : (⊤ : Subgroup K) = A ⊔ A.conjBy x)
    (hA : A = Subgroup.zpowers a ⊔ A0)
    (htwo : IsPGroup 2 A0)
    (hcentral : A0.map action ≤ Subgroup.centralizer (action.range : Set (MulAut V)))
    (hfixed : FixedPoints.subgroup ((twoResidualAmbient (⊤ : Subgroup K)).map action) V = ⊥)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers (action a)) V) = 2) :
    Nat.card V ≤ 4 := by
  have hcard := central_coatom_involution_module_card_eq_square
    action A A0 a x hgen hA htwo hcentral hfixed
    (isInvolution_of_card_two_displacement (action a) hrank).2
  norm_num only [hrank] at hcard
  omega

end Stellmacher.SectionThree
