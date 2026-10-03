module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionThree.ResidualImageOddPGroup

/-!
# The local residual has odd image after killing the two-core

A surjective homomorphism from a genuine Section Nine vertex stabilizer
whose kernel contains its two-core sends the local two-residual into the
odd core of the target. No ambient identification or module action is
needed. The statement is shared by the canonical-factor constructions in
(9.4) and the support lift in (9.5).

The edge data of (7.3) supply the local hypotheses for the residual image
theorem from (3.3). That theorem makes the residual image an odd prime-power
subgroup. Its normality, preserved by surjectivity, places it in the odd
core. This is the existing residual-image argument used in (9.5), now
available at its natural shared interface.

Source: Stellmacher, (3.3) and the quotient actions in (9.4)–(9.5), printed
pp.22 and 50–53 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_local_residual_image_le_oddCore
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    {T A B : Subgroup G} (ctx : SectionNineLocalContext G T A B)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (action : GAt ctx.Γ vertex →* X)
    (hsurj : Function.Surjective action) (hkernel : pCore 2 (GAt ctx.Γ vertex) ≤ action.ker) :
    ((EAt ctx.Γ vertex).subgroupOf (GAt ctx.Γ vertex)).map action ≤
      SectionOne.oddCore X := by
  let P := stabilizer ctx.Γ vertex
  let sylow : Sylow 2 (P ⊓ stabilizer ctx.Γ neighbor : Subgroup G) := default
  let edgeSylow := sylowTwoAmbient (P ⊓ stabilizer ctx.Γ neighbor) sylow
  have hdata := edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) sylow
  obtain ⟨prime, hprime, hodd, himage⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    edgeSylow hdata.1 P hdata.2.1 hdata.2.2.2.1 action hkernel
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hnative : (EAt ctx.Γ vertex).subgroupOf P = twoResidualSubgroup P := by
    rw [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  rw [hnative]
  apply le_sSup
  refine ⟨?_, ?_⟩
  · have hnormal : (twoResidualSubgroup P).Normal := by
      rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
      exact BenderSuzuki.External.hktPResidual_normal
    exact hnormal.map action hsurj
  · obtain ⟨n, hn⟩ := himage.exists_card_eq
    rw [hn]
    exact (hodd.pow).coprime_two_left

end Stellmacher.SectionNine
