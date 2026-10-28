module
public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Theory.GroupTheory.QuaternionCentralProductCenter

/-!
# The terminal center in the distance-one configuration

The commuting endpoint centers imply that the terminal center centralizes
the conjugate closure of the initial center intersected with the terminal
two-core. Conjugating a terminal-center element backwards preserves that
center by stabilizer invariance, so the original commuting relation applies
to every generator of the closure. This step does not require length one.

At length one the terminal center is nontrivial: it contains the omega-center
of the nontrivial distinguished edge Sylow subgroup. Its nontriviality follows
from the nontrivial center of a finite two-group and Cauchy's theorem.
The explicit local conclusion supplies two actual commuting quaternion factors
with intersection of order two. The generic quaternion central-product theorem
therefore gives the closure's center order two. The additional containment of
the terminal center in that closure embeds it in this center; nontriviality
then proves its order is exactly two. The faithful conclusion is retained as
an explicit interface input, although this final reduction does not use it.
This is the order-two terminal-center calculation used in the ambient
centralizer argument of Stellmacher (9.1),
Journal of Algebra 190 (1997), p.48 / PDF p.38 of
`refs/files/stellmacher-n-group.pdf`. The graph reductions do not assume a
classification conclusion; the final theorem takes those conclusions and the
containment explicitly, without enlarging the shared graph context.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven
universe u

public theorem distance_one_terminal_center_centralizes_closure
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ≤
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a' : Set G) := by
  have hcomm := Subgroup.commutator_eq_bot_iff_le_centralizer.mp ctx.commutator_eq
  have hnorm := stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a'
  rw [conjugateClosure, Subgroup.closure_le]
  rintro element ⟨actor, generator, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro center hcenter
  have hconj : (actor : G)⁻¹ * center * (actor : G) ∈
      ZAt ctx.Γ ctx.criticalPath.a' := by
    simpa using Subgroup.le_normalizer_iff.mp hnorm
      (actor : G)⁻¹ ((GAt ctx.Γ ctx.criticalPath.a').inv_mem actor.property)
      center hcenter
  have heq := Subgroup.mem_centralizer_iff.mp (hcomm generator.property.1) _ hconj
  have heq' := congrArg (fun element : G => (actor : G) * element * (actor : G)⁻¹) heq
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel, mul_one] using heq'

public theorem distance_one_terminal_center_ne_bot
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1) :
    ZAt ctx.Γ ctx.criticalPath.a' ≠ ⊥ := by
  have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hlength
  have hsyl : IsSylowTwoIn T (GAt ctx.Γ ctx.criticalPath.firstStep) := by
    change IsSylowTwoIn T (ctx.Γ.stabilizer ctx.criticalPath.firstStep)
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.2]
      exact ctx.sectionSeven.P2_mem.1.2.1
    · rw [hedge.2]
      exact ctx.sectionSeven.P1_mem.1.2.1
  have hp : IsPGroup 2 T := by
    obtain ⟨_, sylow, heq⟩ := hsyl
    rw [← heq]
    exact sylow.isPGroup'.map _
  let _ : Nontrivial T :=
    (Subgroup.nontrivial_iff_ne_bot T).2 ctx.sectionSeven.S_nontrivial
  let _ : Nontrivial (Subgroup.center T) := hp.center_nontrivial
  obtain ⟨power, hpos, hcard⟩ :=
    (hp.to_subgroup (Subgroup.center T)).nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center T) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
  have hinner := omega₁_map_subtype_ne_bot (G := T) (Subgroup.center T) 2 hdvd
  have hne : omegaOneCenter T ≠ ⊥ := by
    intro hbot
    apply hinner
    apply Subgroup.map_injective (f := T.subtype) T.subtype_injective
    simpa [omegaOneCenter] using hbot
  have hle : omegaOneCenter T ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
    rw [hend]
    obtain ⟨_, sylow, heq⟩ := hsyl
    change omegaOneCenter T ≤ ctx.Γ.zAt _
    rw [ctx.Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter heq.symm⟩
  intro hbot
  exact hne (le_bot_iff.mp (hle.trans_eq hbot))

public theorem distance_one_terminal_center_card
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (_hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2 := by
  let closure := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  have hcenter : Nat.card (Subgroup.center closure) = 2 := by
    obtain ⟨left, right, hleft, hright, hjoin, hinter, hcomm, _⟩ := hlocal.2.2.2.2
    change closure = left ⊔ right at hjoin
    rw [hjoin]
    exact Subgroup.quaternion_central_product_center_card left right
      hleft hright hinter hcomm
  have hle : ZAt ctx.Γ ctx.criticalPath.a' ≤
      (Subgroup.center closure).map closure.subtype := by
    intro element helement
    refine ⟨⟨element, hcontain helement⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact (distance_one_terminal_center_centralizes_closure ctx.toLocalContext
      other.property element helement).symm
  have hupper := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective closure.subtype_injective] at hupper
  have hlower := (Subgroup.one_lt_card_iff_ne_bot _).mpr
    (distance_one_terminal_center_ne_bot ctx.toLocalContext hlength)
  change 1 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a') at hlower
  omega

end Stellmacher.SectionNine
