module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionThree.PSetResidualKernel
public import Theory.GroupTheory.CommutatorPreimage

/-!
# A trivial outside-core two-actor kills the residual quotient action

Suppose the first stabilizer normalizes K and C≤K. If a supplied two-actor
outside the first core centralizes K modulo C, then the whole first
residual centralizes K modulo C. K need not lie in the first stabilizer,
and normality of C inside K is unnecessary.

Use the intrinsic subgroup of the first stabilizer whose commutators with
K lie in C. Simultaneous normalization of K and C makes this subgroup
normal. It contains the supplied actor's cyclic two-group. The actual PSet
normal-kernel criterion therefore forces the entire first residual into
it, since otherwise that cyclic group would lie in the first core.

This is the quotient-kernel implication in the excluded-terminal-center
branch at the end of Stellmacher (9.10), printed p.59. The supplied actor
is retained, and no replacement quotient action or critical path is used.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_actor_trivial_quotient_residual_commutator_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (K C : Subgroup G) (_hCK : C≤K)
    (hPK : GAt ctx.Γ ctx.criticalPath.firstStep≤Subgroup.normalizer (K:Set G))
    (hPC : GAt ctx.Γ ctx.criticalPath.firstStep≤Subgroup.normalizer (C:Set G))
    (actor : GAt ctx.Γ ctx.criticalPath.firstStep)
    (hout : (actor:G)∉QAt ctx.Γ ctx.criticalPath.firstStep)
    (hactorTwo : IsPGroup 2 (Subgroup.zpowers (actor:G)))
    (hcomm : ⁅K,Subgroup.zpowers (actor:G)⁆≤C) :
    ⁅K,EAt ctx.Γ ctx.criticalPath.firstStep⁆≤C := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let N := Subgroup.commutatorPreimage P K C
  let U := Subgroup.zpowers (actor:G)
  have hNP : N≤P := Subgroup.commutatorPreimage_le P K C
  have hPN : P≤Subgroup.normalizer (N:Set G) :=
    Subgroup.commutatorPreimage_normalized P K C P hPC P.le_normalizer hPK hPC
  have hNN : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have hUN : U≤N := Subgroup.le_commutatorPreimage
    (Subgroup.zpowers_le.mpr actor.property) (by rwa [Subgroup.commutator_comm])
  have hNC : ⁅N,K⁆≤C := Subgroup.commutator_commutatorPreimage_le P K C hPC
  have hE : E=twoResidualAmbient P := Γ.twoResidualAt_def cp.firstStep
  by_contra hnot
  have hRnot : ¬twoResidualAmbient P≤N := by
    intro hle
    apply hnot
    rw [Subgroup.commutator_comm]
    have hEN : E≤N := by rwa [hE]
    exact (Subgroup.commutator_mono hEN le_rfl).trans hNC
  let edge := P⊓GAt Γ cp.a
  let sylow : Sylow 2 edge := default
  let Sedge := sylowTwoAmbient edge sylow
  have hlocal := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) sylow
  have hcore := SectionThree.pSet_two_subgroup_normal_kernel_le_core
    Sedge hlocal.1 P N U hlocal.2.1 hlocal.2.2.2.1 hNP hNN hRnot hUN hactorTwo
  apply hout
  change (actor:G)∈Γ.twoCoreAt cp.firstStep
  rw [Γ.twoCoreAt_def]
  exact hcore (Subgroup.mem_zpowers (actor:G))

end Stellmacher.SectionNine
