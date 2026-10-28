module
public import Stellmacher.SectionNine.DistanceOneChiefPreimage
public import Stellmacher.SectionNine.DistanceOneChiefOrder
public import Theory.GroupTheory.CentralActionKernelCore

/-!
# The ordinary quotient in the noncentral chief branch

In the distance-one noncentral branch, the canonical chief action has
kernel exactly Q_a. Its kernel is already known to coincide with the
initial-center action kernel K. The chief preimage equality C=Z_a makes
K act trivially on both Z_a and Q_a/Z_a.

Inside the initial stabilizer, the (7.4) Sylow intersection gives K∩T=Q_a.
The generic central-action-kernel lemma then kills an odd complement to
Q_a in K: it fixes the two central layers, so it centralizes Q_a, and
characteristic two type places it inside Q_a. This proves K=Q_a.

The original faithful-center quotient now gives the ordinary wreath
quotient. Multiplying the orders of the chief quotient and its preimage
also gives |Q_a|=256. These are the ordinary quotient and core-size inputs
to the D* argument after Stellmacher (9.1)(10), Journal of Algebra190
(1997), p.48. The noncentral branch is retained throughout.
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_ordinary_action_kernel
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    (distanceOneChiefAction ctx.toLocalContext).ker =
      (q ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Q := q Γ cp.a
  let Z := z Γ cp.a
  let K := P ⊓ Subgroup.centralizer (Z : Set G)
  let q0 := Q.subgroupOf P
  let z0 := Z.subgroupOf P
  let k0 := K.subgroupOf P
  have hprops := distance_one_chief_subgroup_properties ctx.toLocalContext
  have hQP : Q ≤ P := by
    change q Γ cp.a ≤ stabilizer Γ cp.a
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZQ : Z ≤ Q := hprops.2.1.trans hprops.1
  have hZP : Z ≤ P := hZQ.trans hQP
  have hq0 : q0 = pCore 2 P := by
    change (q Γ cp.a).subgroupOf P = _
    rw [q, Γ.twoCoreAt_def]
    change ((pCore 2 P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  let _ : q0.Normal := by rw [hq0]; infer_instance
  have hdata := distance_one_initial_centralizer_kernel_data ctx hb branch.U
    branch.le_terminal_core (by
      simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using branch.terminal_residual_commutator)
  let _ : k0.Normal := hdata.2.1
  have hker : (distanceOneChiefAction ctx.toLocalContext).ker = k0 := by
    rw [distance_one_chief_action_kernel ctx hb hfaith branch]
    change (Subgroup.centralizer (Z : Set G)).subgroupOf P = k0
    simp only [k0, K, Subgroup.inf_subgroupOf_left]
  have hQK : q0 ≤ k0 := hker ▸ distance_one_chief_core_le_action_kernel ctx hb hfaith branch
  obtain ⟨hTP, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
  have hS : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hsylow, Subgroup.map_subgroupOf_eq_of_le hTP]
  have hKS : k0 ⊓ (sylow : Subgroup P) = q0 := by
    rw [hS]
    change (K ⊓ T).subgroupOf P = Q.subgroupOf P
    rw [hdata.2.2.1]
  have hZcentral : z0 ≤ Subgroup.centralizer (q0 : Set P) := by
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro coreElement hcoreElement
    apply Subtype.ext
    have hZomega := (lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
    have hh := (centerAmbient_le_centralizer Q) (omegaOneCenter_le_centerAmbient Q (hZomega helement))
    exact Subgroup.mem_centralizer_iff.mp hh coreElement hcoreElement
  have hKZ : k0 ≤ Subgroup.centralizer (z0 : Set P) := by
    intro actor hactor
    rw [Subgroup.mem_centralizer_iff]
    intro point hpoint
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hactor.2 point hpoint
  have hQKcomm : ⁅q0,k0⁆ ≤ z0 := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQP,
      Subgroup.map_subgroupOf_eq_of_le (show K ≤ P from inf_le_left),
      Subgroup.map_subgroupOf_eq_of_le hZP]
    change ⁅Q,K⁆ ≤ z ctx.Γ ctx.criticalPath.a
    rw [← distance_one_chief_preimage_eq_center ctx hb hfaith branch]
    exact (distance_one_chief_actor_le_kernel_iff ctx.toLocalContext K inf_le_left).mp
      (by rw [hker]; exact le_rfl)
  have hself : Subgroup.centralizer (q0 : Set P) ≤ q0 := by
    rw [hq0]
    exact (edge_characteristic_data ctx.sectionSeven Γ cp).1
  rw [hker]
  exact Subgroup.eq_of_sylow_intersection_of_central_action_layers sylow q0 k0 z0
    (hq0 ▸ pCore_isPGroup) hQK hKS (Subgroup.subgroupOf_mono P hZQ)
    hZcentral hKZ hQKcomm hself
public theorem distance_one_chief_ordinary_quotient_wreath
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2TwoWreathC2 := by
  change QuotientIsModel (stabilizer ctx.Γ ctx.criticalPath.a)
    (q ctx.Γ ctx.criticalPath.a) SL2TwoWreathC2
  obtain ⟨f, hf, hk⟩ := hfaith.2
  change (stabilizer ctx.Γ ctx.criticalPath.a) →* SL2TwoWreathC2 at f
  change Function.Surjective f at hf
  change f.ker = ((stabilizer ctx.Γ ctx.criticalPath.a) ⊓
    Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a) at hk
  refine ⟨f,hf,?_⟩
  rw [hk]
  rw [Subgroup.inf_subgroupOf_left,
    ← distance_one_chief_action_kernel ctx hb hfaith branch,
    distance_one_chief_ordinary_action_kernel ctx hb hfaith branch]

public theorem distance_one_chief_core_card
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    Nat.card (q ctx.Γ ctx.criticalPath.a) = 256 := by
  let Q := q ctx.Γ ctx.criticalPath.a
  let C := distanceOneChiefSubgroup ctx.toLocalContext
  let c := C.subgroupOf Q
  have hCQ : C ≤ Q := (distance_one_chief_subgroup_properties ctx.toLocalContext).1
  have hccard : Nat.card c = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCQ).toEquiv]
    change Nat.card (distanceOneChiefSubgroup ctx.toLocalContext) = 16
    rw [distance_one_chief_preimage_eq_center ctx hb hfaith branch]
    exact hfaith.1
  have hcindex : c.index = 16 := by
    rw [Subgroup.index_eq_card]
    exact distance_one_chief_quotient_card_sixteen ctx hb hfaith branch
  have hh := c.index_mul_card
  rw [hcindex,hccard] at hh
  exact hh.symm
end Stellmacher.SectionNine
