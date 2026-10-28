module
public import Stellmacher.SectionNine.DistanceOneChiefCentralLayer
public import Stellmacher.SectionNine.DistanceOneChiefNoHom
public import Theory.GroupTheory.CenterFreeChiefHomCollapse

/-!
# The chief preimage is the initial vertex center

In the noncentral branch of the distance-one configuration, the canonical
chief preimage C equals the initial vertex center Z_a. The already proved
central-layer theorem makes C abelian and gives [C,Q_a] ≤ Z_a. Its defining
residual commutator also lies in Z_a.

Restricting these subgroups to the initial stabilizer allows the generic
center-free chief-hom collapse theorem to apply. The residual supplements
the edge Sylow, its image modulo the two-core is odd by (3.3), and (7.5)
gives a trivial stabilizer center. The actual chief-module no-hom theorem
supplies precisely the normal-conjugation equivariance obstruction. Mapping
back to the graph group gives the asserted equality.

This formalizes the nonisomorphic-module step after Stellmacher (9.1)(10),
Journal of Algebra190 (1997), p.48. The genuine noncentral branch remains
an explicit hypothesis; no initial-core equality is assumed.
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_preimage_eq_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    distanceOneChiefSubgroup ctx.toLocalContext = z ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Q := q Γ cp.a
  let C := distanceOneChiefSubgroup ctx.toLocalContext
  let Z := z Γ cp.a
  let E := e Γ cp.a
  have hprops := distance_one_chief_subgroup_properties ctx.toLocalContext
  have hQP : Q ≤ P := by
    change q Γ cp.a ≤ stabilizer Γ cp.a
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hCP : C ≤ P := hprops.1.trans hQP
  have hZP : Z ≤ P := hprops.2.1.trans hCP
  have hEP : E ≤ P := by
    change e Γ cp.a ≤ stabilizer Γ cp.a
    rw [CosetGraphContext.e, Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  let c := C.subgroupOf P
  let z := Z.subgroupOf P
  let q0 := Q.subgroupOf P
  let e0 := E.subgroupOf P
  let _ : c.Normal := hprops.2.2.1
  let _ : z.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (stabilizer_le_normalizer_z Γ cp.a)
  let _ : q0.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (stabilizer_le_normalizer_q Γ cp.a)
  have hq0 : q0 = pCore 2 P := by
    change (q Γ cp.a).subgroupOf P = _
    rw [q, Γ.twoCoreAt_def]
    change ((pCore 2 P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  have he0 : e0 = twoResidualSubgroup P := by
    change (e Γ cp.a).subgroupOf P = _
    rw [CosetGraphContext.e, Γ.twoResidualAt_def]
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  let _ : e0.Normal := by
    rw [he0, SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨_, sylow, _⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
  have hcover : e0 ⊔ (sylow : Subgroup P) = ⊤ := by
    have hh := twoResidualAmbient_top_sup_sylow sylow
    rw [he0, SectionThree.twoResidualSubgroup_eq_hktPResidual']
    simpa only [SectionThree.twoResidualAmbient_top_eq_hktPResidual] using hh
  have hQp : IsPGroup 2 q0 := hq0 ▸ pCore_isPGroup
  have hlocal := (edge_local_data ctx.sectionSeven Γ cp).1
  obtain ⟨prime, hprime, hprimeOdd, hp⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    T (sectionThreeHypotheses ctx.sectionSeven) P ((pFamily_iff_pSet _ _ _).mp hlocal.1)
    hlocal.2 (QuotientGroup.mk' q0) (by rw [QuotientGroup.ker_mk', hq0])
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hodd : Odd (Nat.card (e0.map (QuotientGroup.mk' q0))) := by
    rw [he0]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact hprimeOdd.pow
  have hZcentral : z ≤ Subgroup.centralizer (q0 : Set P) := by
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro coreElement hcoreElement
    apply Subtype.ext
    have hZomega := (lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
    have hh := (centerAmbient_le_centralizer Q) (omegaOneCenter_le_centerAmbient Q (hZomega helement))
    exact Subgroup.mem_centralizer_iff.mp hh coreElement hcoreElement
  have hcmap : c.map P.subtype = C := Subgroup.map_subgroupOf_eq_of_le hCP
  have hzmap : z.map P.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZP
  have hqmap : q0.map P.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQP
  have hemap : e0.map P.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEP
  obtain ⟨hCab, hCQ⟩ := distance_one_chief_central_layer ctx hb hfaith branch
  let _ := hCab
  let _ : IsMulCommutative c := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (setLike_mul_comm (s := C) a.property b.property))⟩⟩
  have hCE : ⁅c,e0⁆ ≤ z := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hcmap, hemap, hzmap]
    exact hprops.2.2.2.1.le
  have hCQnative : ⁅c,q0⁆ ≤ z := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hcmap, hqmap, hzmap]
    exact hCQ
  have hcz := Subgroup.eq_of_centerfree_odd_residual_no_equivariant_hom sylow e0 q0 c z
    hcover hQp hodd (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).start_center_trivial
    (Subgroup.subgroupOf_mono P hprops.2.1) (Subgroup.subgroupOf_mono P hprops.1)
    hZcentral hCQnative hCE
    (fun f hkernel hequiv => distance_one_chief_normal_equivariant_hom_eq_one
      ctx hb hfaith branch f hkernel hequiv)
  have hh := congrArg (Subgroup.map P.subtype) hcz
  rwa [hcmap, hzmap] at hh
end Stellmacher.SectionNine
