module
public import Stellmacher.SectionNine.DistanceOneChiefLiteralAction
public import Theory.GroupTheory.CenterFreeChiefLayer

/-!
# The actual chief preimage is an abelian central layer

In the noncentral chief branch at critical distance one, the canonical
preimage C in Q_a is abelian and [C,Q_a]≤Z_a. Both conclusions use the
actual ambient-retaining context and do not assume C=Z_a or Q_a=Z_a.

The full canonical chief action identifies the image of [Q_a,E_a] in
Q_a/C with the whole quotient, giving Q_a=[Q_a,E_a]C. Restrict the
subgroups to the initial stabilizer. Its center is trivial by (7.5),
its residual supplements the edge Sylow, C is normal with [C,E_a]=Z_a,
and (7.3) makes Z_a central in Q_a. The generic center-free chief-layer
commutator theorem gives both conclusions, which are mapped back to G.

These are the commutator reductions used for the nonisomorphic-module
argument in Stellmacher (9.1), Journal of Algebra190 (1997), p.48.
The comparison of modules and final preimage collapse remain separate.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_central_layer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    IsMulCommutative (distanceOneChiefSubgroup ctx.toLocalContext) ∧
      ⁅distanceOneChiefSubgroup ctx.toLocalContext, q ctx.Γ ctx.criticalPath.a⁆ ≤
        z ctx.Γ ctx.criticalPath.a := by
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
  have hQN := stabilizer_le_normalizer_q Γ cp.a
  let _ : (C.subgroupOf Q).Normal := distanceOneChiefSubgroup_normal_in_core ctx.toLocalContext
  have hfull := distance_one_chief_residual_map_action_full ctx hb hfaith branch
  have himage := Subgroup.quotient_conjugation_commutatorAction_eq_image P Q C E
    hQN hEP inferInstance (distanceOneChiefAction ctx.toLocalContext)
    (distance_one_chief_action_apply ctx.toLocalContext)
  have himageTop : (⁅Q,E⁆.subgroupOf Q).map (QuotientGroup.mk' (C.subgroupOf Q)) = ⊤ := by
    rw [← himage]
    exact hfull
  have hQE : ⁅Q,E⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hQN)
  have hQgen : ⁅Q,E⁆ ⊔ C = Q := by
    apply le_antisymm (sup_le hQE hprops.1)
    intro point hpoint
    have hmem : QuotientGroup.mk' (C.subgroupOf Q) (⟨point,hpoint⟩ : Q) ∈
        (⁅Q,E⁆.subgroupOf Q).map (QuotientGroup.mk' (C.subgroupOf Q)) := by rw [himageTop]; trivial
    obtain ⟨representative, hrepresentative, heq⟩ := hmem
    have hdifference := QuotientGroup.eq_iff_div_mem.mp heq.symm
    have hC : point * (representative : G)⁻¹ ∈ C := by
      change point / (representative : G) ∈ C at hdifference
      simpa only [div_eq_mul_inv] using hdifference
    have hproduct := (⁅Q,E⁆ ⊔ C).mul_mem ((show C ≤ ⁅Q,E⁆ ⊔ C from le_sup_right) hC)
      ((show ⁅Q,E⁆ ≤ ⁅Q,E⁆ ⊔ C from le_sup_left) hrepresentative)
    change point * (representative : G)⁻¹ * (representative : G) ∈ ⁅Q,E⁆ ⊔ C at hproduct
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hproduct
  let c := C.subgroupOf P
  let z := Z.subgroupOf P
  let q0 := Q.subgroupOf P
  let e0 := E.subgroupOf P
  let _ : c.Normal := hprops.2.2.1
  let _ : z.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (stabilizer_le_normalizer_z Γ cp.a)
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
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (q Γ cp.a)
    rw [q, Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hCp : IsPGroup 2 c := (hQp.to_le hprops.1).comap_subtype
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
  have hCE : ⁅c,e0⁆ ≤ z := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hcmap, hemap, hzmap]
    exact hprops.2.2.2.1.le
  have hgen : ⁅q0,e0⁆ ⊔ c = q0 := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_commutator, hcmap, hemap, hqmap, hQgen]
  obtain ⟨hccomm,hcQ⟩ := Subgroup.centerfree_chief_layer_commutators sylow e0 q0 c z
    hcover hCp (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).start_center_trivial
    (Subgroup.subgroupOf_mono P hprops.1) hZcentral hCE hgen
  let _ := hccomm
  have hCab : IsMulCommutative C := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    let a0 : c := ⟨⟨a, hCP a.property⟩, a.property⟩
    let b0 : c := ⟨⟨b, hCP b.property⟩, b.property⟩
    exact congrArg (fun x : c => ((x : P) : G)) (hccomm.is_comm.comm a0 b0)
  refine ⟨hCab, ?_⟩
  have hh := Subgroup.map_mono (f := P.subtype) hcQ
  rwa [Subgroup.map_commutator, hcmap, hqmap, hzmap] at hh
end Stellmacher.SectionNine
