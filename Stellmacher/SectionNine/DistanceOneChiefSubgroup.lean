module

public import Stellmacher.SectionNine.DistanceOneChiefBranchReduction
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.CenterFreeCentralSubgroup
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The actual greatest initial chief subgroup

The initial vertex center is its full commutator with the initial residual.
The commutator preimage therefore constructs the greatest subgroup of the
initial core having precisely that commutator. It contains the vertex
center and is normal in the initial stabilizer. No chief index or core
equality is assumed here.

Source: Stellmacher (9.1), printed p.47, the subgroup in relation (10).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_initial_center_full_residual
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ⁅z ctx.Γ ctx.criticalPath.a, e ctx.Γ ctx.criticalPath.a⁆ =
      z ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Z := z Γ cp.a
  let Q := pCore 2 P
  let E := twoResidualAmbient (⊤ : Subgroup P)
  have hneighbor : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hZomega : Z ≤ omegaOneCenter (q Γ cp.a) :=
    (lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hneighbor
  have hZQ : Z ≤ q Γ cp.a := hZomega.trans (Subgroup.map_subtype_le _)
  have hQmap : Q.map P.subtype = q Γ cp.a := by
    change twoCoreIn P = q Γ cp.a
    exact (Γ.twoCoreAt_def cp.a).symm
  have hQP : q Γ cp.a ≤ P := by
    rw [← hQmap]
    exact Subgroup.map_subtype_le _
  have hZP : Z ≤ P := hZQ.trans hQP
  let M := Z.subgroupOf P
  have hMmap : M.map P.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZP
  let _ : M.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (stabilizer_le_normalizer_z Γ cp.a)
  have hEmap : E.map P.subtype = e Γ cp.a := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) P.subtype P
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    exact hm.trans (Γ.twoResidualAt_def cp.a).symm
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨hTP, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
  have hcover : E ⊔ (sylow : Subgroup P) = ⊤ := twoResidualAmbient_top_sup_sylow sylow
  have hPset := (pFamily_iff_pSet _ _ _).mp (edge_local_data ctx.sectionSeven Γ cp).1.1
  have hsolv := (edge_local_data ctx.sectionSeven Γ cp).1.2
  obtain ⟨maximal, hmaximal, hTmaximal, hunique⟩ := hPset.2
  have hnative : IsCoatom maximal ∧ T.subgroupOf P ≤ maximal ∧
      ∀ other : Subgroup P, IsCoatom other → T.subgroupOf P ≤ other → other = maximal := by
    refine ⟨hmaximal, ?_, ?_⟩
    · intro element helement
      obtain ⟨preimage, hpreimage, heq⟩ := hTmaximal helement
      exact P.subtype_injective heq ▸ hpreimage
    · intro other hother hTother
      apply hunique other hother
      intro element helement
      exact ⟨⟨element, hTP helement⟩, hTother helement, rfl⟩
  obtain ⟨prime, hprime, hoddprime, hresidual⟩ :=
    (SectionThree.lemma_three_three T (sectionThreeHypotheses ctx.sectionSeven) P hPset
      maximal maximal.normalCore hnative
      ⟨maximal.normalCore_le, inferInstance, fun normal hnormal hle => by
        let _ := hnormal
        exact Subgroup.normal_le_normalCore.mpr hle⟩ hsolv).part_a
  have hodd : Odd (Nat.card (E.map (QuotientGroup.mk' Q))) := by
    rw [map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P)
      (QuotientGroup.mk' Q) ⊤
      (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q))]
    let _ : Fact prime.Prime := ⟨hprime⟩
    obtain ⟨exponent, hcard⟩ := hresidual.exists_card_eq
    rw [hcard]
    exact hoddprime.pow
  have hMQ : M ≤ Q := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rwa [hMmap, hQmap]
  have hMC : M ≤ Subgroup.centralizer (Q : Set P) := by
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro coreElement hcoreElement
    apply Subtype.ext
    have hcentral := (omegaOneCenter_le_centerAmbient (q Γ cp.a)) (hZomega helement)
    have hcore : (coreElement : G) ∈ q Γ cp.a :=
      hQmap ▸ Subgroup.mem_map_of_mem P.subtype hcoreElement
    exact Subgroup.mem_centralizer_iff.mp
      ((centerAmbient_le_centralizer (q Γ cp.a)) hcentral) coreElement hcore
  have hfull : ⁅M, E⁆ = M := by
    apply le_antisymm (Subgroup.commutator_le_left M E)
    exact Subgroup.le_of_centerfree_odd_image_central_subgroup sylow E Q M ⁅M, E⁆
      hcover (pCore_isPGroup (p := 2) (G := P)) hodd
      (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).start_center_trivial
      hMQ hMC le_rfl
  have hm := congrArg (fun D : Subgroup P => D.map P.subtype) hfull
  rw [Subgroup.map_commutator, hMmap, hEmap] at hm
  exact hm

public def distanceOneChiefSubgroup
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) : Subgroup G :=
  Subgroup.commutatorPreimage (q ctx.Γ ctx.criticalPath.a)
    (e ctx.Γ ctx.criticalPath.a) (z ctx.Γ ctx.criticalPath.a)

public theorem distance_one_chief_subgroup_properties
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    distanceOneChiefSubgroup ctx ≤ q ctx.Γ ctx.criticalPath.a ∧
    z ctx.Γ ctx.criticalPath.a ≤ distanceOneChiefSubgroup ctx ∧
    ((distanceOneChiefSubgroup ctx).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a)).Normal ∧
    ⁅distanceOneChiefSubgroup ctx, e ctx.Γ ctx.criticalPath.a⁆ = z ctx.Γ ctx.criticalPath.a ∧
    (∀ D : Subgroup G, D ≤ q ctx.Γ ctx.criticalPath.a →
      ⁅D, e ctx.Γ ctx.criticalPath.a⁆ = z ctx.Γ ctx.criticalPath.a →
      D ≤ distanceOneChiefSubgroup ctx) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Q := q Γ cp.a
  let E := e Γ cp.a
  let Z := z Γ cp.a
  let P := stabilizer Γ cp.a
  have hQP : Q ≤ P := by
    change q Γ cp.a ≤ stabilizer Γ cp.a
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPZ : P ≤ Subgroup.normalizer Z := stabilizer_le_normalizer_z Γ cp.a
  have hQZ := hQP.trans hPZ
  have hZQ : Z ≤ Q :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
      (Subgroup.map_subtype_le _)
  have hPE : P ≤ Subgroup.normalizer E := by
    change stabilizer Γ cp.a ≤ Subgroup.normalizer (e Γ cp.a)
    rw [CosetGraphContext.e, Γ.twoResidualAt_def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le _)).mp
      (twoResidualIn_normal _)
  have hZE : ⁅Z, E⁆ = Z := distance_one_initial_center_full_residual ctx
  refine ⟨Subgroup.commutatorPreimage_le Q E Z,
    Subgroup.le_commutatorPreimage hZQ hZE.le, ?_,
    Subgroup.commutator_commutatorPreimage_eq Q E Z hQZ hZQ hZE, ?_⟩
  · exact Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.commutatorPreimage_normalized Q E Z P hQZ
        (stabilizer_le_normalizer_q Γ cp.a) hPE hPZ)
  · intro D hDQ hDE
    exact Subgroup.le_commutatorPreimage hDQ hDE.le

public instance distanceOneChiefSubgroup_normal_in_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ((distanceOneChiefSubgroup ctx).subgroupOf (q ctx.Γ ctx.criticalPath.a)).Normal := by
  have hprops := distance_one_chief_subgroup_properties ctx
  have hQP : q ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  exact Subgroup.normal_subgroupOf_of_le_normalizer (hQP.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hprops.1.trans hQP)).mp hprops.2.2.1))

public abbrev DistanceOneChiefQuotient
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :=
  (q ctx.Γ ctx.criticalPath.a) ⧸
    (distanceOneChiefSubgroup ctx).subgroupOf (q ctx.Γ ctx.criticalPath.a)

public theorem distance_one_chief_quotient_card
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    Nat.card (DistanceOneChiefQuotient ctx) =
      (distanceOneChiefSubgroup ctx).relIndex (q ctx.Γ ctx.criticalPath.a) := by
  symm
  exact Subgroup.index_eq_card
    (H := (distanceOneChiefSubgroup ctx).subgroupOf (q ctx.Γ ctx.criticalPath.a))

end Stellmacher.SectionNine
