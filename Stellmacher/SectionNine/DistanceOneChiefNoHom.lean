module
public import Stellmacher.SectionNine.DistanceOneChiefFaithful
public import Stellmacher.SectionNine.DistanceOneQuadraticImage
public import Stellmacher.SectionOne.NineCoreSupportDecompositionCountingGeometry
public import Theory.GroupAction.MinimalSixteen

/-!
# No equivariant homomorphism between the distance-one chief modules

In the actual noncentral distance-one branch, every initial-stabilizer
equivariant homomorphism Q_a/C → Z_a is trivial. The second theorem gives
the identical conclusion for a homomorphism Q_a → Z_a killing C, using the
caller's normal-subgroup conjugation actions inside the initial stabilizer.

The faithful initial-center witness has an order-nine odd core, a maximal
Sylow two-subgroup, and a sixteen-element module. The general invariant
simplicity theorem therefore makes every nonzero image equal to Z_a.
Surjectivity transfers quadraticity of the actual U-action on Q_a/C to
Z_a. Equality of the two action kernels gives this U-image order four;
U≤VQ_a puts it inside the extracted cross-center image V. The proved
source-(5) bound allows quadratic subgroups there to have order at most
two, a contradiction. Neither an abstract representation classification
nor irreducibility of Q_a/C is assumed.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), printed pp47–48,
relations (5),(8),(10) and their nonisomorphic-module consequence, in
`refs/files/stellmacher-n-group.pdf`. The quotient and all action maps are
the production conjugation constructions on the original graph.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem quadratic_of_surjective_intertwiner
    {A B W Z : Type*} [Group A] [Group B] [Group W] [Group Z]
    [MulDistribMulAction A W] [MulDistribMulAction B Z]
    (f : W →* Z) (hf : Function.Surjective f)
    (hlink : ∀ b : B, ∃ a : A, ∀ v : W, f (a • v) = b • f v)
    (hquad : commutatorAction₂ A W = ⊥) : commutatorAction₂ B Z = ⊥ := by
  have hcomm : commutatorAction B Z ≤ (commutatorAction A W).map f := by
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨b, z, rfl⟩
    obtain ⟨v, rfl⟩ := hf z
    obtain ⟨a, ha⟩ := hlink b
    refine ⟨v⁻¹ * (a • v), ?_, ?_⟩
    · rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨a, v, rfl⟩
    · rw [map_mul, map_inv, ha]
  have hfix : commutatorAction B Z ≤ FixedPoints.subgroup B Z := by
    intro z hz b
    obtain ⟨v, hv, rfl⟩ := hcomm hz
    obtain ⟨a, ha⟩ := hlink b
    rw [← ha, commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad hv a]
  apply bot_unique
  rw [commutatorAction₂, commutatorSubgroup, Subgroup.closure_le]
  rintro _ ⟨b, z, hz, rfl⟩
  change z⁻¹ * (b • z) = 1
  rw [hfix hz b, inv_mul_cancel]

public theorem distance_one_chief_equivariant_hom_eq_one
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx)
    (f : DistanceOneChiefQuotient ctx.toLocalContext →* z ctx.Γ ctx.criticalPath.a)
    (hequiv : ∀ (actor : stabilizer ctx.Γ ctx.criticalPath.a)
      (point : DistanceOneChiefQuotient ctx.toLocalContext),
      (f (distanceOneChiefAction ctx.toLocalContext actor point) : G) =
        (actor : G) * (f point : G) * (actor : G)⁻¹) : f = 1 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let Q := q Γ cp.a
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hZaP : Za ≤ P := by
    change z Γ cp.a ≤ stabilizer Γ cp.a
    rw [z, Γ.zAt_def]
    apply sSup_le
    rintro center ⟨sylow, rfl⟩
    exact (omegaOneCenter_le_centerAmbient _).trans
      ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))
  obtain ⟨w⟩ := exists_quotientModuleWitness P Za hZaP (stabilizer_le_normalizer_z Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  have hcompat (actor : P) (v : W) : f (action actor v) = w.projection actor • f v := by
    apply Subtype.ext
    exact (hequiv actor v).trans (w.action_compatible actor (f v)).symm
  let D : Subgroup Za := f.range
  have hstable (actor : w.X) (v : Za) (hv : v ∈ D) : actor • v ∈ D := by
    obtain ⟨a, rfl⟩ := w.surjective actor
    obtain ⟨point, rfl⟩ := hv
    exact ⟨action a point, hcompat a point⟩
  let _ : IsInvariant w.X Za D := ⟨fun actor v => ⟨hstable actor v, fun hv => by
    have hh := hstable actor⁻¹ (actor • v) hv
    simpa only [inv_smul_smul] using hh⟩⟩
  obtain ⟨hsetup, hcard, hoddcard, ⟨R, hgen, huniq⟩, X, hX, hXcard⟩ :=
    distance_one_faithful_recognition_setup ctx hb branch.extraction w
  let _ : (SectionOne.oddCore w.X).Normal := pPrimeCore_normal
  let _ : IsElementaryAbelian 3 (SectionOne.oddCore w.X) :=
    SectionOne.nineCore_elementary_of_elementary_four hsetup hoddcard X hX hXcard
  have hRmax : IsCoatom (R : Subgroup w.X) := by
    apply Theory.GroupTheory.sylow_isCoatom_of_elementary_odd_supplement_unique_maximal
      (SectionOne.oddCore w.X) R hgen
    obtain ⟨M, hM, hRM, huniqM⟩ := (uniqueMaximalContaining_top_iff _).mp huniq
    exact ⟨M, ⟨hM, hRM⟩, fun N hN => huniqM N hN.1 hN.2⟩
  have hfixed := SectionOne.nineCoreSupportDecomposition_common_fixed_eq_bot
    (SectionOne.oddCore w.X) hoddcard hcard hsetup.action_faithful
  rcases invariant_eq_bot_or_top_of_nine_actor_maximal_sylow R hRmax hsetup.twoCore_eq_bot
      (SectionOne.oddCore w.X) hoddcard hfixed hcard D with hbot | htop
  · apply MonoidHom.ext
    intro point
    exact Subgroup.mem_bot.mp (hbot ▸ (show f point ∈ D from ⟨point, rfl⟩))
  have hsurj : Function.Surjective f := by
    intro point
    exact htop.ge (Subgroup.mem_top point)
  let J := (branch.U.subgroupOf P).map w.projection
  let JA := (branch.U.subgroupOf P).map action
  have hquad : commutatorAction₂ J Za = ⊥ := by
    apply quadratic_of_surjective_intertwiner (A := JA) f hsurj
    · intro actor
      obtain ⟨a, ha, heq⟩ := actor.property
      refine ⟨⟨action a, Subgroup.mem_map_of_mem action ha⟩, ?_⟩
      intro point
      change f (action a point) = (actor : w.X) • f point
      rw [← heq]
      exact hcompat a point
    · exact distance_one_chief_U_map_quadratic ctx hb branch
  have hkernel : w.projection.ker = action.ker := by
    rw [w.kernel_eq]
    simp only [Subgroup.inf_subgroupOf_left]
    exact (distance_one_chief_action_kernel ctx hb hfaith branch).symm
  have hJcard : Nat.card J = 4 := by
    change Nat.card ((branch.U.subgroupOf P).map w.projection) = 4
    rw [← Subgroup.relIndex_ker, hkernel, Subgroup.relIndex_ker]
    exact distance_one_chief_U_map_card_four ctx hb hfaith branch
  let next := Γ.act branch.extraction.x⁻¹ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  have hVP : V ≤ P := (distance_one_product_factors Γ cp.a next).2.2.1.trans inf_le_left
  have hQP : Q ≤ P := by
    dsimp only [Q, P]
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQkernel : Q.subgroupOf P ≤ w.projection.ker := by
    intro element helement
    rw [w.kernel_eq]
    refine ⟨element.property, ?_⟩
    have hQc : Q ≤ Subgroup.centralizer (Za : Set G) :=
      (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer.ge.trans inf_le_right
    exact hQc helement
  have hJle : J ≤ (V.subgroupOf P).map w.projection := by
    have hle := Subgroup.map_mono (f := w.projection)
      (Subgroup.subgroupOf_mono P branch.le_product_core)
    rw [Subgroup.subgroupOf_sup hVP hQP, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff (Q.subgroupOf P)).mpr hQkernel, sup_bot_eq] at hle
    exact hle
  have hbound := distance_one_quadratic_image_card_le_two ctx hb branch.extraction w J hJle hquad
  rw [hJcard] at hbound
  omega

public theorem distance_one_chief_normal_equivariant_hom_eq_one
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx)
    [((q ctx.Γ ctx.criticalPath.a).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a)).Normal]
    [((z ctx.Γ ctx.criticalPath.a).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a)).Normal]
    (f : ((q ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)) →*
      ((z ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)))
    (hkernel : ((distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a)).subgroupOf
      ((q ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)) ≤ f.ker)
    (hequiv : ∀ (actor : stabilizer ctx.Γ ctx.criticalPath.a) point,
      f (MulAut.conjNormal actor point) = MulAut.conjNormal actor (f point)) : f = 1 := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := q ctx.Γ ctx.criticalPath.a
  let Z := z ctx.Γ ctx.criticalPath.a
  let C := distanceOneChiefSubgroup ctx.toLocalContext
  let _ : (C.subgroupOf Q).Normal := distanceOneChiefSubgroup_normal_in_core ctx.toLocalContext
  have hQP : Q ≤ P := by
    dsimp only [Q, P]
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZP : Z ≤ P := (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1.trans
    ((distance_one_chief_subgroup_properties ctx.toLocalContext).1.trans hQP)
  let eQ : Q.subgroupOf P ≃* Q := Subgroup.subgroupOfEquivOfLe hQP
  let eZ : Z.subgroupOf P ≃* Z := Subgroup.subgroupOfEquivOfLe hZP
  let original : Q →* Z := eZ.toMonoidHom.comp (f.comp eQ.symm.toMonoidHom)
  have hCker : C.subgroupOf Q ≤ original.ker := by
    intro point hpoint
    have hz := hkernel (show eQ.symm point ∈ (C.subgroupOf P).subgroupOf (Q.subgroupOf P)
      from hpoint)
    change f (eQ.symm point) = 1 at hz
    change eZ (f (eQ.symm point)) = 1
    rw [hz, map_one]
  let descended : DistanceOneChiefQuotient ctx.toLocalContext →* Z :=
    QuotientGroup.lift (C.subgroupOf Q) original hCker
  have hdescended : descended = 1 := by
    apply distance_one_chief_equivariant_hom_eq_one ctx hb hfaith branch
    intro actor point
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) point
    have hh := hequiv actor (eQ.symm representative)
    have ha := congrArg (fun value : DistanceOneChiefQuotient ctx.toLocalContext =>
      (descended value : G)) (distance_one_chief_action_apply ctx.toLocalContext actor representative)
    exact ha.trans (congrArg (fun value : Z.subgroupOf P => ((value : P) : G)) hh)
  apply MonoidHom.ext
  intro point
  have hh := congrArg (fun hom : DistanceOneChiefQuotient ctx.toLocalContext →* Z =>
    hom (QuotientGroup.mk' (C.subgroupOf Q) (eQ point))) hdescended
  change eZ (f (eQ.symm (eQ point))) = 1 at hh
  rw [eQ.symm_apply_apply] at hh
  exact eZ.injective (hh.trans (map_one eZ).symm)

end Stellmacher.SectionNine
