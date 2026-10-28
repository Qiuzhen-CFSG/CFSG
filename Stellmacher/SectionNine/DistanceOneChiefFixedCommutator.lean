module
public import Stellmacher.SectionNine.DistanceOneChiefFixedLayerNormalizer
public import Theory.GroupAction.Extraspecial27QuadraticNormalizer

/-!
# The terminal bound on the chief fixed-subgroup commutator

In the noncentral distance-one branch, let D be an odd subgroup of the
initial stabilizer, fixed-point-free on Z_a, whose chief image is normalized
by the U-image. Then [C_{Q_a}(D),U] lies in Z_a.

The actual layer L=C_{Q_a}(D)Z_a is elementary and U-normal. Its terminal
action on U/Z_terminal is therefore quadratic and normalizes the full
extraspecial27 residual image. It contains the distinguished initial-center
involution, whose displacement has order4. The pure quadratic-normalizer
bound forces the L-image to have order at most2, hence it equals the cyclic
image of that involution and lies in the Z_a-image. Exact quotient-action
commutator transport now puts [U,L], and thus the asserted commutator, in
Z_a because the terminal center already lies there.

This proves the terminal implication in the D* contradiction of Stellmacher
(9.1), Journal of Algebra190 (1997), p.48. It gives the required commutator
bound directly; no exact terminal action kernel is an assumption.
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_fixed_subgroup_commutator_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx)
    (D : Subgroup G) (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hDodd : Odd (Nat.card D))
    (hfree : z ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hnormalizes : (branch.U.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
      (distanceOneChiefAction ctx.toLocalContext) ≤
      Subgroup.normalizer ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext) : Set _)) :
    ⁅q ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (D : Set G), branch.U⁆ ≤
      z ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Q := q Γ cp.a
  let Z := z Γ cp.a
  let Q0 := Q ⊓ Subgroup.centralizer (D : Set G)
  let L := Q0 ⊔ Z
  have hterminalResidual : ⁅branch.U,twoResidualIn (stabilizer Γ cp.a')⁆ = branch.U := by
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using branch.terminal_residual_commutator
  obtain ⟨hN,hW,hUcard,hWcard,hWne,hPU,ρ,hρ,hker,hfull,x,hx,hxi,hxout,hρxi,hgen,hindex,hcenter,hF,hFcard⟩ :=
    distance_one_large_v1_quotient_action ctx hb branch.U branch.le_terminal_core
      branch.terminal_center_le branch.terminal_core_commutator hterminalResidual branch.le_sylow
      branch.normal_in_sylow branch.action_nontrivial branch.action_upper branch.noncentral
  let _ := hN
  let _ := hW
  let P := stabilizer Γ cp.a'
  let K := z Γ cp.a'
  let W := branch.U ⧸ K.subgroupOf branch.U
  let F := ((twoResidualIn P).subgroupOf P).map ρ
  let actors := (L.subgroupOf P).map ρ
  have hstep : cp.firstStep = cp.a' := by
    rw [← cp.path_end, ← cp.path_first]
    congr 1
    exact Fin.ext hb.symm
  have hZQ : Z ≤ Q := ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans (Subgroup.map_subtype_le _)
  have hQT : Q ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hTP : T ≤ P := by
    change T ≤ stabilizer Γ cp.a'
    rw [← hstep]
    exact (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  have hLP : L ≤ P := (sup_le inf_le_left hZQ).trans (hQT.trans hTP)
  have hZP : Z ≤ P := hZQ.trans (hQT.trans hTP)
  have hUPinitial := branch.le_sylow.trans (edge_sylow_data ctx.sectionSeven Γ cp).1.1
  obtain ⟨hUnorm,hquadAmbient⟩ := distance_one_chief_fixed_layer_normalizer ctx hb hfaith branch
    D branch.U hDP hUPinitial hDodd hfree hnormalizes
  have hquad : commutatorAction₂ actors W = ⊥ :=
    Subgroup.quotient_conjugation_quadratic_of_double_commutator_le P branch.U K L hPU hLP hN
      (by rw [hquadAmbient]; exact bot_le) ρ hρ
  let _ : ((twoResidualIn P).subgroupOf P).Normal := twoResidualIn_normal P
  have hAnorm : actors ≤ Subgroup.normalizer (F : Set (MulAut W)) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro actor ⟨a,ha,rfl⟩ f ⟨b,hb,rfl⟩
    refine ⟨a*b*a⁻¹, Subgroup.Normal.conj_mem inferInstance b hb a, ?_⟩
    simp only [map_mul,map_inv]
  have hxL : (x : G) ∈ L := (le_sup_right : Z ≤ L) hx
  let xA : actors := ⟨ρ x, Subgroup.mem_map_of_mem ρ hxL⟩
  let R := Subgroup.zpowers (ρ x)
  have hRcard : Nat.card R = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hρxi.2 hρxi.1
  have hRdisp : Nat.card (commutatorAction R W) = 4 := by
    let generator : R := ⟨ρ x,Subgroup.mem_zpowers _⟩
    have hg : generator ≠ 1 ∧ generator ^ 2 = 1 :=
      ⟨fun heq => hρxi.1 (congrArg Subtype.val heq), Subtype.ext hρxi.2⟩
    have hc := (card_two_action_fixed_commutator_card_data (U := W) generator hg hRcard).1
    change Nat.card W = 4 * Nat.card (FixedPoints.subgroup R W) at hindex
    change Nat.card W = Nat.card (FixedPoints.subgroup R W) * Nat.card (commutatorAction R W) at hc
    change Nat.card W = 64 at hWcard
    have hfixcard : Nat.card (FixedPoints.subgroup R W) = 16 := by omega
    rw [hWcard,hfixcard] at hc
    omega
  have hAcard : Nat.card actors ≤ 2 := extraspecial27_quadratic_normalizer_card_le_two
    F actors hF hFcard hAnorm hquad xA hρxi hfull hgen hcenter hRdisp
  have hRA : R ≤ actors := Subgroup.zpowers_le.mpr xA.property
  have hReq : R = actors := Subgroup.eq_of_le_of_card_ge hRA (by rw [hRcard]; exact hAcard)
  let Zi := (Z.subgroupOf P).map ρ
  have hAZ : actors ≤ Zi := by
    rw [← hReq]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem ρ hx)
  have hdisp_le : commutatorAction actors W ≤ commutatorAction Zi W := by
    rw [commutatorAction_eq_closure,commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨a,w,rfl⟩
    exact ⟨⟨a,hAZ a.property⟩,w,rfl⟩
  have hUZ : ⁅branch.U,Z⁆ ≤ Z :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hUPinitial.trans (stabilizer_le_normalizer_z Γ cp.a))
  let projection : branch.U →* W := QuotientGroup.mk' (K.subgroupOf branch.U)
  have hmapL := Subgroup.quotient_conjugation_commutatorAction_eq_image P branch.U K L hPU hLP hN ρ hρ
  have hmapZ := Subgroup.quotient_conjugation_commutatorAction_eq_image P branch.U K Z hPU hZP hN ρ hρ
  have hcommMap : (⁅branch.U,L⁆.subgroupOf branch.U).map projection ≤
      (Z.subgroupOf branch.U).map projection := by
    rw [← hmapL]
    exact hdisp_le.trans (hmapZ.le.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hUZ)))
  have hKZ : K ≤ Z := distance_one_terminal_center_le_initial_center ctx.toLocalContext hb
  have hpre : ((Z.subgroupOf branch.U).map projection).comap projection = Z.subgroupOf branch.U := by
    apply Subgroup.comap_map_eq_self
    intro u hu
    exact hKZ ((QuotientGroup.eq_one_iff u).mp hu)
  have hcommNative : ⁅branch.U,L⁆.subgroupOf branch.U ≤ Z.subgroupOf branch.U := by
    have hh := (Subgroup.map_le_iff_le_comap).mp hcommMap
    rwa [hpre] at hh
  have hcommU : ⁅branch.U,L⁆ ≤ branch.U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLP.trans hPU)
  have hcommL : ⁅branch.U,L⁆ ≤ Z := by
    have hh := Subgroup.map_mono (f := branch.U.subtype) hcommNative
    rw [Subgroup.map_subgroupOf_eq_of_le hcommU] at hh
    exact hh.trans (by
      rintro z ⟨u,hu,rfl⟩
      exact hu)
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono le_rfl le_sup_left).trans hcommL
end Stellmacher.SectionNine
