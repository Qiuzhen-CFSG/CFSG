module
public import Stellmacher.SectionNine.DistanceOneV1ElementaryQuotient
public import Stellmacher.SectionNine.DistanceOneInvolutionResidualActor
public import Theory.GroupAction.QuotientConjugationFixedBound
public import Stellmacher.SectionThree.ResidualImageOddPGroup
public import Stellmacher.SectionOne.LemmaOneThree
/-!
# The actual maximal V₁ quotient action in the (9.1) dichotomy

In the ambient critical-length-one configuration, suppose U satisfies the
proved maximal-V₁ commutator and Sylow-normality properties, with nontrivial
initial-center action of index at most four. This module classifies the
actual residual image on the literal quotient U/Z_terminal by the three
alternatives of (1.3). It retains quotient normality, elementary structure,
the exact conjugation homomorphism, its killed terminal core, its full
residual action, and the selected involution in the initial center.
Together with full action, the existing conclusion's action-commutator
orders are precisely the orders 4, 16, or 64 of the whole quotient.

Sylow normality and full residual commutators make U invariant under the
terminal stabilizer. The central elementary terminal vertex subgroup
makes U/Z an elementary module. The terminal core acts trivially on it.
A central nontrivial initial-center image modulo that core supplies an
involution x whose core-extension is Sylow-normal; (3.4) therefore makes
the residual image a full commutator with x's image. Lemma (3.3) makes
this residual image an odd p-group. The initial centralizer-index bound
descends to the actual quotient action, and the reduced (1.3) theorem
applies inside its full automorphism group, whose action is faithful.

Source: Stellmacher, Journal of Algebra 190 (1997), p.47, the application
of (1.3) after (9.1)(9). The image here acts on U/Z; identification with
the action on U itself or the terminal core quotient is a separate local
transfer. No faithful initial-center classification or core equality is
assumed or concluded by this packet.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
private theorem quotient_actor_full
    {G X : Type u} [Group G] [Group X] (P E Q : Subgroup G)
    (hEP : E ≤ P) (hQP : Q ≤ P) (x : G) (hxP : x ∈ P)
    (hfull : ⁅E, Q ⊔ Subgroup.zpowers x⁆ = E)
    (ρ : P →* X) (hker : Q.subgroupOf P ≤ ρ.ker) :
    ⁅(E.subgroupOf P).map ρ, Subgroup.zpowers (ρ ⟨x,hxP⟩)⁆ =
      (E.subgroupOf P).map ρ := by
  let K := Q ⊔ Subgroup.zpowers x
  have hKP : K ≤ P := sup_le hQP (Subgroup.zpowers_le.mpr hxP)
  have hn : ⁅E.subgroupOf P, K.subgroupOf P⁆ = E.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEP,
      Subgroup.map_subgroupOf_eq_of_le hKP, hfull]
  have hK : K.subgroupOf P = Q.subgroupOf P ⊔ Subgroup.zpowers (⟨x,hxP⟩ : P) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKP, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hQP, MonoidHom.map_zpowers]
    rfl
  have hmapK : (K.subgroupOf P).map ρ = Subgroup.zpowers (ρ ⟨x,hxP⟩) := by
    rw [hK, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hker,
      bot_sup_eq, MonoidHom.map_zpowers]
  rw [← hmapK, ← Subgroup.map_commutator, hn]

private theorem automorphism_action_faithful
    (W : Type u) [Group W] : fixingSubgroup (MulAut W) (Set.univ : Set W) = ⊥ := by
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  ext w
  rw [mem_fixingSubgroup_iff] at hf
  exact hf w (Set.mem_univ w)
private theorem classification_of_full
    (W : Type u) [Group W] [Finite W] [Nontrivial W]
    [IsElementaryAbelian 2 W]
    (F : Subgroup (MulAut W)) (x : MulAut W)
    (hxpow : x ^ 2 = 1) (hFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hFW : commutatorAction F W = ⊤)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (hFp : IsPGroup p F)
    (hindex : Nat.card W ≤ 4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) W)) :
    _root_.IsInvolution x ∧ SectionOne.LemmaOneThreeConclusion (MulAut W) W x F := by
  have hFne : F ≠ ⊥ := by
    intro hF
    have hbot : commutatorAction F W = ⊥ := by
      apply le_antisymm _ bot_le
      rw [commutatorAction_eq_closure]
      apply (Subgroup.closure_le (K := (⊥ : Subgroup W))).mpr
      rintro _ ⟨f,w,rfl⟩
      have hf : f = 1 := Subtype.ext (Subgroup.mem_bot.mp (hF ▸ f.property))
      simp [hf]
    exact top_ne_bot (hFW.symm.trans hbot)
  have hx : _root_.IsInvolution x := by
    refine ⟨?_,hxpow⟩
    intro hxeq
    apply hFne
    rw [hxeq, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right] at hFx
    exact hFx.symm
  let _ : Fact p.Prime := ⟨hp⟩
  have hodd : Nat.Coprime 2 (Nat.card F) := by
    obtain ⟨n,hn⟩ := hFp.exists_card_eq
    rw [hn]
    exact (hpodd.pow).coprime_two_left
  refine ⟨hx,?_⟩
  rcases SectionOne.involutionPGroup_smallIndex_classification_on_commutator
    F hFne p hFp hodd x hx hFx hindex (automorphism_action_faithful W)
    with hsmall | hsmall | hlarge
  · exact .cyclicThree hsmall.1 hsmall.2
  · exact .small hsmall.1 hsmall.2.1 hsmall.2.2
  · exact .extraspecial hlarge.1 hlarge.2.1 hlarge.2.2.1 hlarge.2.2.2.1 hlarge.2.2.2.2
public theorem distance_one_v1_action_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (U : Subgroup G)
    (hUQ : U ≤ q ctx.Γ ctx.criticalPath.a')
    (hZU : z ctx.Γ ctx.criticalPath.a' ≤ U)
    (hUQc : ⁅U,q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a')
    (hUE : ⁅U,twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = U)
    (hUT : U ≤ T) (hUn : (U.subgroupOf T).Normal)
    (hlow : Nat.card (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G)
      < Nat.card U)
    (hupper : Nat.card U ≤ 4 * Nat.card
      (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G)) :
    ∃ hN : ((z ctx.Γ ctx.criticalPath.a').subgroupOf U).Normal,
      let _ := hN
      let P := stabilizer ctx.Γ ctx.criticalPath.a'
      let Z := z ctx.Γ ctx.criticalPath.a'
      ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
      let _ := hW
      Nontrivial (U ⧸ Z.subgroupOf U) ∧
      ∃ hPU : P ≤ Subgroup.normalizer (U : Set G),
      ∃ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
        (∀ p : P, ∀ u : U, ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U) ⟨(p:G)*(u:G)*(p:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) ∧
        (q ctx.Γ ctx.criticalPath.a').subgroupOf P ≤ ρ.ker ∧
        commutatorAction ((twoResidualIn P).subgroupOf P |>.map ρ)
          (U ⧸ Z.subgroupOf U) = ⊤ ∧
        ∃ x : P, (x:G) ∈ z ctx.Γ ctx.criticalPath.a ∧ _root_.IsInvolution (x:G) ∧
          (x:G) ∉ q ctx.Γ ctx.criticalPath.a' ∧ _root_.IsInvolution (ρ x) ∧
          ⁅(twoResidualIn P).subgroupOf P |>.map ρ, Subgroup.zpowers (ρ x)⁆ =
            ((twoResidualIn P).subgroupOf P |>.map ρ) ∧
          SectionOne.LemmaOneThreeConclusion (MulAut (U ⧸ Z.subgroupOf U))
            (U ⧸ Z.subgroupOf U) (ρ x) ((twoResidualIn P).subgroupOf P |>.map ρ) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a'
  let Z := z Γ cp.a'
  let Q := q Γ cp.a'
  let E := twoResidualIn P
  let A0 := z Γ cp.a
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hlocal : P ∈ PFamily (⊤ : Subgroup G) T ∧ Group.IsSolvable P := by
    have heq := congrArg (fun b => stabilizer Γ b ∈ PFamily (⊤ : Subgroup G) T ∧
      Group.IsSolvable (stabilizer Γ b)) hstep
    exact heq.mp (edge_local_data ctx.sectionSeven Γ cp).2
  have hsylow : IsSylowTwoIn T P := by
    have heq := congrArg (fun b => IsSylowTwoIn T (stabilizer Γ b)) hstep
    exact heq.mp (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hQP : Q ≤ P := by
    change q Γ cp.a' ≤ stabilizer Γ cp.a'
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hEP : E ≤ P := Subgroup.map_subtype_le _
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := by
    rw [← twoResidualIn_sup_sylow hsylow]
    exact sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mpr hUE.le)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mp hUn)
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ cp.a'
  obtain ⟨hN, hW⟩ := distance_one_v1_quotient_elementary ctx hb U hUQ hZU hUQc hUE
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  have hZcentral : Z ≤ Subgroup.centralizer (P : Set G) := by
    have h75 := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.2
    rw [hstep] at h75
    change z Γ cp.a' ≤ _
    rw [h75]
    exact (omegaOneCenter_le_centerAmbient P).trans (centerAmbient_le_centralizer P)
  have hneighbor : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  have hAT : A0 ≤ T :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.a' hneighbor).trans
      ((Subgroup.map_subtype_le _).trans
        (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1)
  have hAP : A0 ≤ P := hAT.trans hsylow.1
  have hncentral : ¬ U ≤ Subgroup.centralizer (A0 : Set G) := by
    intro hh
    have heq : U ⊓ Subgroup.centralizer (A0 : Set G) = U := inf_eq_left.mpr hh
    change Nat.card (U ⊓ Subgroup.centralizer (A0:Set G):Subgroup G) < Nat.card U at hlow
    have hh : Nat.card U < Nat.card U := by simpa only [heq] using hlow
    exact (Nat.lt_irrefl _) hh
  obtain ⟨u, hu, hunc⟩ := Set.not_subset.mp hncentral
  let uU : U := ⟨u,hu⟩
  have hWne : (QuotientGroup.mk' (Z.subgroupOf U) uU : W) ≠ 1 := by
    intro hh
    have hzu : uU ∈ Z.subgroupOf U := (QuotientGroup.eq_one_iff _).mp hh
    have hz : u ∈ Z := hzu
    exact hunc ((hZcentral.trans (Subgroup.centralizer_le hAP)) hz)
  let _ : Nontrivial W := ⟨⟨_,1,hWne⟩⟩
  obtain ⟨ρ,hρ,hker,hfull⟩ := Subgroup.exists_quotient_conjugation_full_action
    P U Z E Q hPU hPZ hN hEP hUE hUQc.le
  have hcoreker : pCore 2 P ≤ ρ.ker := by
    intro a ha
    apply hker
    change (a:G) ∈ q Γ cp.a'
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype ha
  obtain ⟨p,hp,hodd,hFp⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    T (sectionThreeHypotheses ctx.sectionSeven) P
    ((pFamily_iff_pSet ⊤ T P).mp hlocal.1) hlocal.2 ρ hcoreker
  have hEsub : E.subgroupOf P = twoResidualSubgroup P := by
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  rw [← hEsub] at hFp
  obtain ⟨x,hx,hxi,hxQ,hKT,hKn,hEx⟩ := distance_one_involution_residual_actor ctx hb
  let xP : P := ⟨x,hAP hx⟩
  have hFx := quotient_actor_full P E Q hEP hQP x xP.property hEx ρ hker
  have hxsq : (ρ xP)^2=1 := by
    rw [← map_pow]
    have hxp : xP^2=1 := Subtype.ext hxi.2
    rw [hxp,map_one]
  have hindex := Subgroup.quotient_conjugation_fixed_card_bound P U Z A0 hPU hN
    ρ hρ xP hx 4 hupper
  have hclass := classification_of_full W _ (ρ xP) hxsq hFx hfull p hp hodd hFp hindex
  exact ⟨hN,hW,inferInstance,hPU,ρ,hρ,hker,hfull,xP,hx,hxi,hxQ,hclass.1,hFx,hclass.2⟩
end Stellmacher.SectionNine
