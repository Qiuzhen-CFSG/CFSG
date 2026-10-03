module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionNine.NineTwoAmbientCentralizerCommutator
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionEight.LocalQuotientCore
public import Stellmacher.QuotientModuleWitness
public import Stellmacher.DihedralThreePowerCoreQuotient
public import Theory.Representation.CardFourTwoGroupImage
public import Theory.GroupTheory.SpecificGroups.OddDihedralCentralizer

/-!
# The actual Section Nine core quotient from a four-element center

In an ambient-retaining Section Nine context, an explicitly four-element
initial center forces the initial stabilizer modulo its actual two-core
to be SL₂(2). This is the quotient-recognition branch of (9.2); it neither
proves the center's order nor assumes a generating neighbor or (6.4).
Hypothesis Two remains on H, while the graph and its subgroups remain in G.

The faithful center action embeds in GL₂(2). The proper local core and
(7.4) make the Sylow image nontrivial, while the generic faithful center
quotient has trivial two-core. Its order is therefore six. The exact
Sylow/kernel intersection in (7.4) then gives the actual Sylow/core index
two. The proved (3.3)/(3.6) extraction identifies the ordinary core quotient
as an odd dihedral group with cyclic three-power rotation subgroup. This
supplies the cyclic structure behind the source's residual-cyclicity step.

The imported ambient centralizer-commutator lemma uses (7.5), the ambient
P-star residual theorem, and injective Sylow/subnormality transport to
establish the genuine hypotheses of (7.7)(a). Its bound makes the action
kernel centralize the image of the next residual's core in the dihedral
quotient. That image is nontrivial by (7.6), and its centralizer is a
two-group. Hence the normal action kernel is itself a two-group and lies
in the actual core; (7.3) gives the reverse containment. The faithful
projection consequently has precisely the kernel required by the conclusion.

Source: B. Stellmacher, Journal of Algebra 190 (1997), printed p.48 / PDF
p.38, final sentences of (9.2), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
open scoped IsMulCommutative commutatorElement
universe u

private theorem faithful_four_embedding
    {X V : Type u} [Group X] [Group V] [Finite X] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut X V))
    (hcard : Nat.card V = 4) :
    ∃ linear : X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2),
      Function.Injective linear := by
  classical
  let representation := Representation.ofElementaryAbelianAction (A := X) (G := V) (p := 2)
  have hinj : Function.Injective representation.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro actor hactor
    have heq : representation actor = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hactor)
    apply hfaithful
    ext point
    change actor • point = (1 : X) • point
    rw [one_smul]
    apply Additive.ofMul.injective
    have hpoint := LinearMap.congr_fun heq (Additive.ofMul point)
    simpa only [representation, Representation.ofElementaryAbelianAction_apply_ofMul,
      Module.End.one_apply] using hpoint
  have hdim : Module.finrank (ZMod 2) (Additive V) = 2 := by
    have hc : Nat.card (Additive V) = 4 := (Nat.card_congr Additive.toMul).trans hcard
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hc
    norm_num at hc
    exact Nat.pow_right_injective (by omega : 1 < 2) hc
  let basis : Module.Basis (Fin 2) (ZMod 2) (Additive V) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hdim
  exact ⟨(Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
    representation.asGroupHom,
    (Matrix.GeneralLinearGroup.toLin' basis).symm.injective.comp hinj⟩

private noncomputable def gl_equiv_sl :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* SL2Two :=
  (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL ⟨
    Matrix.SpecialLinearGroup.toGL_injective, by
      intro matrix
      have hdet : Matrix.det (matrix : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
        have hu : Matrix.GeneralLinearGroup.det matrix = 1 := Subsingleton.elim _ _
        exact congrArg Units.val hu
      refine ⟨⟨(matrix : Matrix (Fin 2) (Fin 2) (ZMod 2)), hdet⟩, ?_⟩
      exact Units.ext rfl⟩).symm

private theorem nine_two_dihedral_action_of_card_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    (∃ n : ℕ, Nonempty
      ((GAt ctx.Γ ctx.criticalPath.a ⧸ pCore 2 (GAt ctx.Γ ctx.criticalPath.a)) ≃*
        DihedralGroup (3 ^ n))) ∧
    (∀ w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a),
      let _ := w.groupX
      let _ := w.finiteX
      IsSL2Two w.X) := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨_, sylow, hsylow⟩ := hP.1.1.2.1
  have hTP : T ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnative : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hsylow
  have hkernel : ∀ w : QuotientModuleWitness P
      (P ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a),
      let _ := w.groupX
      (sylow : Subgroup P) ⊓ w.projection.ker = pCore 2 P := by
    intro w
    let := w.groupX
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_inf _ _ _ P.subtype_injective, hsylow, w.kernel_eq,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    have h74 := (lemma_seven_four h Γ cp).edge_centralizer
    change T ⊓ (P ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) = twoCoreIn P
    rw [← inf_assoc, inf_eq_left.mpr hTP]
    change T ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G) =
      (pCore 2 (Γ.stabilizer cp.a)).map (Γ.stabilizer cp.a).subtype
    change T ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G) = Γ.twoCoreAt cp.a at h74
    rw [Γ.twoCoreAt_def] at h74
    exact h74
  have haction : ∀ w : QuotientModuleWitness P
      (P ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a),
      let _ := w.groupX
      let _ := w.finiteX
      IsSL2Two w.X := by
    intro w
    let := w.groupX
    let := w.finiteX
    let := MulDistribMulAction.compHom (ZAt Γ cp.a) w.action
    have hfaithful : Function.Injective (MulDistribMulAction.toMulAut w.X (ZAt Γ cp.a)) := by
      intro left right heq
      apply w.action_injective
      ext point
      exact congrArg Subtype.val (DFunLike.congr_fun heq point)
    obtain ⟨linear, hlinear⟩ := faithful_four_embedding hfaithful hcard
    have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    have hdiv := Subgroup.card_dvd_of_injective linear hlinear
    rw [hGL] at hdiv
    let imageSylow := sylow.mapSurjective w.surjective
    have himageNe : (imageSylow : Subgroup w.X) ≠ ⊥ := by
      intro hbot
      have hle := (Subgroup.map_eq_bot_iff _).mp hbot
      have heq : (sylow : Subgroup P) = pCore 2 P := by
        rw [← hkernel w, inf_eq_left.mpr hle]
      apply hP.1.1.2.2.2
      exact hsylow.symm.trans (congrArg (Subgroup.map P.subtype) heq)
    have heven : 2 ∣ Nat.card w.X := by
      let : Nontrivial imageSylow := (Subgroup.nontrivial_iff_ne_bot _).mpr himageNe
      obtain ⟨power, hpos, hpower⟩ :=
        imageSylow.isPGroup'.nontrivial_iff_card.mp inferInstance
      exact (show 2 ∣ Nat.card imageSylow by
        rw [hpower]
        exact dvd_pow_self 2 (by omega)).trans (Subgroup.card_subgroup_dvd_card _)
    have hnotTwo : Nat.card w.X ≠ 2 := by
      intro htwo
      have hgroup : IsPGroup 2 w.X := IsPGroup.of_card (n := 1) (by simpa using htwo)
      have htop : (⊤ : Subgroup w.X) ≤ pCore 2 w.X :=
        le_sSup ⟨inferInstance, hgroup.to_subgroup _⟩
      rw [SectionEight.local_quotient_twoCore_eq_bot Γ cp.a w] at htop
      have hzero : (imageSylow : Subgroup w.X) = ⊥ := bot_unique (le_top.trans htop)
      exact himageNe hzero
    have hsix : Nat.card w.X = 6 := by
      have hle : Nat.card w.X ≤ 6 := Nat.le_of_dvd (by decide) hdiv
      have hcases : ∀ order ≤ 6, order ∣ 6 → 2 ∣ order → order ≠ 2 → order = 6 := by
        decide
      exact hcases _ hle hdiv heven hnotTwo
    have hbij : Function.Bijective linear :=
      (Nat.bijective_iff_injective_and_card linear).mpr ⟨hlinear, hsix.trans hGL.symm⟩
    exact ⟨(MulEquiv.ofBijective linear hbij).trans gl_equiv_sl⟩
  have hZP : ZAt Γ cp.a ≤ P := by
    exact ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      ((Subgroup.map_subtype_le _).trans (by
        change Γ.twoCoreAt cp.a ≤ Γ.stabilizer cp.a
        rw [Γ.twoCoreAt_def]
        exact Subgroup.map_subtype_le _))
  obtain ⟨w⟩ := exists_quotientModuleWitness P (ZAt Γ cp.a) hZP
    (stabilizer_le_normalizer_z Γ cp.a)
  let := w.groupX
  let := w.finiteX
  let imageSylow := sylow.mapSurjective w.surjective
  have himage : Nat.card imageSylow = 2 := by
    rw [imageSylow.card_eq_multiplicity,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (haction w)]
    have hfactorization : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp [hfactorization]
  have hindex : (pCore 2 P).relIndex (sylow : Subgroup P) = 2 := by
    rw [← hkernel w, Subgroup.inf_relIndex_left, Subgroup.relIndex_ker]
    exact himage
  have hcore : pCore 2 P ≠ ⊥ := by
    intro hbot
    apply hP.1.1.2.2.1
    change (pCore 2 P).map P.subtype = ⊥
    rw [hbot, Subgroup.map_bot]
  have hunique : IsUniqueMaximalContaining (sylow : Subgroup P) (⊤ : Subgroup P) := by
    obtain ⟨_, maximal, hmaximal, hcontains, hunique⟩ := hP.1.2
    let equiv := (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P)
    refine ⟨maximal.comap equiv.toMonoidHom, (Subgroup.isCoatom_comap equiv).mpr hmaximal,
      ?_, ?_⟩
    · intro element helement
      refine ⟨⟨element, Subgroup.mem_top _⟩, ?_, rfl⟩
      exact hcontains (hnative ▸ helement)
    · intro other hother hotherContains
      have heq : other.map equiv.toMonoidHom = maximal := by
        apply hunique _ ((OrderIso.isCoatom_iff equiv.mapSubgroup other).mpr hother)
        intro element helement
        exact hotherContains (hnative.symm ▸ helement)
      rw [← heq]
      exact (Subgroup.comap_map_eq_self_of_injective equiv.injective other).symm
  obtain ⟨power, ⟨equiv⟩⟩ := dihedral_three_power_core_quotient hP.2 sylow hcore
    hunique hindex w.projection w.surjective (haction w)
  exact ⟨⟨power, ⟨equiv⟩⟩, haction⟩

/-- A four-element initial center identifies the ordinary two-core quotient,
with Hypothesis Two retained on the original ambient group. -/
public theorem nine_two_core_quotient_of_card_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Z := ZAt Γ cp.a
  let Q := QAt Γ cp.a
  let R := twoCoreIn (EAt Γ cp.firstStep)
  have hbound := nine_two_initial_centralizer_commutator ctx
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    SevenSix.mem_neighborhood_iff_adjacent Γ |>.mpr cp.firstStep_adj
  have hQP : Q ≤ P := by
    change Γ.twoCoreAt cp.a ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZQ : Z ≤ Q :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      (Subgroup.map_subtype_le _)
  have hQnative : Q.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.a).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hRT : R ≤ T := by
    have hRQ : R ≤ QAt Γ cp.firstStep := by
      change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
      rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, SevenSix.residual_core_eq_inter_core]
      exact inf_le_right
    exact hRQ.trans (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hRP : R ≤ P := hRT.trans (cp.S_le_edge_stabilizers.trans inf_le_left)
  obtain ⟨w⟩ := exists_quotientModuleWitness P Z (hZQ.trans hQP)
    (stabilizer_le_normalizer_z Γ cp.a)
  let := w.groupX
  let := w.finiteX
  obtain ⟨⟨power, ⟨equiv⟩⟩, haction⟩ := nine_two_dihedral_action_of_card_four ctx hcard
  let projection : P →* DihedralGroup (3 ^ power) :=
    equiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hprojection : projection.ker = pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective]
    exact QuotientGroup.ker_mk' _
  let actor := (R.subgroupOf P).map projection
  have hactor : IsPGroup 2 actor :=
    ((pCore_isPGroup (G := EAt Γ cp.firstStep) (p := 2)).map
      (EAt Γ cp.firstStep).subtype).comap_subtype.map projection
  have hactorNe : actor ≠ ⊥ := by
    intro hbot
    have hle := (Subgroup.map_eq_bot_iff _).mp hbot
    rw [hprojection, ← hQnative] at hle
    apply (lemma_seven_six h Γ cp).next_residual_core.1
    intro element helement
    exact hle (show (⟨element, hRP helement⟩ : P) ∈ R.subgroupOf P from helement)
  have hcentralizer := DihedralGroup.isPGroup_centralizer_of_nontrivial_two_subgroup
    ((by decide : Odd 3).pow) actor hactor hactorNe
  have hkernelImage : w.projection.ker.map projection ≤
      Subgroup.centralizer (actor : Set (DihedralGroup (3 ^ power))) := by
    rintro image ⟨element, helement, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro other ⟨actorElement, hactorElement, rfl⟩
    have helementC : (element : G) ∈ Subgroup.centralizer (Z : Set G) := by
      rw [w.kernel_eq] at helement
      exact helement.2
    have hcommQ : ⁅(element : G), (actorElement : G)⁆ ∈ Q :=
      hbound (Subgroup.commutator_mem_commutator helementC
        ((le_sup_right : R ≤ EAt Γ cp.a ⊔ R) hactorElement))
    have hcomm : ⁅element, actorElement⁆ ∈ projection.ker := by
      rw [hprojection, ← hQnative]
      exact hcommQ
    have hzero : ⁅projection element, projection actorElement⁆ = 1 := by
      rw [← map_commutatorElement]
      exact hcomm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm
  have hkernelTwo : IsPGroup 2 w.projection.ker := by
    have hprojTwo : IsPGroup 2 projection.ker := by
      rw [hprojection]
      exact pCore_isPGroup
    exact ((hcentralizer.to_le hkernelImage).comap_of_ker_isPGroup projection
      hprojTwo).to_le (Subgroup.le_comap_map _ _)
  have hkernelCore : w.projection.ker ≤ pCore 2 P :=
    le_sSup ⟨inferInstance, hkernelTwo⟩
  have hcoreKernel : pCore 2 P ≤ w.projection.ker := by
    have hZcentral : Z ≤ Subgroup.centralizer (Q : Set G) :=
      ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient Q).trans
          (SevenSix.centerAmbient_le_centralizer Q))
    intro element helement
    rw [w.kernel_eq]
    refine ⟨element.property, (Subgroup.le_centralizer_iff.mp hZcentral) ?_⟩
    change element ∈ Q.subgroupOf P
    rwa [hQnative]
  obtain ⟨actionEquiv⟩ := haction w
  refine ⟨actionEquiv.toMonoidHom.comp w.projection,
    actionEquiv.surjective.comp w.surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ actionEquiv.injective,
    le_antisymm hkernelCore hcoreKernel]
  exact hQnative.symm

end Stellmacher.SectionNine
