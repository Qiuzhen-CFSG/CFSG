module
public import Stellmacher.SectionEight.LemmaEightOne
public import Stellmacher.SectionEight.LocalQuotientSL2
public import Stellmacher.DihedralThreePowerCoreQuotient
public import Theory.Representation.CardFourTwoGroupImage

/-!
# The initial dihedral core quotient from a four-element center

In the noncommuting critical-pair context of Section Eight, an initial
center of order four forces its faithful action quotient to be SL₂(2)
and its ordinary two-core quotient to be dihedral of order twice a power
of three. No centrality assumption at the first neighbor is required.
This is the conditional bridge in the first proof paragraph of (8.5),
`refs/files/stellmacher-n-group.pdf`, PDF page 30 / journal page 40.

The nontrivial offender and the proved (8.1) decomposition supply an SL₂(2)
factor. Faithfulness embeds the action group in GL₂(2), of order six, so
that factor is the entire action group. Its Sylow subgroup has order two.
The essential transfer uses (7.4): the intersection of the actual initial
Sylow with the action kernel is the actual two-core. Thus the native
Sylow/core relative index is two, not merely an action-image index.
The local P-family data supply solvability, nontrivial core, and unique
maximal containment for `dihedral_three_power_core_quotient`, which
packages the valid (3.3)/(3.6) extraction. Finally the existing faithful
local-quotient theorem gives SL₂(2) for every exact quotient-module witness.
This leaf is used by the ordinary-quotient recognition step of (8.5).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped IsMulCommutative
universe u

private theorem faithful_four_card_bound
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut G V))
    (hcard : Nat.card V = 4) : Nat.card G ≤ 6 := by
  classical
  let representation := Representation.ofElementaryAbelianAction (A := G) (G := V) (p := 2)
  have hinj : Function.Injective representation.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro actor hactor
    have heq : representation actor = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hactor)
    apply hfaithful
    ext point
    change actor • point = (1 : G) • point
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
  let linear : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp representation.asGroupHom
  have hlinear := (Matrix.GeneralLinearGroup.toLin' basis).symm.injective.comp hinj
  have hdiv := Subgroup.card_dvd_of_injective linear hlinear
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  rw [hGL] at hdiv
  exact Nat.le_of_dvd (by decide) hdiv

/-- A four-element initial center gives the actual dihedral core quotient
and identifies every exact faithful center-action quotient with SL₂(2). -/
public theorem eight_five_dihedral_action_of_card_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    (∃ n : ℕ, Nonempty
      ((GAt ctx.Γ ctx.criticalPath.a ⧸ pCore 2 (GAt ctx.Γ ctx.criticalPath.a)) ≃*
        DihedralGroup (3 ^ n))) ∧
    (∀ w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a),
      let _ := w.groupX
      let _ := w.finiteX
      IsSL2Two w.X) := by
  classical
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  obtain ⟨w, hw⟩ := (lemma_eight_one ctx).barred_decomposition
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt Γ cp.a) w.action
  obtain ⟨rank, factors, lifts, modules, fixed, barredJ, liftedJ,
    _hJlift, hJ, _hlifts, hjoin, _hprod, hSL, _hrest⟩ := hw
  have hJne := (lemma_eight_one_offender ctx w).2
  have hrank : 0 < rank := by
    by_contra hzero
    have hr : rank = 0 := by omega
    have hempty : (⨆ index : Fin rank, factors index) = ⊥ := by
      apply bot_unique
      refine iSup_le fun index => ?_
      have := index.isLt
      omega
    rw [hempty] at hjoin
    apply hJne
    rw [← hJ]
    exact bot_unique (le_sup_right.trans_eq hjoin)
  let first : Fin rank := ⟨0, hrank⟩
  have hfaithful : Function.Injective (MulDistribMulAction.toMulAut w.X (ZAt Γ cp.a)) := by
    intro left right heq
    apply w.action_injective
    ext point
    exact congrArg Subtype.val (DFunLike.congr_fun heq point)
  have hbound : Nat.card w.X ≤ 6 :=
    faithful_four_card_bound hfaithful hcard
  have hfactor : Nat.card (factors first) = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (hSL first)
  have htop : factors first = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm (Subgroup.card_le_card_group _) (by omega)
  have haction : IsSL2Two w.X := by
    obtain ⟨equiv⟩ := hSL first
    rw [htop] at equiv
    exact ⟨Subgroup.topEquiv.symm.trans equiv⟩
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨_, sylow, hsylow⟩ := hP.1.1.2.1
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hsylow
  let imageSylow := sylow.mapSurjective w.surjective
  have himage : Nat.card imageSylow = 2 := by
    rw [imageSylow.card_eq_multiplicity,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card haction]
    have hfactorization : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp [hfactorization]
  have hkernel : (sylow : Subgroup P) ⊓ w.projection.ker = pCore 2 P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_inf _ _ _ P.subtype_injective, hsylow, w.kernel_eq,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    have h74 := (lemma_seven_four h Γ cp).edge_centralizer
    change S ⊓ (P ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set H)) = twoCoreIn P
    rw [← inf_assoc, inf_eq_left.mpr hSP]
    change S ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set H) =
      (pCore 2 (Γ.stabilizer cp.a)).map (Γ.stabilizer cp.a).subtype
    change S ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set H) = Γ.twoCoreAt cp.a at h74
    rw [Γ.twoCoreAt_def] at h74
    exact h74
  have hindex : (pCore 2 P).relIndex (sylow : Subgroup P) = 2 := by
    rw [← hkernel, Subgroup.inf_relIndex_left, Subgroup.relIndex_ker]
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
    hunique hindex w.projection w.surjective haction
  exact ⟨⟨power, ⟨equiv⟩⟩, fun witness =>
    local_quotient_isSL2Two_of_dihedral_core ctx witness power equiv⟩

end Stellmacher.SectionEight
