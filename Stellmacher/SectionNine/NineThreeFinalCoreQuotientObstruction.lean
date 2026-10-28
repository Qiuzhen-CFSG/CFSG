module

public import Stellmacher.SectionNine.NineThreeNormalizedPairCentralizer
public import Stellmacher.TwoResidualIdentification
public import FeitThompson.BGsection1.PLengthLemmas
public import Mathlib.GroupTheory.Transfer

/-!
# The actual mixed centralizer has no two-nilpotent core quotient

The unchanged first extracted residual escapes the odd-core layer of the
mixed centralizer. A homomorphism into a two-group kills the two-residual,
so the quotient of C/O₂(C) by its odd core cannot be a two-group.
Burnside transfer then excludes Sylow subgroups of order at most two in
C/O₂(C). This uses the actual residual obstruction, not the separate
odd-layer action noncontainment theorem.

These are necessary conditions on the original configuration. They do not
prove the outstanding order-eight odd-layer containment, or assert an
upper bound on the quotient Sylow order from hyperplane cardinality alone.

Source: Stellmacher (9.3), printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`, final R₀,C₀ paragraph.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem normal_two_complement_of_sylow_card_le_two
    {K : Type*} [Group K] [Finite K]
    (sylow : Sylow 2 K) (hsmall : Nat.card sylow ≤ 2) :
    HasNormalPComplement 2 K := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentral : Subgroup.normalizer (sylow : Set K) ≤
      Subgroup.centralizer (sylow : Set K) := by
    by_cases hone : Nat.card sylow ≤ 1
    · have hbot : (sylow : Subgroup K) = ⊥ := Subgroup.eq_bot_of_card_le _ hone
      intro actor _
      apply Subgroup.mem_centralizer_iff.mpr
      intro element helement
      have heq : element = 1 := (hbot ▸ helement : element ∈ (⊥ : Subgroup K))
      simp [heq]
    · have htwo : Nat.card sylow = 2 := by omega
      obtain ⟨distinguished, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : sylow)).mp htwo
      intro actor hactor
      apply Subgroup.mem_centralizer_iff.mpr
      intro element helement
      by_cases heq : element = 1
      · simp [heq]
      let original : sylow := ⟨element, helement⟩
      let conjugate : sylow := ⟨actor * element * actor⁻¹, (hactor element).mp helement⟩
      have horiginal : original ≠ 1 := fun h => heq (congrArg Subtype.val h)
      have hconjugate : conjugate ≠ 1 := by
        intro h
        have hvalue := congrArg (fun member : sylow => actor⁻¹ * (member : K) * actor) h
        apply heq
        simpa [conjugate, mul_assoc] using hvalue
      have hsame : conjugate = original :=
        (hunique conjugate hconjugate).trans (hunique original horiginal).symm
      have hvalue := congrArg (fun member : sylow => (member : K) * actor) hsame
      simpa [conjugate, original, mul_assoc] using hvalue.symm
  let transfer := MonoidHom.transferSylow sylow hcentral
  have hcoprime : Nat.Coprime 2 (Nat.card transfer.ker) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow sylow hcentral)
  have hquotient : IsPGroup 2 (K ⧸ transfer.ker) :=
    (sylow.isPGroup'.to_subgroup transfer.range).of_equiv
      (QuotientGroup.quotientKerEquivRange transfer).symm
  exact ⟨transfer.ker, inferInstance, hcoprime, hquotient⟩

public theorem residual_image_le_of_two_group_quotient
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (embedding : G →* H) (actor : Subgroup G) (overgroup : Subgroup H)
    (hactor : actor.map embedding ≤ overgroup)
    (kernel : Subgroup overgroup) [kernel.Normal]
    (hquotient : IsPGroup 2 (overgroup ⧸ kernel)) :
    ((twoResidualAmbient actor).map embedding).subgroupOf overgroup ≤ kernel := by
  let inclusion : actor →* overgroup :=
    (embedding.comp actor.subtype).codRestrict overgroup (by
      intro element
      exact hactor ⟨element, element.property, rfl⟩)
  let quotient := (QuotientGroup.mk' kernel).comp inclusion
  have hrange : IsPGroup 2 quotient.range := hquotient.to_subgroup quotient.range
  have hquot : IsPGroup 2 (actor ⧸ quotient.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange quotient).symm
  have hresidual : twoResidualSubgroup actor ≤ quotient.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_le quotient.ker inferInstance hquot
  intro element helement
  obtain ⟨original, horiginal, heq⟩ := helement
  obtain ⟨member, hmember, rfl⟩ := horiginal
  have hzero := hresidual hmember
  change QuotientGroup.mk' kernel (inclusion member) = 1 at hzero
  have hmem := (QuotientGroup.eq_one_iff (N := kernel) (inclusion member)).mp hzero
  have heq' : inclusion member = element := Subtype.ext heq
  exact heq' ▸ hmem

public theorem nine_three_final_odd_core_quotient_not_two_group
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    ¬ IsPGroup 2 ((centralizer ⧸ pCore 2 centralizer) ⧸
      pPrimeCore 2 (centralizer ⧸ pCore 2 centralizer)) := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let quotient := QuotientGroup.mk' (pCore 2 centralizer)
  let oddCore := pPrimeCore 2 (centralizer ⧸ pCore 2 centralizer)
  let actor := first.E.map (MulAut.conj config.g⁻¹).toMonoidHom
  change ¬ IsPGroup 2 ((centralizer ⧸ pCore 2 centralizer) ⧸ oddCore)
  intro hsmall
  have hactor : actor.map embedding ≤ centralizer :=
    le_sup_left.trans (nine_three_normalized_pair_centralizer ctx hb hlarge
      first second config).2
  let oddQuotient := (QuotientGroup.mk' oddCore).comp quotient
  have hp : IsPGroup 2 (centralizer ⧸ oddQuotient.ker) :=
    (hsmall.to_subgroup oddQuotient.range).of_equiv
      (QuotientGroup.quotientKerEquivRange oddQuotient).symm
  have hres := residual_image_le_of_two_group_quotient embedding actor centralizer
    hactor oddQuotient.ker hp
  apply nine_three_mixed_centralizer_residual_not_le ctx hb hlarge first second config
  rintro element ⟨member, hmember, rfl⟩
  have hzero := hres hmember
  exact (QuotientGroup.eq_one_iff (N := oddCore) (quotient member)).mp hzero

public theorem nine_three_final_core_quotient_sylow_card_gt_two
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    ∀ sylow : Sylow 2 (centralizer ⧸ pCore 2 centralizer), 2 < Nat.card sylow := by
  dsimp only
  intro sylow
  by_contra hsmall
  have hcomplement := normal_two_complement_of_sylow_card_le_two sylow
    (Nat.le_of_not_gt hsmall)
  exact nine_three_final_odd_core_quotient_not_two_group ctx hb hlarge first second config
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 _ hcomplement)


end Stellmacher.SectionNine
