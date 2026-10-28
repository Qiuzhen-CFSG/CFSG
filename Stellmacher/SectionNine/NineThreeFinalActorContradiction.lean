module
public import Stellmacher.SectionNine.NineThreeFinalCoreQuotientObstruction
public import Stellmacher.SectionNine.NineThreeFinalCentralizerSetup

/-!
# The final prescribed-actor contradiction in (9.3)

If the initial center maps into the two-core after quotienting the actual
mixed centralizer by its two-core and then its odd core, the first extracted
group has two-group image in that final quotient. Its exact generation
uses one prescribed actor from the initial center and a conjugate two-subgroup.
Their images lie in a product of the normal two-core with a two-subgroup.
Thus the extracted two-residual maps trivially and lies in the odd-core
layer, contrary to the geometric first-residual exclusion.

This common implication is used both to exclude an order-eight intersection
with the final core and to finish the faithful transvection-action argument.
It retains the original ambient group, embedding, residual and actor.
Source: Stellmacher (9.3), printed p.50/PDF p.40, the final R₀,C₀ paragraph
of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem nine_three_final_contradiction_of_initial_center_oddCoreLayer
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
    let C := Subgroup.centralizer (mixed.map embedding : Set H)
    let core := pCore 2 C
    let q := QuotientGroup.mk' core
    let Y := (((ZAt ctx.Γ ctx.criticalPath.a).map embedding).subgroupOf C).map q
    Y.map (QuotientGroup.mk' (pPrimeCore 2 (C ⧸ core))) ≤
      pCore 2 ((C ⧸ core) ⧸ pPrimeCore 2 (C ⧸ core)) → False := by
  classical
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let C := Subgroup.centralizer (mixed.map embedding : Set H)
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  let internal := vectors.subgroupOf C
  let core := pCore 2 C
  let q := QuotientGroup.mk' core
  let r := QuotientGroup.mk' (pPrimeCore 2 (C ⧸ core))
  let projection := r.comp q
  change (internal.map q).map r ≤ pCore 2 ((C ⧸ core) ⧸ pPrimeCore 2 (C ⧸ core)) → False
  intro hbound
  have hdata := nine_three_final_centralizer_center_core ctx hb hlarge first second config
  let E := first.E.map (MulAut.conj config.g⁻¹).toMonoidHom
  let A0 := (VAt ctx.Γ ctx.criticalPath.firstStep).conjBy config.first_geometry.x
  let image := (E.map embedding).subgroupOf C
  let imageA := (A0.map embedding).subgroupOf C
  have hEC : E.map embedding ≤ C :=
    le_sup_left.trans (nine_three_normalized_pair_centralizer
      ctx hb hlarge first second config).2
  have hA0E : A0 ≤ E := by
    change A0 ≤ first.E.map (MulAut.conj config.g⁻¹).toMonoidHom
    rw [config.first_geometry.generated]
    exact le_sup_right
  have hA0C : A0.map embedding ≤ C := (Subgroup.map_mono hA0E).trans hEC
  have hactorC : embedding config.first_actor ∈ C :=
    hdata.1 (Subgroup.mem_map_of_mem embedding config.first_actor_initial)
  let actor : C := ⟨embedding config.first_actor, hactorC⟩
  have hactorCore : projection actor ∈ pCore 2 ((C ⧸ core) ⧸ pPrimeCore 2 (C ⧸ core)) := by
    apply hbound
    apply Subgroup.mem_map_of_mem r
    apply Subgroup.mem_map_of_mem q
    exact Subgroup.mem_map_of_mem embedding config.first_actor_initial
  have hAp : IsPGroup 2 A0 := by
    have hp := (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.2.1.isPGroup
    exact hp.map (MulAut.conj config.first_geometry.x).toMonoidHom
  have himageAp : IsPGroup 2 (imageA.map projection) :=
    ((hAp.map embedding).of_equiv (Subgroup.subgroupOfEquivOfLe hA0C).symm).map projection
  let container := pCore 2 ((C ⧸ core) ⧸ pPrimeCore 2 (C ⧸ core)) ⊔ imageA.map projection
  have hcontainer : IsPGroup 2 container :=
    pCore_isPGroup.to_sup_of_normal_left himageAp
  have hactorV : config.first_actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep := by
    apply ((lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1)
    exact config.first_actor_initial
  have hgen : E = Subgroup.closure ({config.first_actor} : Set G) ⊔ A0 :=
    config.first_geometry.actor_generated config.first_actor hactorV config.first_geometry.actor_outside
  have hEcontainer : E.map embedding ≤ (container.comap projection).map C.subtype := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [hgen]
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro element helement
      have heq : element = config.first_actor := Set.mem_singleton_iff.mp helement
      subst element
      exact Subgroup.mem_map_of_mem C.subtype (show actor ∈ container.comap projection from
        (show pCore 2 ((C ⧸ core) ⧸ pPrimeCore 2 (C ⧸ core)) ≤ container from le_sup_left) hactorCore)
    · intro element helement
      exact Subgroup.mem_map_of_mem C.subtype
        (show (⟨embedding element, hA0C (Subgroup.mem_map_of_mem embedding helement)⟩ : C) ∈
          container.comap projection from
          (show imageA.map projection ≤ container from le_sup_right)
            (Subgroup.mem_map_of_mem projection (Subgroup.mem_map_of_mem embedding helement)))
  have himageLe : image.map projection ≤ container := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hEC]
    exact hEcontainer
  let inclusion : E →* C := (embedding.comp E.subtype).codRestrict C (by
    intro element
    exact hEC (Subgroup.mem_map_of_mem embedding element.property))
  let f := projection.comp inclusion
  have hrange : IsPGroup 2 f.range := hcontainer.to_le (by
    rintro _ ⟨element, rfl⟩
    apply himageLe
    exact Subgroup.mem_map_of_mem projection (Subgroup.mem_map_of_mem embedding element.property))
  have hquotient : IsPGroup 2 (E ⧸ f.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hresidual : twoResidualSubgroup E ≤ f.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_le f.ker inferInstance hquotient
  apply nine_three_mixed_centralizer_residual_not_le ctx hb hlarge first second config
  rintro _ ⟨element, helement, rfl⟩
  obtain ⟨original, horiginal, heq⟩ := helement
  obtain ⟨member, hmember, rfl⟩ := horiginal
  have hzero := hresidual hmember
  change projection (inclusion member) = 1 at hzero
  have heq' : inclusion member = element := Subtype.ext heq
  rw [heq'] at hzero
  exact (QuotientGroup.eq_one_iff (N := pPrimeCore 2 (C ⧸ core)) (q element)).mp hzero

end Stellmacher.SectionNine
