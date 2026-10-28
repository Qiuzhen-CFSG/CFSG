module

public import Stellmacher.SectionNine.EmbeddedOrderTwoVertex
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Stellmacher.SectionNine.NineSevenCommutatorGeometry

/-!
# Centralizer-core control for the large-distance branch of (9.7)

Order-two vertex centers give residual subnormality in the full ambient
centralizer. Injectivity pulls this back to the graph centralizer. The
ambient Sylow equality also supplies an actual Sylow of the graph group,
so the characteristic centralizer core lies in the local vertex core.

Applied to the genuine commutator witnesses, these facts give
O₂(E_rho) ≤ O₂(C_G(R)) ≤ Q_rho' ≤ G_penultimate and invariance of the
penultimate neighborhood join. This is the opening core-control step, not
the subsequent transport of U or the final normality contradiction.

Source: Stellmacher, printed p.54 / PDF p.44, first paragraph,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem centralizer_map_comap
    {G H : Type*} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (subgroup : Subgroup G) :
    (Subgroup.centralizer (subgroup.map embedding : Set H)).comap embedding =
      Subgroup.centralizer (subgroup : Set G) := by
  ext element
  change embedding element ∈ Subgroup.centralizer (subgroup.map embedding : Set H) ↔ _
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h member hmember
    apply hinjective
    simpa using h (embedding member) ⟨member, hmember, rfl⟩
  · intro h member hmember
    obtain ⟨preimage, hpreimage, rfl⟩ := hmember
    simpa using congrArg embedding (h preimage hpreimage)

private theorem subnormalIn_pullback
    {G H : Type*} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (subgroup : Subgroup G) (ambient : Subgroup H)
    (hsub : SubnormalIn (subgroup.map embedding) ambient) :
    SubnormalIn subgroup (ambient.comap embedding) := by
  refine ⟨fun element helement => hsub.1 ⟨element, helement, rfl⟩, ?_⟩
  let restricted : ambient.comap embedding →* ambient :=
    (embedding.comp (ambient.comap embedding).subtype).codRestrict ambient
      (fun element => element.property)
  have hpull := hsub.2.comap restricted
  have heq : ((subgroup.map embedding).subgroupOf ambient).comap restricted =
      subgroup.subgroupOf (ambient.comap embedding) := by
    ext element
    change embedding element.val ∈ subgroup.map embedding ↔ element.val ∈ subgroup
    constructor
    · rintro ⟨preimage, hpreimage, heq⟩
      exact hinjective heq ▸ hpreimage
    · intro hmem
      exact ⟨element.val, hmem, rfl⟩
  rwa [heq] at hpull

public theorem nine_seven_ambient_centralizer_core_pullback
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (subgroup : Subgroup G) :
    (twoCoreIn (Subgroup.centralizer (subgroup.map embedding : Set H))).comap embedding ≤
      twoCoreIn (Subgroup.centralizer (subgroup : Set G)) := by
  let ambient := Subgroup.centralizer (subgroup.map embedding : Set H)
  let graphCentralizer := Subgroup.centralizer (subgroup : Set G)
  let pulled := (twoCoreIn ambient).comap embedding
  have hcentral : ambient.comap embedding = graphCentralizer :=
    centralizer_map_comap embedding hinjective subgroup
  have hpulled : pulled ≤ graphCentralizer := by
    rw [← hcentral]
    exact Subgroup.comap_mono (twoCoreIn_le ambient)
  have hnormal : (pulled.subgroupOf graphCentralizer).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hpulled).mpr
    intro element actor helement hactor
    change embedding (actor * element * actor⁻¹) ∈ twoCoreIn ambient
    rw [map_mul, map_mul, map_inv]
    apply (Subgroup.normal_subgroupOf_iff (twoCoreIn_le ambient)).mp
      (twoCoreIn_normal ambient) (embedding element) (embedding actor) helement
    change actor ∈ ambient.comap embedding
    rwa [hcentral]
  have htwo : IsPGroup 2 pulled :=
    ((pCore_isPGroup (G := ambient) (p := 2)).map ambient.subtype).comap_of_injective
      embedding hinjective
  exact isPGroup_le_pCoreAmbient_of_isSubnormalIn graphCentralizer pulled 2 hpulled
    hnormal.isSubnormal htwo

public theorem nine_seven_vertex_centralizer_core_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (sylow : Sylow 2 G) (hglobal : T = (sylow : Subgroup G))
    (vertex : Γ.Vertex) :
    twoCoreIn (Subgroup.centralizer (ZAt Γ vertex : Set G)) ≤ QAt Γ vertex := by
  let centralizer := Subgroup.centralizer (ZAt Γ vertex : Set G)
  let core := twoCoreIn centralizer
  have hNcore : Subgroup.normalizer (centralizer : Set G) ≤
      Subgroup.normalizer (core : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor element helement
    obtain ⟨inner, hinner, rfl⟩ := helement
    let normalizerActor : Subgroup.normalizer (centralizer : Set G) := ⟨actor, hactor⟩
    let aut := Subgroup.normalizerMonoidHom centralizer normalizerActor
    have hfix : (pCore 2 centralizer).comap aut.toMonoidHom = pCore 2 centralizer :=
      (inferInstance : (pCore 2 centralizer).Characteristic).fixed aut
    have himage : aut inner ∈ pCore 2 centralizer := by
      change inner ∈ (pCore 2 centralizer).comap aut.toMonoidHom
      rwa [hfix]
    exact ⟨aut inner, himage, by
      simp [aut, normalizerActor, mul_assoc,
        Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  have hNC : Subgroup.normalizer (ZAt Γ vertex : Set G) ≤
      Subgroup.normalizer (centralizer : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (ZAt Γ vertex : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hGcore : GAt Γ vertex ≤ Subgroup.normalizer (core : Set G) :=
    (stabilizer_le_normalizer_z Γ vertex).trans (hNC.trans hNcore)
  have hSyl : ∃ localSylow : Sylow 2 G,
      (localSylow : Subgroup G) ≤ GAt Γ vertex := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one h Γ).vertex_stabilizers_conjugate vertex
    let localSylow := sylow.mapSurjective (f := (MulAut.conj actor).toMonoidHom)
      (MulAut.conj actor).surjective
    refine ⟨localSylow, ?_⟩
    change (sylow : Subgroup G).map (MulAut.conj actor).toMonoidHom ≤ stabilizer Γ vertex
    rw [← hglobal]
    rcases hactor with hactor | hactor
    · rw [hactor]
      exact Subgroup.map_mono h.P1_mem.1.2.1.1
    · rw [hactor]
      exact Subgroup.map_mono h.P2_mem.1.2.1.1
  obtain ⟨localSylow, hlocal⟩ := hSyl
  have hcoreP : IsPGroup 2 core := (pCore_isPGroup (G := centralizer) (p := 2)).map _
  have hcoreSylow : core ≤ (localSylow : Subgroup G) := by
    have heq := localSylow.is_maximal'
      (localSylow.isPGroup'.to_sup_of_normal_right' hcoreP (hlocal.trans hGcore))
      le_sup_left
    exact le_sup_right.trans heq.le
  have hcoreG : core ≤ GAt Γ vertex := hcoreSylow.trans hlocal
  have hnormal : (core.subgroupOf (GAt Γ vertex)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreG).mpr hGcore
  have hcorePG : IsPGroup 2 (core.subgroupOf (GAt Γ vertex)) :=
    hcoreP.of_equiv (Subgroup.subgroupOfEquivOfLe hcoreG).symm
  have hcore : core.subgroupOf (GAt Γ vertex) ≤ pCore 2 (GAt Γ vertex) :=
    le_sSup ⟨hnormal, hcorePG⟩
  have hmap := Subgroup.map_mono (f := (GAt Γ vertex).subtype) hcore
  rw [Subgroup.map_subgroupOf_eq_of_le hcoreG] at hmap
  exact hmap.trans_eq (Γ.twoCoreAt_def vertex).symm

public theorem nine_seven_order_two_centralizer_core_control
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex) (hcard : Nat.card (ZAt ctx.Γ vertex) = 2) :
    SubnormalIn (EAt ctx.Γ vertex)
        (Subgroup.centralizer (ZAt ctx.Γ vertex : Set G)) ∧
      twoCoreIn (EAt ctx.Γ vertex) ≤
        twoCoreIn (Subgroup.centralizer (ZAt ctx.Γ vertex : Set G)) ∧
      twoCoreIn (Subgroup.centralizer (ZAt ctx.Γ vertex : Set G)) ≤
        QAt ctx.Γ vertex := by
  obtain ⟨hglobal, hsub, _⟩ := embedded_orderTwoVertex_residual_subnormal ctx vertex hcard
  have hlocal := subnormalIn_pullback embedding ctx.embedding_injective _ _ hsub
  rw [centralizer_map_comap embedding ctx.embedding_injective] at hlocal
  refine ⟨hlocal, pCoreAmbient_mono_of_isSubnormalIn _ _ 2 hlocal.1 hlocal.2, ?_⟩
  have hrange : (S0 : Subgroup H) ≤ embedding.range := by
    rw [← hglobal, ← ctx.map_S]
    exact Subgroup.map_le_range embedding T
  let sylow := S0.comapOfInjective embedding ctx.embedding_injective hrange
  have hsylow : T = (sylow : Subgroup G) := by
    change T = (S0 : Subgroup H).comap embedding
    rw [← hglobal, ← ctx.map_S,
      Subgroup.comap_map_eq_self_of_injective ctx.embedding_injective]
  exact nine_seven_vertex_centralizer_core_le ctx.sectionSeven ctx.Γ sylow hsylow vertex

public theorem nine_seven_stabilizer_normalizes_neighborhood
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (vertex : Γ.Vertex) :
    GAt Γ vertex ≤ Subgroup.normalizer (GeneratedNeighborhoodV Γ vertex : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hmap : (GeneratedNeighborhoodV Γ vertex).map (MulAut.conj actor).toMonoidHom ≤
      GeneratedNeighborhoodV Γ vertex := by
    rw [Subgroup.map_le_iff_le_comap, GeneratedNeighborhoodV]
    apply sSup_le
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩
    apply Subgroup.map_le_iff_le_comap.mp
    have htransport := v_act Γ actor⁻¹ neighbor
    simp only [inv_inv] at htransport
    change (v Γ neighbor).map (MulAut.conj actor).toMonoidHom ≤ _
    rw [← htransport]
    apply le_sSup
    refine ⟨Γ.act actor⁻¹ neighbor, ?_, rfl⟩
    have hadj := adjacent_act Γ actor⁻¹
      ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
    have hfix : Γ.act actor⁻¹ vertex = vertex :=
      (Set.ext_iff.mp (Γ.stabilizer_def vertex) actor⁻¹).mp
        ((GAt Γ vertex).inv_mem hactor)
    rw [hfix] at hadj
    exact (mem_neighborhood_iff_adjacent Γ).mpr hadj
  exact hmap ⟨element, helement, rfl⟩

public theorem nine_seven_commutator_centralizer_core_control
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^3)
    (hendModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hlong : 3 < ctx.criticalPath.length) :
    let Γ := ctx.Γ
    let cp := ctx.criticalPath
    let second := cp.path ⟨2, by dsimp [cp]; omega⟩
    let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
    let R := ⁅VAt Γ cp.a', ZAt Γ cp.a⁆
    let centralizer := Subgroup.centralizer (R : Set G)
    let core := twoCoreIn centralizer
    (∃ rho, rho ∈ Neighborhood Γ second ∧ R = ZAt Γ rho ∧
      SubnormalIn (EAt Γ rho) centralizer ∧ twoCoreIn (EAt Γ rho) ≤ core) ∧
      (∃ rho', rho' ∈ Neighborhood Γ penultimate ∧ R = ZAt Γ rho' ∧
        core ≤ QAt Γ rho' ∧ QAt Γ rho' ≤ GAt Γ penultimate) ∧
      core ≤ GAt Γ penultimate ∧
      core ≤ Subgroup.normalizer (GeneratedNeighborhoodV Γ penultimate : Set G) := by
  dsimp only
  obtain ⟨hcard, _, _, ⟨rho, hrho, hRrho⟩, ⟨other, hother, hRother⟩, _⟩ :=
    nine_seven_commutator_geometry ctx hb third hpath hindex hfirstCard hfirstModel
      hendCard hendModel hstartData hlong
  have hleft := nine_seven_order_two_centralizer_core_control ctx rho
    (by rwa [← hRrho])
  have hright := nine_seven_order_two_centralizer_core_control ctx other
    (by rwa [← hRother])
  rw [← hRrho] at hleft
  rw [← hRother] at hright
  have hreverse : ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩ ∈
      Neighborhood ctx.Γ other :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hother))
  have hcoreG := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
    other _ hreverse default).2.2
  exact ⟨⟨rho, hrho, hRrho, hleft.1, hleft.2.1⟩,
    ⟨other, hother, hRother, hright.2.2, hcoreG⟩,
    hright.2.2.trans hcoreG,
    (hright.2.2.trans hcoreG).trans (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ _)⟩

end Stellmacher.SectionNine

