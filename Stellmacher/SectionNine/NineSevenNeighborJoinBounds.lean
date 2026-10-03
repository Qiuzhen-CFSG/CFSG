module

public import Stellmacher.SectionNine.NineSevenCentralizerCore
public import Theory.GroupTheory.PGroup.SubnormalConjugateCore
public import Stellmacher.SectionThree.SubnormalOddQuotient

/-!
# Core comparison and bounded-distance assembly for (9.7)

These helpers justify comparison modulo the genuine graph centralizer core
without identifying that core with the pullback of the full ambient core.
The ambient comparison is factored through a normal subgroup product and
the proved containment of the ambient core pullback in the graph core.
The intrinsic odd-prime quotient of a vertex residual follows from the
actual Section Three edge data, not from an additional quotient hypothesis.

The distance lemma bounds a neighborhood join by a core when its center
generators are strictly closer than the critical distance. The final join
assembly is conditional on nearby bounds; it does not establish the missing
geometric contractions or the principal penultimate-transport theorem.

Source: Stellmacher, printed p.54 / PDF p.44, first paragraph,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise

universe u

public theorem nine_seven_adjacent_distance_bound
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (left middle right : Γ.Vertex)
    (hadjacent : Γ.adjacent left middle) :
    Γ.distance left right ≤ Γ.distance middle right + 1 := by
  obtain ⟨tail, hstart, hend, hadj⟩ := Γ.distance_path middle right
  let path : Fin (Γ.distance middle right + 1 + 1) → Γ.Vertex := Fin.cases left tail
  have hpath : ∀ step : Fin (Γ.distance middle right + 1),
      Γ.adjacent (path step.castSucc) (path step.succ) := by
    intro step
    refine Fin.cases ?_ (fun next => ?_) step
    · change Γ.adjacent left (tail 0)
      rwa [hstart]
    · simpa [path] using hadj next
  have hbound := Γ.distance_le_of_path (Γ.distance middle right + 1) path hpath
  have hlast : path ⟨Γ.distance middle right + 1, Nat.lt_succ_self _⟩ = right := hend
  simpa only [show path 0 = left from rfl, hlast] using hbound

public theorem nine_seven_neighborhood_le_core_of_distance
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (source target : Γ.Vertex) (hdistance : Γ.distance source target + 2 < cp.length) :
    GeneratedNeighborhoodV Γ source ≤ QAt Γ target := by
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  change v Γ neighbor ≤ q Γ target
  rw [v, Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨outer, houter, rfl⟩
  have hfirst := nine_seven_adjacent_distance_bound Γ neighbor source target
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
  have hsecond := nine_seven_adjacent_distance_bound Γ outer neighbor target
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp houter))
  exact critical_minimality Γ cp (by omega)

public theorem nine_seven_map_join_core_pullback
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (commutator source target : Subgroup G)
    (htarget : target ≤ Subgroup.centralizer (commutator : Set G))
    (hbound : source.map embedding ≤ target.map embedding ⊔
      twoCoreIn (Subgroup.centralizer (commutator.map embedding : Set H))) :
    source ≤ target ⊔ twoCoreIn (Subgroup.centralizer (commutator : Set G)) := by
  let ambient := Subgroup.centralizer (commutator.map embedding : Set H)
  let core := twoCoreIn ambient
  have htargetAmbient : target.map embedding ≤ ambient := by
    rintro element ⟨preimage, hpreimage, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro element ⟨other, hother, rfl⟩
    simpa only [map_mul] using congrArg embedding
      ((Subgroup.mem_centralizer_iff.mp (htarget hpreimage)) other hother)
  have hnormal : NormalIn core ambient := ⟨twoCoreIn_le ambient, twoCoreIn_normal ambient⟩
  have hnormalize : target.map embedding ≤ Subgroup.normalizer (core : Set H) :=
    htargetAmbient.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2)
  intro element helement
  have hmem := hbound (Subgroup.mem_map_of_mem embedding helement)
  change embedding element ∈ (target.map embedding ⊔ core : Subgroup H) at hmem
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormalize] at hmem
  obtain ⟨image, ⟨preimage, hpreimage, rfl⟩, remainder, hremainder, hproduct⟩ := hmem
  have hrem : embedding (preimage⁻¹ * element) = remainder := by
    rw [map_mul, map_inv, ← hproduct, inv_mul_cancel_left]
  have hcore : preimage⁻¹ * element ∈
      (twoCoreIn ambient).comap embedding := by
    change embedding (preimage⁻¹ * element) ∈ core
    rwa [hrem]
  have hpull := nine_seven_ambient_centralizer_core_pullback embedding hinjective commutator hcore
  have hmul := (target ⊔ twoCoreIn (Subgroup.centralizer (commutator : Set G))).mul_mem
    (Subgroup.mem_sup_left hpreimage) (Subgroup.mem_sup_right hpull)
  simpa only [mul_inv_cancel_left] using hmul

public theorem nine_seven_neighbor_join_le_of_nearby_bounds
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (target : Γ.Vertex) (core : Subgroup G) (hcore : core ≤ GAt Γ target)
    (hnearby : ∀ neighbor, neighbor ∈ Neighborhood Γ cp.a →
      ∃ nearby, GeneratedNeighborhoodV Γ neighbor ≤ core ⊔ GeneratedNeighborhoodV Γ nearby ∧
        Γ.distance nearby target + 2 < cp.length) :
    sSup {subgroup : Subgroup G | ∃ neighbor, neighbor ∈ Neighborhood Γ cp.a ∧
      subgroup = GeneratedNeighborhoodV Γ neighbor} ≤ GAt Γ target := by
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  obtain ⟨nearby, hbound, hdistance⟩ := hnearby neighbor hneighbor
  apply hbound.trans (sup_le hcore _)
  have hnearbyCore := nine_seven_neighborhood_le_core_of_distance Γ cp nearby target hdistance
  have hcoreGroup : QAt Γ target ≤ GAt Γ target := by
    rw [show QAt Γ target = twoCoreIn (GAt Γ target) from Γ.twoCoreAt_def target]
    exact twoCoreIn_le _
  exact hnearbyCore.trans hcoreGroup

public theorem nine_seven_vertex_residual_odd_quotient
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (hypotheses : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (vertex neighbor : Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood Γ vertex) :
    ∃ prime : ℕ, prime.Prime ∧ prime ≠ 2 ∧
      IsPGroup prime (EAt Γ vertex ⧸ pCore 2 (EAt Γ vertex)) := by
  have hdata := edge_sectionThree_data hypotheses Γ hneighbor default
  have hsubnormal : IsSubnormalIn (twoResidualAmbient (GAt Γ vertex))
      (twoResidualAmbient (GAt Γ vertex)) := by
    refine ⟨le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    exact (inferInstance : (⊤ : Subgroup (twoResidualAmbient (GAt Γ vertex))).Normal).isSubnormal
  have hquotient := SectionThree.subnormal_quotient_twoCore_is_odd_pGroup _
    hdata.1 _ hdata.2.1 hdata.2.2.2.1 _ hsubnormal
  change ∃ prime : ℕ, prime.Prime ∧ prime ≠ 2 ∧
    IsPGroup prime (e Γ vertex ⧸ pCore 2 (e Γ vertex))
  rw [CosetGraphContext.e, Γ.twoResidualAt_def]
  exact hquotient

public theorem nine_seven_order_two_residual_conjugate_bound
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex) (hcard : Nat.card (ZAt ctx.Γ vertex) = 2)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood ctx.Γ vertex)
    (common source : Subgroup G)
    (hcentral : common ≤ Subgroup.centralizer (ZAt ctx.Γ vertex : Set G))
    (hcommon : IsPGroup 2 common) (hsource : source ≤ common)
    (actor : G) (hactor : actor ∈ EAt ctx.Γ vertex)
    (hconjugate : source.conjBy actor ≤ common) :
    source ≤ source.conjBy actor ⊔
      twoCoreIn (Subgroup.centralizer (ZAt ctx.Γ vertex : Set G)) := by
  obtain ⟨_, hsubnormal, _⟩ := embedded_orderTwoVertex_residual_subnormal ctx vertex hcard
  obtain ⟨prime, hprimePrime, hprime, hquotient⟩ :=
    nine_seven_vertex_residual_odd_quotient ctx.sectionSeven ctx.Γ vertex neighbor hneighbor
  let _ : Fact prime.Prime := ⟨hprimePrime⟩
  let residual := EAt ctx.Γ vertex
  let ambient := Subgroup.centralizer ((ZAt ctx.Γ vertex).map embedding : Set H)
  let equiv := residual.equivMapOfInjective embedding ctx.embedding_injective
  let quotientEquiv := QuotientGroup.congr _ _ equiv (pCore_map_iso 2 equiv)
  have hquotientImage : IsPGroup prime
      (residual.map embedding ⧸ pCore 2 (residual.map embedding)) :=
    hquotient.of_equiv quotientEquiv
  have hcommonAmbient : common.map embedding ≤ ambient := by
    rintro element ⟨preimage, hpreimage, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro element ⟨other, hother, rfl⟩
    simpa only [map_mul] using congrArg embedding
      ((Subgroup.mem_centralizer_iff.mp (hcentral hpreimage)) other hother)
  have hconjugateImage : (source.map embedding).conjBy (embedding actor) =
      (source.conjBy actor).map embedding := by
    change (source.map embedding).map (MulAut.conj (embedding actor)).toMonoidHom =
      (source.map (MulAut.conj actor).toMonoidHom).map embedding
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext element
    simp [MulAut.conj_apply]
  have hbound := subnormal_conjugate_le_sup_pCore_in prime 2 hprime ambient
    (residual.map embedding) hsubnormal.1 hsubnormal.2 hquotientImage
    (common.map embedding) (source.map embedding) hcommonAmbient
    (hcommon.map embedding) (Subgroup.map_mono hsource) (embedding actor)
    (Subgroup.mem_map_of_mem embedding hactor)
    (hconjugateImage ▸ Subgroup.map_mono hconjugate)
  rw [hconjugateImage] at hbound
  exact nine_seven_map_join_core_pullback embedding ctx.embedding_injective _ _ _
    (hconjugate.trans hcentral) hbound

end Stellmacher.SectionNine
