module

public import Stellmacher.SectionNine.NineSevenNormalityObstructions

/-!
# Source-correct first-step W joins for (9.7)

The printed proof of (9.7) uses a parity-sensitive `W_d`: on the first-step
orbit it is the join of the `V` groups at distance two from `d`. This leaf
uses the convenient two-step-walk enlargement, which also permits returning
to `d`; identification with the exact-distance join is a separate obligation.
The established `GeneratedNeighborhoodV` intentionally remains the
uniform one-step join used by the existing Section Nine API. This leaf adds
the source-specific odd-orbit construction without identifying it with that
uniform join.

Conjugation carries two-step walks to two-step walks and transports each
module by `v_act`; inverse conjugation gives equality. An element fixing the
initial vertex therefore normalizes the join of all first-step-orbit `W`s.
Expanding a `V` group into its neighboring centers gives the radius-three
core bound by critical minimality.
These are the structural inputs needed to state the normality portion of the
printed (9.7) argument faithfully. Source: Stellmacher (9.3), printed p.50,
and (9.7), printed p.54 / PDF pp.40, 44.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

@[expose] public noncomputable def SourceOddW
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (vertex : Gamma.Vertex) : Subgroup G :=
  sSup {subgroup : Subgroup G | ∃ middle, middle ∈ Neighborhood Gamma vertex ∧
    ∃ endpoint, endpoint ∈ Neighborhood Gamma middle ∧ subgroup = VAt Gamma endpoint}

@[expose] public noncomputable def SourceInitialOddJoin
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (vertex : Gamma.Vertex) : Subgroup G :=
  sSup {subgroup : Subgroup G | ∃ neighbor, neighbor ∈ Neighborhood Gamma vertex ∧
    subgroup = SourceOddW Gamma neighbor}

private theorem sourceOddW_act_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (actor : G) (vertex : Gamma.Vertex) :
    (SourceOddW Gamma vertex).map (MulAut.conj actor⁻¹).toMonoidHom ≤
      SourceOddW Gamma (Gamma.act actor vertex) := by
  rw [Subgroup.map_le_iff_le_comap, SourceOddW]
  apply sSup_le
  rintro subgroup ⟨middle, hmiddle, endpoint, hendpoint, rfl⟩
  apply Subgroup.map_le_iff_le_comap.mp
  rw [← v_act]
  apply le_sSup
  refine ⟨Gamma.act actor middle, ?_, Gamma.act actor endpoint, ?_, rfl⟩
  · exact (mem_neighborhood_iff_adjacent Gamma).mpr
      (adjacent_act Gamma actor ((mem_neighborhood_iff_adjacent Gamma).mp hmiddle))
  · exact (mem_neighborhood_iff_adjacent Gamma).mpr
      (adjacent_act Gamma actor ((mem_neighborhood_iff_adjacent Gamma).mp hendpoint))

public theorem sourceOddW_act
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (actor : G) (vertex : Gamma.Vertex) :
    SourceOddW Gamma (Gamma.act actor vertex) =
      (SourceOddW Gamma vertex).map (MulAut.conj actor⁻¹).toMonoidHom := by
  apply le_antisymm ?_ (sourceOddW_act_le Gamma actor vertex)
  have hback := Subgroup.map_mono (f := (MulAut.conj actor⁻¹).toMonoidHom)
    (sourceOddW_act_le Gamma actor⁻¹ (Gamma.act actor vertex))
  have hcomp : (MulAut.conj actor⁻¹).toMonoidHom.comp
      (MulAut.conj actor).toMonoidHom = MonoidHom.id G := by
    ext element
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [← Gamma.act_mul, mul_inv_cancel, Gamma.act_one, inv_inv,
    Subgroup.map_map, hcomp, Subgroup.map_id] using hback

private theorem sourceInitialOddJoin_act_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (actor : G) (vertex : Gamma.Vertex) :
    (SourceInitialOddJoin Gamma vertex).map (MulAut.conj actor⁻¹).toMonoidHom ≤
      SourceInitialOddJoin Gamma (Gamma.act actor vertex) := by
  rw [Subgroup.map_le_iff_le_comap, SourceInitialOddJoin]
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  apply Subgroup.map_le_iff_le_comap.mp
  rw [← sourceOddW_act]
  apply le_sSup
  refine ⟨Gamma.act actor neighbor, ?_, rfl⟩
  exact (mem_neighborhood_iff_adjacent Gamma).mpr
    (adjacent_act Gamma actor ((mem_neighborhood_iff_adjacent Gamma).mp hneighbor))

public theorem source_initial_odd_join_act
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (actor : G) (vertex : Gamma.Vertex) :
    SourceInitialOddJoin Gamma (Gamma.act actor vertex) =
      (SourceInitialOddJoin Gamma vertex).map (MulAut.conj actor⁻¹).toMonoidHom := by
  apply le_antisymm ?_ (sourceInitialOddJoin_act_le Gamma actor vertex)
  have hback := Subgroup.map_mono (f := (MulAut.conj actor⁻¹).toMonoidHom)
    (sourceInitialOddJoin_act_le Gamma actor⁻¹ (Gamma.act actor vertex))
  have hcomp : (MulAut.conj actor⁻¹).toMonoidHom.comp
      (MulAut.conj actor).toMonoidHom = MonoidHom.id G := by
    ext element
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [← Gamma.act_mul, mul_inv_cancel, Gamma.act_one, inv_inv,
    Subgroup.map_map, hcomp, Subgroup.map_id] using hback

/-- The initial stabilizer normalizes the source's join of first-step-orbit
two-step `W` groups. -/
public theorem stabilizer_normalizes_source_initial_odd_join
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (vertex : Gamma.Vertex) :
    GAt Gamma vertex ≤ Subgroup.normalizer (SourceInitialOddJoin Gamma vertex : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hfix : Gamma.act (actor : G)⁻¹ vertex = vertex :=
    (Set.ext_iff.mp (Gamma.stabilizer_def vertex) (actor : G)⁻¹).mp
      ((GAt Gamma vertex).inv_mem hactor)
  have hmap : (SourceInitialOddJoin Gamma vertex).map
      (MulAut.conj (actor : G)).toMonoidHom ≤ SourceInitialOddJoin Gamma vertex := by
    have hact := source_initial_odd_join_act Gamma (actor : G)⁻¹ vertex
    simp only [inv_inv] at hact
    rw [← hact, hfix]
  exact hmap ⟨element, helement, rfl⟩

private theorem adjacent_distance_bound
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (left middle right : Gamma.Vertex)
    (hadjacent : Gamma.adjacent left middle) :
    Gamma.distance left right ≤ Gamma.distance middle right + 1 := by
  obtain ⟨tail, hstart, hend, hadj⟩ := Gamma.distance_path middle right
  let path : Fin (Gamma.distance middle right + 1 + 1) → Gamma.Vertex :=
    Fin.cases left tail
  have hpath : ∀ step : Fin (Gamma.distance middle right + 1),
      Gamma.adjacent (path step.castSucc) (path step.succ) := by
    intro step
    refine Fin.cases ?_ (fun next => ?_) step
    · change Gamma.adjacent left (tail 0)
      rwa [hstart]
    · simpa [path] using hadj next
  have hbound := Gamma.distance_le_of_path (Gamma.distance middle right + 1) path hpath
  have hlast : path ⟨Gamma.distance middle right + 1,
      Nat.lt_succ_self _⟩ = right := hend
  simpa only [show path 0 = left from rfl, hlast] using hbound

public theorem source_odd_w_le_core_of_distance
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (cp : CriticalPath Gamma)
    (source target : Gamma.Vertex)
    (hdistance : Gamma.distance source target + 3 < cp.length) :
    SourceOddW Gamma source ≤ QAt Gamma target := by
  unfold SourceOddW
  apply sSup_le
  rintro subgroup ⟨middle, hmiddle, endpoint, hendpoint, rfl⟩
  change v Gamma endpoint ≤ _
  rw [v, Gamma.vAt_def]
  apply sSup_le
  rintro subgroup ⟨outer, houter, rfl⟩
  have hsourceMiddle := (mem_neighborhood_iff_adjacent Gamma).mp hmiddle
  have hmiddleEndpoint := (mem_neighborhood_iff_adjacent Gamma).mp hendpoint
  have hendpointOuter := (mem_neighborhood_iff_adjacent Gamma).mp houter
  have h₁ := adjacent_distance_bound Gamma middle source target
    (Gamma.adjacent_symm hsourceMiddle)
  have h₂ := adjacent_distance_bound Gamma endpoint middle target
    (Gamma.adjacent_symm hmiddleEndpoint)
  have h₃ := adjacent_distance_bound Gamma outer endpoint target
    (Gamma.adjacent_symm hendpointOuter)
  exact critical_minimality Gamma cp (by omega)

end Stellmacher.SectionNine
