module

public import Stellmacher.SectionNine.NineSevenCubicFamilyKernel
public import Stellmacher.SectionNine.NineSevenSourceOddW

/-!
# Core forcing from the two initial commutator bounds

The source's two possible commutator containments each normalize every
neighboring member of a natural vertex family. The cubic-family kernel
then places all actors in the initial core. The V-family uses the common
initial center; the odd-W family uses the common initial W. Critical
minimality places the vertex families in their own two-cores. The initial
center is nontrivial by criticality and is contained in each neighboring
family member. The statements retain the actor subgroup's containment in
the initial stabilizer, which is essential for the cubic kernel argument.

Source: Stellmacher (9.7), printed p.54 / PDF p.44, the two normality
consequences when the terminal module lies in the first-step core. The
odd-W statement uses the explicit two-step-walk construction defined in
`NineSevenSourceOddW`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

variable {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}

private theorem initial_center_ne_bot (ctx : SectionNineLocalContext G T A B) :
    ZAt ctx.Γ ctx.criticalPath.a ≠ ⊥ := by
  intro hbot
  apply ctx.criticalPath.critical.2
  change ZAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.a'
  rw [hbot]
  exact bot_le

public theorem nine_seven_neighborhood_commutator_forces_core
    (ctx : SectionNineLocalContext G T A B) (hb : 1 < ctx.criticalPath.length)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (actors : Subgroup G) (hactors : actors ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, actors⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a) :
    actors ≤ QAt ctx.Γ ctx.criticalPath.a := by
  apply nine_seven_cubic_family_kernel ctx.sectionSeven ctx.Γ ctx.criticalPath.a hmodel
    (VAt ctx.Γ) (v_act ctx.Γ) (stabilizer_le_normalizer_v ctx.Γ) ?_ ?_
    actors hactors ?_
  · intro point _
    exact nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ point _
      (nine_seven_module_le_own_core ctx hb point)
  · intro point hpoint hbot
    apply initial_center_ne_bot ctx
    exact le_bot_iff.mp (hbot ▸ nine_seven_neighbor_center_le_module ctx.Γ
      (ctx.Γ.adjacent_symm hpoint))
  · intro point hpoint
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact ((Subgroup.commutator_mono
      (nine_seven_neighbor_module_le_neighborhood ctx.Γ hpoint) le_rfl).trans hcomm).trans
        (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hpoint))

private theorem own_stabilizer_normalizes_odd_w
    (Gamma : CosetGraphContext G T A B) (vertex : Gamma.Vertex) :
    GAt Gamma vertex ≤ Subgroup.normalizer (SourceOddW Gamma vertex : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hfix : Gamma.act actor⁻¹ vertex = vertex :=
    (Set.ext_iff.mp (Gamma.stabilizer_def vertex) actor⁻¹).mp
      ((GAt Gamma vertex).inv_mem hactor)
  have hact := sourceOddW_act Gamma actor⁻¹ vertex
  simp only [inv_inv, hfix] at hact
  exact hact.symm ▸ Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom helement

private theorem initial_w_le_neighbor_odd_w
    (Gamma : CosetGraphContext G T A B) {vertex neighbor : Gamma.Vertex}
    (hadj : Gamma.adjacent vertex neighbor) :
    GeneratedNeighborhoodV Gamma vertex ≤ SourceOddW Gamma neighbor := by
  unfold GeneratedNeighborhoodV
  apply sSup_le
  rintro subgroup ⟨endpoint, hendpoint, rfl⟩
  exact le_sSup ⟨vertex,
    (mem_neighborhood_iff_adjacent Gamma).mpr (Gamma.adjacent_symm hadj),
    endpoint, hendpoint, rfl⟩

public theorem nine_seven_source_join_commutator_forces_core
    (ctx : SectionNineLocalContext G T A B) (hb : 3 < ctx.criticalPath.length)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (actors : Subgroup G) (hactors : actors ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅SourceInitialOddJoin ctx.Γ ctx.criticalPath.a, actors⁆ ≤
      GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a) :
    actors ≤ QAt ctx.Γ ctx.criticalPath.a := by
  apply nine_seven_cubic_family_kernel ctx.sectionSeven ctx.Γ ctx.criticalPath.a hmodel
    (SourceOddW ctx.Γ) (sourceOddW_act ctx.Γ) (own_stabilizer_normalizes_odd_w ctx.Γ)
    ?_ ?_ actors hactors ?_
  · intro point _
    apply nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ point
    exact source_odd_w_le_core_of_distance ctx.Γ ctx.criticalPath point point
      (by simpa only [ctx.Γ.distance_refl, Nat.zero_add] using hb)
  · intro point hpoint hbot
    apply initial_center_ne_bot ctx
    have hZV := nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hpoint)
    have hVW := nine_seven_neighbor_module_le_neighborhood ctx.Γ hpoint
    have hWW := initial_w_le_neighbor_odd_w ctx.Γ hpoint
    exact le_bot_iff.mp (hbot ▸ ((hZV.trans hVW).trans hWW))
  · intro point hpoint
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    have hmember : SourceOddW ctx.Γ point ≤ SourceInitialOddJoin ctx.Γ ctx.criticalPath.a :=
      le_sSup ⟨point, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hpoint, rfl⟩
    exact ((Subgroup.commutator_mono hmember le_rfl).trans hcomm).trans
      (initial_w_le_neighbor_odd_w ctx.Γ hpoint)

end Stellmacher.SectionNine

