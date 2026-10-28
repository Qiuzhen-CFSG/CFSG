module
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation

/-!
# Selecting a neighbor core from center centralization

A two-subgroup W in a vertex stabilizer that centralizes the center at an
initial-orbit neighbor lies in the two-core at some neighbor of that vertex.
The graph and commuting critical path are retained exactly; no ambient
Hypothesis Two or critical-length bound is needed in this selection step.

The common edge Sylow normalizes the relative center centralizer. Sylow
conjugacy inside a normalized subgroup puts W in that edge Sylow using a
centralizing actor of the original stabilizer. The general initial-orbit
center-centralizer theorem then puts the conjugate in the original neighbor
core. Conjugating back gives the desired neighbor and core containment.

This supplies the missing neighboring-core input to the first application
of (7.8) to W in (9.8), Stellmacher, printed p.55 / PDF p.45. The theorem
asserts only this genuine Sylow preparation, not the later index-two or
noncommutation conclusion.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise
universe u

public theorem nine_eight_core_neighbor_of_center_centralizing
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (d l : ctx.Γ.Vertex) (hl : l ∈ neighborhood ctx.Γ d)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a l)
    (W : Subgroup G) (hW : IsPGroup 2 W)
    (hWP : W ≤ GAt ctx.Γ d)
    (hWC : W ≤ Subgroup.centralizer (ZAt ctx.Γ l : Set G)) :
    ∃ neighbor : ctx.Γ.Vertex, neighbor ∈ neighborhood ctx.Γ d ∧ W ≤ QAt ctx.Γ neighbor := by
  let Γ := ctx.Γ
  let P := GAt Γ d
  let edge := P ⊓ GAt Γ l
  let edgeSylow := sylowTwoAmbient edge (default : Sylow 2 edge)
  have hsylow := (lemma_seven_three ctx.sectionSeven Γ).sylow_and_core d l hl
    (default : Sylow 2 edge)
  obtain ⟨hSP, localSylow, hlocalSylow⟩ := hsylow.1
  change (localSylow : Subgroup P).map P.subtype = edgeSylow at hlocalSylow
  let C := P ⊓ Subgroup.centralizer (ZAt Γ l : Set G)
  have hSC : edgeSylow ≤ Subgroup.normalizer (C : Set G) := by
    apply (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact hSP.trans P.le_normalizer
    · exact hsylow.2.1.1.trans ((stabilizer_le_normalizer_z Γ l).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.centralizer_le_normalizer (ZAt Γ l : Set G))).mp inferInstance))
  have hlocalC : (localSylow : Subgroup P) ≤ Subgroup.normalizer (C.subgroupOf P : Set P) := by
    intro actor hactor
    have hactorS : (actor : G) ∈ edgeSylow := by
      rw [← hlocalSylow]
      exact Subgroup.mem_map_of_mem P.subtype hactor
    apply Subgroup.mem_normalizer_iff.mpr
    intro element
    change (element : G) ∈ C ↔ (actor : G) * (element : G) * (actor : G)⁻¹ ∈ C
    exact Subgroup.mem_normalizer_iff.mp (hSC hactorS) element
  have hlocalW : IsPGroup 2 (W.subgroupOf P) :=
    hW.comap_of_injective P.subtype P.subtype_injective
  have hlocalWC : W.subgroupOf P ≤ C.subgroupOf P := by
    intro element helement
    exact ⟨element.property, hWC helement⟩
  obtain ⟨actor, hactorC, hconj⟩ := hlocalW.exists_conj_le_sylow_of_normalized
    localSylow (C.subgroupOf P) (W.subgroupOf P) hlocalC hlocalWC
  have hconjS : W.map (MulAut.conj (actor : G)).toMonoidHom ≤ edgeSylow := by
    rintro element ⟨w, hw, rfl⟩
    rw [← hlocalSylow]
    exact Subgroup.mem_map_of_mem P.subtype (hconj
      (Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom
        (show (⟨w, hWP hw⟩ : P) ∈ W.subgroupOf P from hw)))
  have hconjC : W.map (MulAut.conj (actor : G)).toMonoidHom ≤
      Subgroup.centralizer (ZAt Γ l : Set G) := by
    rintro element ⟨w, hw, rfl⟩
    exact (Subgroup.centralizer (ZAt Γ l : Set G)).mul_mem
      ((Subgroup.centralizer (ZAt Γ l : Set G)).mul_mem hactorC.2 (hWC hw))
      ((Subgroup.centralizer (ZAt Γ l : Set G)).inv_mem hactorC.2)
  have hcore := nine_three_orbit_pgroup_centralizer ctx l horbit _
    (hW.map (MulAut.conj (actor : G)).toMonoidHom)
    (hconjS.trans hsylow.2.1.1) hconjC
  refine ⟨Γ.act (actor : G) l, ?_, ?_⟩
  · apply (mem_neighborhood_iff_adjacent Γ).mpr
    have hadj := adjacent_act Γ (actor : G) ((mem_neighborhood_iff_adjacent Γ).mp hl)
    have hfix : Γ.act (actor : G) d = d :=
      (Set.ext_iff.mp (Γ.stabilizer_def d) (actor : G)).mp actor.property
    rwa [hfix] at hadj
  · change W ≤ q Γ (Γ.act (actor : G) l)
    rw [q_act]
    intro w hw
    refine ⟨(actor : G) * w * (actor : G)⁻¹,
      hcore (Subgroup.mem_map_of_mem _ hw), ?_⟩
    simp [mul_assoc]

end Stellmacher.SectionNine
