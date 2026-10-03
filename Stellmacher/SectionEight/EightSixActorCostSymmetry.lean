module
public import Stellmacher.SectionEight.GeneratedEightSixNormalizerExtraction
public import Stellmacher.SectionNine.NineSevenShiftedIntersections

/-!
A uniform lower bound on the next quotient's predecessor-actor costs also
holds after interchanging the two distinct neighbors of the initial vertex.
The initial SL₂(2) quotient has a cubic local action; the proved ordered
two-arc transport supplies a stabilizer element swapping those neighbors.
Conjugation exchanges their modules, cores, and center lines, fixes the
initial core, and preserves the raw commutator relative index.

This makes explicit the symmetric applications of source assertion (15) in
Stellmacher's Lemma 8.6, printed pp.44–45, particularly (16) and (18).
The numerical bound is arbitrary, and no selected actor, module model, or
classification alternative is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_actor_cost_bound_symmetry
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (bound : ℕ)
    (hbound : ∀ actor : G, actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        bound ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath actor) :
    ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a →
      actor ∉ QAt ctx.Γ previous →
        bound ≤ (ZAt ctx.Γ previous).relIndex
          (⁅VAt ctx.Γ previous,Subgroup.zpowers actor⁆ ⊔ ZAt ctx.Γ previous) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hpa : Γ.adjacent cp.a previous := (SevenSix.mem_neighborhood_iff_adjacent Γ).mp hprev.1
  obtain ⟨g,hgPrev,hgInitial,hgNext⟩ := SectionNine.nine_seven_two_arc_transport
    ctx.sectionSeven Γ hpa cp.firstStep_adj hprev.2 cp.firstStep_adj hpa hprev.2.symm
    (show IsConjugateVertex Γ cp.a cp.a from ⟨1,Γ.act_one _⟩) hquot
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hVprev : (VAt Γ previous).map f = VAt Γ cp.firstStep := by
    change (v Γ previous).map (MulAut.conj g⁻¹).toMonoidHom = v Γ cp.firstStep
    rw [← v_act Γ g previous,hgPrev]
  have hVnext : (VAt Γ cp.firstStep).map f = VAt Γ previous := by
    change (v Γ cp.firstStep).map (MulAut.conj g⁻¹).toMonoidHom = v Γ previous
    rw [← v_act Γ g cp.firstStep,hgNext]
  have hZprev : (ZAt Γ previous).map f = ZAt Γ cp.firstStep := by
    change (z Γ previous).map (MulAut.conj g⁻¹).toMonoidHom = z Γ cp.firstStep
    rw [← z_act Γ g previous,hgPrev]
  have hQprev : (QAt Γ previous).map f = QAt Γ cp.firstStep := by
    change (q Γ previous).map (MulAut.conj g⁻¹).toMonoidHom = q Γ cp.firstStep
    rw [← SevenSix.q_act Γ g previous,hgPrev]
  have hQa : (QAt Γ cp.a).map f = QAt Γ cp.a := by
    change (q Γ cp.a).map (MulAut.conj g⁻¹).toMonoidHom = q Γ cp.a
    rw [← SevenSix.q_act Γ g cp.a,hgInitial]
  intro actor ha hout
  have hactor : f actor ∈ VAt Γ previous ⊓ QAt Γ cp.a :=
    ⟨hVnext ▸ Subgroup.mem_map_of_mem f ha.1,hQa ▸ Subgroup.mem_map_of_mem f ha.2⟩
  have hactorOut : f actor ∉ QAt Γ cp.firstStep := by
    rw [← hQprev]
    exact fun hm => hout ((Subgroup.mem_map_iff_mem (MulAut.conj g⁻¹).injective).mp hm)
  have hh := hbound (f actor) hactor hactorOut
  have heq := Subgroup.relIndex_map_map_of_injective (f := f) (ZAt Γ previous)
    (⁅VAt Γ previous,Subgroup.zpowers actor⁆ ⊔ ZAt Γ previous) (MulAut.conj g⁻¹).injective
  change (Subgroup.map f (ZAt Γ previous)).relIndex
    (Subgroup.map f (⁅VAt Γ previous,Subgroup.zpowers actor⁆ ⊔ ZAt Γ previous)) = _ at heq
  rw [Subgroup.map_sup,Subgroup.map_commutator,MonoidHom.map_zpowers,hZprev,hVprev] at heq
  exact heq ▸ hh

end Stellmacher.SectionEight
