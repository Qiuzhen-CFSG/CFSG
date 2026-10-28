module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedGeometry
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The original HS local hypotheses at every seed point

The actual seed normalizer fuses its seven involutions. Transport along
such a conjugator carries the full involution centralizer, its intrinsic
generalized Fitting subgroup, its quotient marking and the seed embedding
to the corresponding objects at the new point. The seed and its full
normalizer remain the same literal subgroups.

This supplies the distinct point cores used for involution lifts in a
dual-plane centralizer during the construction in I.4.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private def pointCentralizerEquiv (e : G ≃* G) (u : G) (hu : e z = u) :
    involutionCentralizer z ≃* involutionCentralizer u where
  toFun a := ⟨e a, mem_centralizer_singleton_iff.mpr (by
    rw [← hu, ← map_mul, ← map_mul]
    exact congrArg e (mem_centralizer_singleton_iff.mp a.property))⟩
  invFun a := ⟨e.symm a, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hu]
    exact mem_centralizer_singleton_iff.mp a.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv a := Subtype.ext (e.apply_symm_apply a)
  map_mul' a b := Subtype.ext (e.map_mul a b)

private theorem typeAt_of_seed_preserving_equiv (h : TypeAt z V)
    (e : G ≃* G) (heV : V.map e.toMonoidHom = V) (u : G) (hu : e z = u) :
    TypeAt u V := by
  let a := pointCentralizerEquiv e u hu
  have hcore : (localCore z).map a.toMonoidHom = localCore u :=
    map_generalizedFitting_equiv a
  let b : localCore z ≃* localCore u :=
    (a.subgroupMap (localCore z)).trans (MulEquiv.subgroupCongr hcore)
  refine {
    involution := ?_
    elementary := h.elementary
    seed_card := h.seed_card
    centralizer_core := h.centralizer_core.of_equiv b
    centralizer_quotient := ?_
    seed_le_core := ?_
    normalizer_core := h.normalizer_core
    normalizer_quotient := h.normalizer_quotient }
  · rw [← hu, e.orderOf_eq]
    exact h.involution
  · exact h.centralizer_quotient.map fun f =>
      (QuotientGroup.congr (localCore z) (localCore u) a hcore).symm.trans f
  · intro v hv
    have hw : e.symm v ∈ V := by
      rw [← heV] at hv
      exact mem_map_equiv.mp hv
    obtain ⟨q, hq, he⟩ := h.seed_le_core hw
    refine ⟨a q, hcore ▸ mem_map_of_mem a.toMonoidHom hq, ?_⟩
    change e (q : G) = v
    change (q : G) = e.symm v at he
    rw [he, e.apply_symm_apply]

/-- Each nonidentity element of the original seed has the same original
HS local data, with its own full involution centralizer and intrinsic core. -/
theorem TypeAt.at_seed_point (h : TypeAt z V) (u : G) (hu : u ∈ V) (hu1 : u ≠ 1) :
    TypeAt u V := by
  have hz1 : z ≠ 1 := by
    intro he
    have hh := h.involution
    simp [he] at hh
  obtain ⟨g, hg⟩ := h.seed_transitive ⟨z, h.involution_mem_seed⟩ ⟨u, hu⟩
    (fun he => hz1 (congrArg Subtype.val he))
    (fun he => hu1 (congrArg Subtype.val he))
  exact typeAt_of_seed_preserving_equiv h (MulAut.conj (g : G))
    (mem_normalizer_iff_map_conj_eq.mp g.property) u (congrArg Subtype.val hg)

end CFSG.Quasithin.HigmanSims
