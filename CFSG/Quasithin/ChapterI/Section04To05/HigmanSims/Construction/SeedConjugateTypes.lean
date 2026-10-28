module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Type
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Full HS markings on literal images and conjugates of the seed

An actual group isomorphism carries the full marked involution centralizer
and the full seed normalizer to the corresponding image subgroups. Their
intrinsic generalized Fitting subgroups and quotient markings transport
with them. Thus every conjugate of the original involution has an actual
conjugate seed satisfying the complete original TypeAt hypotheses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
variable {z : G} {V : Subgroup G}

/-- Transport every original HS clause along an actual group isomorphism,
retaining the literal image seed and the full centralizer and normalizer. -/
theorem TypeAt.map (h : TypeAt z V) (e : G ≃* G') :
    TypeAt (e z) (V.map e.toMonoidHom) := by
  have hH : (involutionCentralizer z).map e.toMonoidHom =
      involutionCentralizer (e z) := by
    simpa only [Set.image_singleton] using map_centralizer_equiv ({z} : Set G) e
  let a : involutionCentralizer z ≃* involutionCentralizer (e z) :=
    (e.subgroupMap (involutionCentralizer z)).trans (MulEquiv.subgroupCongr hH)
  have hQ : (localCore z).map a.toMonoidHom = localCore (e z) :=
    map_generalizedFitting_equiv a
  let aq : localCore z ≃* localCore (e z) :=
    (a.subgroupMap (localCore z)).trans (MulEquiv.subgroupCongr hQ)
  let M := normalizer (V : Set G)
  let M' := normalizer (V.map e.toMonoidHom : Set G')
  have hM : M.map e.toMonoidHom = M' := map_equiv_normalizer_eq V e
  let m : M ≃* M' := (e.subgroupMap M).trans (MulEquiv.subgroupCongr hM)
  have hP : (generalizedFitting M).map m.toMonoidHom = generalizedFitting M' :=
    map_generalizedFitting_equiv m
  let mp : generalizedFitting M ≃* generalizedFitting M' :=
    (m.subgroupMap (generalizedFitting M)).trans (MulEquiv.subgroupCongr hP)
  let : IsElementaryAbelian 2 V := h.elementary
  refine {
    involution := (e.orderOf_eq z).trans h.involution
    elementary := IsElementaryAbelian.map e.toMonoidHom
    seed_card := (card_map_of_injective e.injective).trans h.seed_card
    centralizer_core := h.centralizer_core.of_equiv aq
    centralizer_quotient := ?_
    seed_le_core := ?_
    normalizer_core := h.normalizer_core.map (fun f => mp.symm.trans f)
    normalizer_quotient := ?_ }
  · exact h.centralizer_quotient.map (fun f =>
      (QuotientGroup.congr (localCore z) (localCore (e z)) a hQ).symm.trans f)
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨q, hq, hqv⟩ := h.seed_le_core hv
    refine ⟨a q, hQ ▸ mem_map_of_mem a.toMonoidHom hq, ?_⟩
    change e (q : G) = e v
    exact congrArg e hqv
  · exact h.normalizer_quotient.of_mulEquiv
      (QuotientGroup.congr (generalizedFitting M) (generalizedFitting M') m hP).symm

/-- Conjugation transports the original full HS marking to its literal
conjugate involution and seed. -/
theorem TypeAt.conj (h : TypeAt z V) (g : G) :
    TypeAt (g * z * g⁻¹) (V.map (MulAut.conj g).toMonoidHom) :=
  h.map (MulAut.conj g)

/-- Every involution in the original marked conjugacy class has a seed
satisfying all of the original HS local hypotheses. -/
theorem TypeAt.exists_typeAt_of_isConj (h : TypeAt z V) (x : G) (hx : IsConj x z) :
    ∃ W : Subgroup G, TypeAt x W := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx.symm
  exact ⟨V.map (MulAut.conj g).toMonoidHom, hg ▸ h.conj g⟩

end CFSG.Quasithin.HigmanSims
