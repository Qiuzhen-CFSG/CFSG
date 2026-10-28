module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Basic
public import Theory.GroupAction.ActorSubtypeCommutator
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Ambient conjugation of a normal subgroup's canonical supports

Let H be normal in an acting group G. Conjugation by G preserves the Fitting
subgroup of H, factor order and displacement cardinality. Thus it permutes
H's canonical small-support family through the actual normal-conjugation
automorphism of H. The join of these factors, mapped into G, is normal in G.

The support identity uses the ambient G action, with literal actor inclusions.
This supplies the ambient normality needed when projecting the source seed
onto the canonical fixed complement for Jhat in original 15.1.2 and D.2.25.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
  (H : Subgroup G) [H.Normal]

private theorem support_map_conjNormal (X : Subgroup H) (g : G) :
    (commutatorAction X V).map (MulDistribMulAction.toMulAut G V g).toMonoidHom =
      commutatorAction (X.map (MulAut.conjNormal g).toMonoidHom) V := by
  rw [←commutatorAction_map_actor_subtype H X,
    ←commutatorAction_map_actor_subtype H (X.map (MulAut.conjNormal g).toMonoidHom)]
  have he : (X.map (MulAut.conjNormal g).toMonoidHom).map H.subtype =
      (X.map H.subtype).conjBy g := by
    simp only [conjBy,map_map]
    congr 1
  rw [he]
  exact smallSupport_support_conjBy _ _

theorem smallSupportFactors_conjNormal {k : ℕ} {X : Subgroup H}
    (hX : X ∈ smallSupportFactors H V k) (g : G) :
    X.map (MulAut.conjNormal g).toMonoidHom ∈ smallSupportFactors H V k := by
  refine ⟨?_,?_,?_⟩
  · exact (map_mono hX.1).trans_eq ((characteristic_iff_map_eq.mp inferInstance) _)
  · exact (card_map_of_injective (f := (MulAut.conjNormal g : MulAut H).toMonoidHom)
      (MulAut.conjNormal g).injective).trans hX.2.1
  · rw [←support_map_conjNormal H X g]
    exact (card_map_of_injective
      (f := (MulDistribMulAction.toMulAut G V g).toMonoidHom)
      (MulDistribMulAction.toMulAut G V g).injective).trans hX.2.2

theorem smallSupportGroup_map_normal (k : ℕ) :
    ((smallSupportGroup H V k).map H.subtype).Normal := by
  constructor
  rintro _ ⟨x,hx,rfl⟩ g
  have hm : (smallSupportGroup H V k).map (MulAut.conjNormal g).toMonoidHom ≤
      smallSupportGroup H V k := by
    rw [smallSupportGroup_eq_iSup,Subgroup.map_iSup]
    exact iSup_le fun X => le_iSup_of_le
      ⟨X.val.map (MulAut.conjNormal g).toMonoidHom,smallSupportFactors_conjNormal H X.property g⟩ le_rfl
  exact ⟨MulAut.conjNormal g x,hm (mem_map_of_mem _ hx),rfl⟩
end CFSG.Quasithin.ChapterD
