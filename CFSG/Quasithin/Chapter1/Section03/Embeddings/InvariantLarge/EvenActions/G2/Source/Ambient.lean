module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Model
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter1.Section03.Basic.FrattiniAction

/-!
# Transporting actual ambient conjugation to the G₂ model

Conjugation on a normal subgroup, transported through a multiplicative
equivalence, gives an action of the whole ambient group on the model. Each
ambient Sylow element preserves the intersection with the normal subgroup.
These equations identify the source action rather than assuming an abstract
action with the desired properties.

Source: the normal-subgroup and Sylow-intersection step in Aschbacher–Smith,
combined 1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
variable {J E : Type*} [Group J] (D : Subgroup J) [D.Normal] [Field E]

def modelAction (e : D ≃* Model E) : J →* MulAut (Model E) where
  toFun s := (e.symm.trans (MulAut.conjNormal s)).trans e
  map_one' := by ext x; simp
  map_mul' s t := by
    ext x
    simp [MulEquiv.trans_apply, map_mul]

@[simp] theorem modelAction_apply (e : D ≃* Model E) (s : J) (d : D) :
    modelAction D e s (e d) = e (MulAut.conjNormal s d) := by
  simp [modelAction]

theorem modelAction_inner (e : D ≃* Model E) (d : D) :
    modelAction D e (d : J) = MulAut.conj (e d) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [modelAction_apply]
  change e (d * y * d⁻¹) = e d * e y * (e d)⁻¹
  simp


theorem modelAction_preserves_intersection (e : D ≃* Model E)
    (S : Subgroup J) (s : S) :
    ((S.subgroupOf D).map e.toMonoidHom).map (modelAction D e s).toMonoidHom =
      (S.subgroupOf D).map e.toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change modelAction D e s (e x) ∈ _
    rw [modelAction_apply]
    apply mem_map_of_mem
    exact S.mul_mem (S.mul_mem s.property hx) (S.inv_mem s.property)
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨e (MulAut.conjNormal (s : J)⁻¹ x), ?_, ?_⟩
    · apply mem_map_of_mem
      change (s : J)⁻¹ * (x : J) * ((s : J)⁻¹)⁻¹ ∈ S
      rw [inv_inv]
      exact S.mul_mem (S.mul_mem (S.inv_mem s.property) (show (x : J) ∈ S from hx)) s.property
    · change modelAction D e s (e (MulAut.conjNormal (s : J)⁻¹ x)) = e x
      rw [modelAction_apply]
      congr 1
      apply Subtype.ext
      change (s : J) * ((s : J)⁻¹ * (x : J) * ((s : J)⁻¹)⁻¹) * (s : J)⁻¹ = x
      group

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
