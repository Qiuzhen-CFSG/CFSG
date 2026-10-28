module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.SourceModel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ModelInput
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# Transport from the literal action quotient to the ambient automizer

The first isomorphism theorem for the original normalizer action identifies
its quotient with Aut_G(W). Transporting the compatible H.9 source model
along that exact equivalence preserves the representation and both marked
summands. In particular, the H.9 generated-core theorems apply to the same
action image used by E.3.32.

This transports an existing SourceModel; its independent construction
remains with the source-model producer. The layer comparison and the
transported implementation stay private behind the marked-model interface.
Source: Aschbacher--Smith, H.9 and 12.1.3, printed pp.389--392,789--790.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)
  (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))

private theorem layer_mem_iff {K H : Type*} [Group K] [Group H] (e : K ≃* H) (k : K) :
    e k ∈ componentLayer H ↔ k ∈ componentLayer K := by
  constructor
  · intro hk
    have he := map_componentLayer_le e.symm.toMonoidHom e.symm.surjective
    simpa using he (mem_map_of_mem e.symm.toMonoidHom hk)
  · intro hk
    exact map_componentLayer_le e.toMonoidHom e.surjective (mem_map_of_mem _ hk)

private def layerEquiv :
    componentLayer (Automizer (componentOrbit V (T : Subgroup G))) ≃*
      componentLayer B.ActionQuotient where
  toFun a := ⟨(B.quotientEquivAutomizer hNM).symm a,
    (layer_mem_iff (B.quotientEquivAutomizer hNM).symm a).mpr a.property⟩
  invFun a := ⟨B.quotientEquivAutomizer hNM a,
    (layer_mem_iff (B.quotientEquivAutomizer hNM) a).mpr a.property⟩
  left_inv a := Subtype.ext ((B.quotientEquivAutomizer hNM).apply_symm_apply a)
  right_inv a := Subtype.ext ((B.quotientEquivAutomizer hNM).symm_apply_apply a)
  map_mul' a b := Subtype.ext ((B.quotientEquivAutomizer hNM).symm.map_mul a b)

theorem representation_automizer (a : Automizer (componentOrbit V (T : Subgroup G))) :
    S.setup.representation ((B.quotientEquivAutomizer hNM).symm a) =
      automizerRepresentation (componentOrbit V (T : Subgroup G)) a := by
  obtain ⟨q, rfl⟩ := (B.quotientEquivAutomizer hNM).surjective a
  obtain ⟨m, rfl⟩ := B.actionProjection_surjective q
  rw [MulEquiv.symm_apply_apply, S.representation_eq]
  rfl

/-- Transport the supplied compatible quotient model to the literal ambient automizer. -/
def automizerModel : B.MarkedAutomizerModel where
  setup := {
    degree := S.setup.degree
    projective := (B.quotientEquivAutomizer hNM).symm.trans S.setup.projective
    layer := (layerEquiv hNM).trans S.setup.layer
    representation := automizerRepresentation (componentOrbit V (T : Subgroup G))
    natural := S.setup.natural
    dual := S.setup.dual
    complement := S.setup.complement
    naturalCoordinates := S.setup.naturalCoordinates
    natural_action := by
      intro l x
      rw [← S.representation_automizer hNM]
      exact S.setup.natural_action (layerEquiv hNM l) x
    outer := by
      obtain ⟨t, ht, he⟩ := S.setup.outer
      refine ⟨B.quotientEquivAutomizer hNM t,
        fun hh => ht ((layer_mem_iff (B.quotientEquivAutomizer hNM) t).mp hh), ?_⟩
      rw [← S.representation_automizer hNM, MulEquiv.symm_apply_apply]
      exact he }
  representation_eq := rfl
  natural_eq := by
    ext w
    exact S.natural_marking w.toMul
  dual_eq := by
    ext w
    exact S.dual_marking w.toMul

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
