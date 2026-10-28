module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ChevalleyVersions
public import Theory.AlgebraicGroup.RootSystems.Weyl

/-!
This module transports the geometric root-model data used by Chevalley
versions along an equivalence of finite reduced crystallographic root pairings.
The carrier, algebraic-group structure, maximal torus, root realization, and
all semisimplicity data are left unchanged; only the base and the indexing
equivalence are transported.  The compatibility proof is the formal content
of the pairing equivalence: its root-weight map carries reflections to
reflections, while the mapped base support is characterized by
`Base.mem_mapEquiv_support`.  This gives a small API for concrete Cartan-type
model modules without invoking any downstream version theorem.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public noncomputable def RootSystemModel.transport
    {ι E E' ι₂ F F' : Type u} [Finite ι] [Finite ι₂]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    {Q : RootPairing ι₂ ℝ F F'} [Q.IsRootSystem] [Q.IsCrystallographic]
    [Q.IsReduced]
    (e : P.Equiv Q) {G : Variety k} [AlgebraicGroup G]
    (model : RootSystemModel Q G) : RootSystemModel P G := by
  let es : Q.Equiv P := RootPairing.Equiv.symm P Q e
  let b : P.Base := RootPairing.Base.mapEquiv es model.base
  let eroot : model.rootData.Root ≃ ι := model.rootEquiv.trans es.indexEquiv
  have hreflect (i j : ι₂) :
      es.indexEquiv (Q.reflectionPerm i j) =
        P.reflectionPerm (es.indexEquiv i) (es.indexEquiv j) := by
    apply P.root.injective
    rw [P.root_reflectionPerm]
    rw [← RootPairing.Hom.root_weightMap_apply Q P
      (Q.reflectionPerm i j) es.toHom]
    rw [Q.root_reflectionPerm]
    rw [Q.reflection_apply, map_sub, map_smul]
    rw [RootPairing.Hom.root_weightMap_apply Q P i es.toHom,
      RootPairing.Hom.root_weightMap_apply Q P j es.toHom]
    rw [Q.root_coroot'_eq_pairing]
    rw [← es.pairing_eq j i]
    rw [P.reflection_apply_root]
  have hactual : IsActualBasedRootPairing model.rootData P b eroot := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro α β
      change (model.rootData.pairing α β : ℝ) =
        P.pairing (eroot α) (eroot β)
      rw [model.actual.1 α β]
      exact (RootPairing.Equiv.pairing_eq es
        (model.rootEquiv α) (model.rootEquiv β)).symm
    · intro α β
      change es.indexEquiv (model.rootEquiv (model.rootData.reflect α β)) =
        P.reflectionPerm (es.indexEquiv (model.rootEquiv α))
          (es.indexEquiv (model.rootEquiv β))
      rw [model.actual.2.1 α β]
      exact hreflect _ _
    · intro α
      change es.indexEquiv (model.rootEquiv (model.rootData.neg α)) =
        P.reflectionPerm (es.indexEquiv (model.rootEquiv α))
          (es.indexEquiv (model.rootEquiv α))
      rw [model.actual.2.2.1 α]
      exact hreflect _ _
    · intro α
      change α ∈ model.rootData.simple ↔
        es.indexEquiv (model.rootEquiv α) ∈ b.support
      rw [model.actual.2.2.2 α]
      change model.rootEquiv α ∈ model.base.support ↔
        es.indexEquiv (model.rootEquiv α) ∈
          (RootPairing.Base.mapEquiv es model.base).support
      rw [RootPairing.Base.mem_mapEquiv_support]
      simp
  exact
    { torus := model.torus
      maximalTorus := model.maximalTorus
      rootData := model.rootData
      realization := model.realization
      base := b
      rootEquiv := eroot
      actual := hactual }

omit [IsAlgClosed k] in
public noncomputable def SemisimpleVersion.transport
    {ι E E' ι₂ F F' : Type u} [Finite ι] [Finite ι₂]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    {Q : RootPairing ι₂ ℝ F F'} [Q.IsRootSystem] [Q.IsCrystallographic]
    [Q.IsReduced]
    (e : P.Equiv Q) (V : SemisimpleVersion (k := k) Q) :
    SemisimpleVersion (k := k) P := by
  letI : AlgebraicGroup V.carrier := V.group
  exact
    { carrier := V.carrier
      group := V.group
      semisimple := V.semisimple
      rootModel := RootSystemModel.transport e V.rootModel }

end Theory.AlgebraicGroup
