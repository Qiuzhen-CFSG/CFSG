module

public import Stellmacher.PushingUp.CriticalDistanceBasic

/-!
# Transporting the nested `SL₂(2)` condition to a vertex stabilizer

This module formalizes the conjugacy transport of standing condition (A) used
in the proof of (2.2) of Stellmacher, *Pushing up*, Arch. Math. 46 (1986).  A
vertex in the orbit of the distinguished `M`-vertex has stabilizer isomorphic
to `M`.  Hence the assertion that
`(M / O₂(M)) / Φ(M / O₂(M))` is isomorphic to `SL₂(2)` also holds for the
corresponding nested quotient of the vertex stabilizer.

The proof privately identifies `M` with the base stabilizer and then transports
that stabilizer along the graph action by conjugation.  The resulting group
equivalence is lifted through `pCore` and `frattini` by two applications of
`QuotientGroup.congr`, after which the `SL₂(2)` isomorphism is composed with
the nested equivalence.  Only the final transport theorem is public.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M]

private def baseMHom (S : Subgroup M) :
    M →* stabilizer S (mVertex S 1) :=
  (embedM S).codRestrict _ (fun m ↦ by
    rw [stabilizer_m_base]
    exact ⟨m, rfl⟩)

private theorem baseMHom_injective (S : Subgroup M) :
    Function.Injective (baseMHom S) := by
  intro x y hxy
  apply embedM_injective S
  exact congrArg Subtype.val hxy

private theorem baseMHom_surjective (S : Subgroup M) :
    Function.Surjective (baseMHom S) := by
  intro y
  have hy : (y : FreeAmalgam S) ∈ Mbar S := by
    rw [← stabilizer_m_base]
    exact y.property
  obtain ⟨m, hm⟩ := hy
  refine ⟨m, Subtype.ext ?_⟩
  exact hm

private noncomputable def baseMEquiv (S : Subgroup M) :
    M ≃* stabilizer S (mVertex S 1) :=
  MulEquiv.ofBijective (baseMHom S)
    ⟨baseMHom_injective S, baseMHom_surjective S⟩

private noncomputable def stabilizerActEquiv (S : Subgroup M)
    (g : FreeAmalgam S) (d : Vertex S) :
    stabilizer S d ≃* stabilizer S (act S g d) :=
  ((MulAut.conj g⁻¹).subgroupMap (stabilizer S d)).trans
    (MulEquiv.subgroupCongr (stabilizer_act S g d).symm)

private theorem frattini_map_equiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro y hy
    have hy' : e.symm y ∈ frattini G :=
      frattini_le_comap_frattini_of_surjective
        (G := H) (H := G) (φ := e.symm.toMonoidHom) e.symm.surjective hy
    exact ⟨e.symm y, hy', e.apply_symm_apply y⟩

private theorem nested_isSL2Two_of_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    IsSL2Two
      ((H ⧸ pCore 2 H) ⧸ frattini (H ⧸ pCore 2 H)) := by
  have hcore : (pCore 2 G).map e.toMonoidHom = pCore 2 H :=
    pCore_map_iso 2 e
  let eCore : (G ⧸ pCore 2 G) ≃* (H ⧸ pCore 2 H) :=
    QuotientGroup.congr _ _ e hcore
  have hfrattini : (frattini (G ⧸ pCore 2 G)).map
      eCore.toMonoidHom = frattini (H ⧸ pCore 2 H) :=
    frattini_map_equiv eCore
  let eNested :
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)) ≃*
        ((H ⧸ pCore 2 H) ⧸ frattini (H ⧸ pCore 2 H)) :=
    QuotientGroup.congr _ _ eCore hfrattini
  obtain ⟨eSL⟩ := hA
  exact ⟨eNested.symm.trans eSL⟩

public theorem stabilizer_isSL2Two_nested_of_mOrbit [Finite M]
    (S : Subgroup M) (a : Vertex S) (ha : InMVertexOrbit S a)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M))) :
    IsSL2Two
      (((stabilizer S a ⧸ pCore 2 (stabilizer S a)) ⧸
        frattini (stabilizer S a ⧸ pCore 2 (stabilizer S a)))) := by
  obtain ⟨g, rfl⟩ := ha
  let e : M ≃* stabilizer S (act S g (mVertex S 1)) :=
    (baseMEquiv S).trans (stabilizerActEquiv S g (mVertex S 1))
  exact nested_isSL2Two_of_mulEquiv e hA

end Stellmacher.PushingUp
