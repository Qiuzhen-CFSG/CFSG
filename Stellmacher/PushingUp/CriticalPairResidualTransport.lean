module

public import Stellmacher.PushingUp.CriticalVertexCentralizer

/-!
# Transporting the critical-vertex residual hypothesis

This module proves the conjugacy transport used immediately before clause
(1.4)(b) of Stellmacher, *Pushing up*, Arch. Math. 46 (1986).  If two vertices
lie in the orbit of the distinguished `M`-vertex, their stabilizers are
conjugate.  Consequently the hypothesis that the 2-residual of
`(G_a / O₂(G_a)) / Φ(G_a / O₂(G_a))` is minimal normal transfers from either
vertex to the other.

The proof fixes the right-action orientation explicitly, transports the
stabilizer through conjugation, and lifts that isomorphism first through the
2-core quotient and then through the Frattini quotient.  The 2-residual is
functorial under the resulting equivalence, while minimal normality is
transported by mapping and comapping subgroups.  This source-neutral orbit
lemma keeps path parity and critical-distance arguments in the later
critical-pair module.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph
open BenderSuzuki External

universe u v

variable {M : Type u} [Group M]

private theorem exists_act_eq_of_mOrbit (S : Subgroup M)
    {a b : Vertex S} (ha : InMVertexOrbit S a)
    (hb : InMVertexOrbit S b) :
    ∃ g : FreeAmalgam S, b = act S g a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x⁻¹ * y, ?_⟩
  rw [hy, ← act_mul]
  simp

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

private theorem hktPResidual_le_map_equiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    hktPResidual 2 H ≤ (hktPResidual 2 G).map e.toMonoidHom := by
  let R : Subgroup G := hktPResidual 2 G
  have hRnormal : R.Normal := hktPResidual_normal
  let _ : R.Normal := hRnormal
  have hmapNormal : (R.map e.toMonoidHom).Normal :=
    hRnormal.map e.toMonoidHom e.surjective
  let _ : (R.map e.toMonoidHom).Normal := hmapNormal
  let eQ : (G ⧸ R) ≃* (H ⧸ R.map e.toMonoidHom) :=
    QuotientGroup.congr R (R.map e.toMonoidHom) e rfl
  have hquot : IsPGroup 2 (H ⧸ R.map e.toMonoidHom) :=
    (hktPResidual_quotient_isPGroup (Q := G) (q := 2)).of_equiv eQ
  exact hktPResidual_le (R.map e.toMonoidHom) hmapNormal hquot

private theorem hktPResidual_map_equiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (hktPResidual 2 G).map e.toMonoidHom = hktPResidual 2 H := by
  apply le_antisymm
  · have hback := hktPResidual_le_map_equiv e.symm
    have hmap := Subgroup.map_mono (f := e.toMonoidHom) hback
    have hcancel : ((hktPResidual 2 H).map e.symm.toMonoidHom).map
        e.toMonoidHom = hktPResidual 2 H := by
      ext x
      simp
    exact hmap.trans_eq hcancel
  · exact hktPResidual_le_map_equiv e

private theorem twoResidualAmbient_top_map_equiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (twoResidualAmbient (⊤ : Subgroup G)).map e.toMonoidHom =
      twoResidualAmbient (⊤ : Subgroup H) := by
  rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual,
    SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  exact hktPResidual_map_equiv e

private theorem isMinimalNormalOver_bot_top_map_equiv
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (R : Subgroup G)
    (h : SectionThree.IsMinimalNormalOver
      (⊥ : Subgroup G) (⊤ : Subgroup G) R) :
    SectionThree.IsMinimalNormalOver
      (⊥ : Subgroup H) (⊤ : Subgroup H) (R.map e.toMonoidHom) := by
  have hRnormal : R.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    exact top_unique <|
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp h.2.2.2.1
  have hRmapNormal : (R.map e.toMonoidHom).Normal :=
    hRnormal.map e.toMonoidHom e.surjective
  refine ⟨bot_le, le_top, ?_, ?_, ?_⟩
  · intro hmapBot
    exact h.2.2.1 <|
      (Subgroup.map_eq_bot_iff_of_injective R e.injective).mp hmapBot
  · simpa using hRmapNormal.subgroupOf (⊤ : Subgroup H)
  · intro K _hbotK _hKtop hKnormal hKR
    let Kpre : Subgroup G := K.comap e.toMonoidHom
    have hKnormal' : K.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      exact top_unique <|
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hKnormal
    have hKpreNormal : Kpre.Normal := hKnormal'.comap e.toMonoidHom
    have hKpreR : Kpre ≤ R := by
      intro x hx
      have hex : e x ∈ K := hx
      have heR : e x ∈ R.map e.toMonoidHom := hKR hex
      simpa using (Subgroup.mem_map_equiv.mp heR)
    have hmin := h.2.2.2.2 Kpre bot_le le_top
      (by simpa using hKpreNormal.subgroupOf (⊤ : Subgroup G)) hKpreR
    rcases hmin with hKbot | hKR'
    · left
      have hmap := congrArg (Subgroup.map e.toMonoidHom) hKbot
      rw [show Kpre = K.comap e.toMonoidHom from rfl,
        Subgroup.map_comap_eq_self_of_surjective e.surjective] at hmap
      simpa using hmap
    · right
      have hmap := congrArg (Subgroup.map e.toMonoidHom) hKR'
      rw [show Kpre = K.comap e.toMonoidHom from rfl,
        Subgroup.map_comap_eq_self_of_surjective e.surjective] at hmap
      exact hmap

private theorem hasMinimalFrattiniResidual_act [Finite M]
    (S : Subgroup M) (g : FreeAmalgam S) (a : Vertex S)
    (hres : HasMinimalFrattiniResidual S a) :
    HasMinimalFrattiniResidual S (act S g a) := by
  let e : stabilizer S a ≃* stabilizer S (act S g a) :=
    stabilizerActEquiv S g a
  have hcore : (pCore 2 (stabilizer S a)).map e.toMonoidHom =
      pCore 2 (stabilizer S (act S g a)) := pCore_map_iso 2 e
  let eCore : VertexCoreQuotient S a ≃*
      VertexCoreQuotient S (act S g a) :=
    QuotientGroup.congr _ _ e hcore
  have hfrattini : (frattini (VertexCoreQuotient S a)).map
      eCore.toMonoidHom = frattini (VertexCoreQuotient S (act S g a)) :=
    frattini_map_equiv eCore
  let eNested : VertexFrattiniQuotient S a ≃*
      VertexFrattiniQuotient S (act S g a) :=
    QuotientGroup.congr _ _ eCore hfrattini
  have hminimalMap := isMinimalNormalOver_bot_top_map_equiv eNested
    (vertexFrattiniResidual S a) hres
  have hresMap : (vertexFrattiniResidual S a).map eNested.toMonoidHom =
      vertexFrattiniResidual S (act S g a) := by
    exact twoResidualAmbient_top_map_equiv eNested
  rwa [hresMap] at hminimalMap

public theorem hasMinimalFrattiniResidual_of_mOrbit [Finite M]
    (S : Subgroup M) {a a' : Vertex S}
    (ha : InMVertexOrbit S a) (ha' : InMVertexOrbit S a')
    (hres : HasMinimalFrattiniResidual S a) :
    HasMinimalFrattiniResidual S a' := by
  obtain ⟨g, hg⟩ := exists_act_eq_of_mOrbit S ha ha'
  rw [hg]
  exact hasMinimalFrattiniResidual_act S g a hres

end Stellmacher.PushingUp
