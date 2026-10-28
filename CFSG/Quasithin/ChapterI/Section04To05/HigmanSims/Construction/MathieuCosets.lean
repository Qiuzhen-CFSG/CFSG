module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CosetFaithfulness
public import Theory.SpecificGroups.LeechRelated.HSRecognition.RankThreeData
public import Theory.GroupAction.MarkedOrbit

/-!
# The rank-three action from literal Mathieu coset geometry

Given an actual M₂₂ subgroup of index 100, with three orbits on its
left-coset space and an orbit of length 22, transport the left action to
Fin 100. The identity coset is sent to 0. The previously proved type-HS
kernel theorem supplies injectivity, and the range equivalence transports
the actual point stabilizer, orbit relation and suborbit size.

The source subgroup construction must still provide the subgroup, its
index and its two orbit clauses. This theorem removes every further action,
faithfulness and coordinate-transport premise from that construction; it
does not claim the existence of the required coset geometry.

Source: the degree-100 action discussed at Aschbacher–Smith I.4.8,
printed p.418. The remaining local construction and the final application
are owned by qt-i48-hs-rank-three-construction.
-/

public section

open Subgroup MulAction Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The literal index and suborbit conditions suffice; faithfulness follows from HS1–HS2. -/
theorem TypeAt.rank_three_action_of_mathieu_cosets (h : TypeAt z V) (K : Subgroup G)
    (eK : K ≃* Sporadic.Mathieu.M22) (hi : K.index = 100)
    (hrank : Nat.card (orbitRel.Quotient K (G ⧸ K)) = 3)
    (hsub : ∃ x : G ⧸ K, Nat.card (orbit K x) = 22) :
    Sporadic.LeechRelated.HS.HasRankThreeAction G := by
  classical
  let X := G ⧸ K
  let base : X := (1 : G)
  let : Fintype X := Fintype.ofFinite X
  let e₀ : X ≃ Fin 100 := Fintype.equivFinOfCardEq
    (by rw [← Nat.card_eq_fintype_card]; exact hi)
  let e : X ≃ Fin 100 := e₀.trans (Equiv.swap (e₀ base) 0)
  have he0 : e base = 0 := by simp [e]
  let f : G →* Equiv.Perm (Fin 100) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G X)
  have hf : Function.Injective f :=
    (Equiv.permCongrHom e).injective.comp (h.m22_coset_faithful K eK)
  let a : G ≃* f.range := MonoidHom.ofInjective hf
  have ha (g : G) (x : X) : e (g • x) = a g • e x := by
    change e (g • x) = ((Equiv.permCongrHom e) (MulAction.toPermHom G X g)) (e x)
    simp
  have hs : K.map a.toMonoidHom = stabilizer f.range (0 : Fin 100) := by
    have hh := stabilizer_map_of_equivariant a e ha base
    rw [he0] at hh
    change (stabilizer G ((1 : G) : G ⧸ K)).map a.toMonoidHom = _ at hh
    rwa [stabilizer_quotient] at hh
  have hrel (x y : X) : orbitRel K X x y ↔
      orbitRel (K.map a.toMonoidHom) (Fin 100) (e x) (e y) := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨⟨a k, mem_map_of_mem _ k.property⟩, ?_⟩
      exact (ha k y).symm.trans (congrArg e hk)
    · rintro ⟨k, hk⟩
      obtain ⟨g, hg, he⟩ := k.property
      refine ⟨⟨g, hg⟩, e.injective ?_⟩
      exact (ha g y).trans ((congrArg (fun b : f.range => b • e y) he).trans hk)
  refine ⟨f, hf, ?_⟩
  constructor
  · constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e.symm x) (e.symm y)
    refine ⟨a g, ?_⟩
    simpa only [Equiv.apply_symm_apply] using (ha g (e.symm x)).symm.trans (congrArg e hg)
  · exact ⟨((MulEquiv.subgroupCongr hs).symm.trans (a.subgroupMap K).symm).trans eK⟩
  · rw [← hs, ← hrank]
    exact (Nat.card_congr (Quotient.congr e hrel)).symm
  · obtain ⟨x, hx⟩ := hsub
    refine ⟨e x, ?_⟩
    rw [← hs, ← hx]
    exact (orbit_card_of_equivariant a e ha K x).symm
end CFSG.Quasithin.HigmanSims
