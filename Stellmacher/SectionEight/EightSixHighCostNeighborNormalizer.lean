module
public import Stellmacher.SectionEight.EightSixSelectedPlaneImage
public import Theory.GroupTheory.ElementaryEightPlaneMover

/-!
# The high-cost neighbor-plane normalizer quotient

The actual selected configuration in Stellmacher (8.6), including the
high-cost bound and Q=O₂(L), produces a neighbor lambda of the next vertex,
different from the initial vertex, whose joined center plane has normalizer
quotient by its full ambient centralizer isomorphic to PSL₃(2). The source
geometry, group, graph, normalizer, and centralizer are retained.

The selected orbit U of the initial center is elementary of order eight.
Its actual L-conjugation image has order twenty-four and preserves the
initial four-element plane, by `EightSixSelectedPlaneImage`. Since the
E-orbit spans U, some element of E moves that plane. The original and moved
planes join to U by their orders. The generic full-plane mover theorem
recognizes two distinct S₄ images inside the actual normalizer conjugation
range and identifies its quotient by the true centralizer with PSL₃(2).
Transporting the moved plane along the graph action gives the required
neighbor lambda. No model for E/C(U), self-centralization, or faithful
ambient action is assumed.

This proves the unchanged clause (c4) after assertion (16) in Stellmacher,
Journal of Algebra 190 (1997), (8.6), printed pp.44–45,
`refs/files/stellmacher-n-group.pdf`. It is independent of the later
high-cost cardinality calculations in assertions (20) and (21).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_high_cost_neighbor_normalizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hQ : Q = twoCoreIn L) :
    ∃ lam : ctx.Γ.Vertex,
      lam ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep ∧
      lam ≠ ctx.criticalPath.a ∧
      QuotientIsModel
        (Subgroup.normalizer
          ((ZAt ctx.Γ lam ⊔ ZAt ctx.Γ ctx.criticalPath.a : Subgroup G) : Set G))
        (Subgroup.centralizer
          ((ZAt ctx.Γ lam ⊔ ZAt ctx.Γ ctx.criticalPath.a : Subgroup G) : Set G))
        L3Two := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let B := ZAt Γ cp.a
  let U := conjugateClosure B E
  let _ : IsElementaryAbelian 2 U := eight_six_selected_orbit_elementary ctx E hcore
  have hU : Nat.card U = 8 := eight_six_selected_orbit_card_eight ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hseed : B ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hEN : E ≤ Subgroup.normalizer (U : Set G) := eight_six_conjugate_closure_normalizer _ _
  have hnot : ¬ E ≤ Subgroup.normalizer (B : Set G) := by
    intro h
    have heq : U = B := le_antisymm (eight_six_conjugate_closure_le B E B le_rfl h) hseed
    have hh : Nat.card U = Nat.card B := congrArg (fun K : Subgroup G => Nat.card K) heq
    rw [hU,hcard] at hh
    omega
  obtain ⟨mover, hmover, hmove⟩ := SetLike.not_le_iff_exists.mp hnot
  let C := B.map (MulAut.conj mover).toMonoidHom
  have hCne : C ≠ B := fun h => hmove (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hCU : C ≤ U := by
    have hh := Subgroup.map_mono (f := (MulAut.conj mover).toMonoidHom) hseed
    have hUn : U.map (MulAut.conj mover).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEN hmover)
    rw [hUn] at hh
    exact hh
  have hCcard : Nat.card C = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj mover).injective]
    exact hcard
  have hjoin : B ⊔ C = U := by
    have hle : B ⊔ C ≤ U := sup_le hseed hCU
    have hbound := Subgroup.card_le_of_le hle
    rw [hU] at hbound
    have hmore : 4 < Nat.card (B ⊔ C : Subgroup G) := by
      have hb := Subgroup.card_le_of_le (show B ≤ B ⊔ C from le_sup_left)
      change Nat.card B = 4 at hcard
      rw [hcard] at hb
      by_contra hn
      have heq : B = B ⊔ C := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
      have hCB : C ≤ B := le_sup_right.trans_eq heq.symm
      exact hCne (Subgroup.eq_of_le_of_card_ge hCB (by omega))
    have hdiv : 4 ∣ Nat.card (B ⊔ C : Subgroup G) :=
      hcard ▸ Subgroup.card_dvd_of_le (show B ≤ B ⊔ C from le_sup_left)
    obtain ⟨k,hk⟩ := hdiv
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  obtain ⟨hLN,hJ,hstable⟩ := eight_six_selected_plane_image_card ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hQ
  let f : L →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  let W := B.subgroupOf U
  let e : MulAut U := U.normalizerMonoidHom ⟨mover,hEN hmover⟩
  have hW : Nat.card W = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hseed).toEquiv]
    exact hcard
  have he : e ∈ U.normalizerMonoidHom.range := ⟨⟨mover,hEN hmover⟩,rfl⟩
  have hmapFormula : (W.map e.toMonoidHom).map U.subtype = C := by
    rw [Subgroup.map_map]
    have hh : U.subtype.comp e.toMonoidHom =
        (MulAut.conj mover).toMonoidHom.comp U.subtype := by ext u; rfl
    rw [hh,←Subgroup.map_map,Subgroup.map_subgroupOf_eq_of_le hseed]
  have hWmove : W.map e.toMonoidHom ≠ W := by
    intro h
    apply hCne
    rw [←hmapFormula,h,Subgroup.map_subgroupOf_eq_of_le hseed]
  have hJR : f.range ≤ U.normalizerMonoidHom.range := by
    rintro j ⟨l,rfl⟩
    exact ⟨⟨l,hLN l.property⟩,rfl⟩
  have hJstable : ∀ j : f.range, ∀ u : U, (j : MulAut U) u ∈ W ↔ u ∈ W := by
    intro j u
    have hh := (SetLike.ext_iff.mp (hstable j j.property) ((j:MulAut U) u)).symm
    simpa only [Subgroup.mem_map_equiv,MulEquiv.symm_apply_apply] using hh
  have hmodel : QuotientIsModel (Subgroup.normalizer (U : Set G))
      (Subgroup.centralizer (U : Set G)) L3Two :=
    elementaryEight_normalizer_centralizer_quotient_of_full_plane_mover U hU W hW
      f.range hJ hJR hJstable e he hWmove
  let lam := Γ.act mover⁻¹ cp.a
  have hC : ZAt Γ lam = C := by
    change z Γ (Γ.act mover⁻¹ cp.a) = _
    rw [z_act,inv_inv]
  have hmoverNext : mover⁻¹ ∈ GAt Γ cp.firstStep :=
    (GAt Γ cp.firstStep).inv_mem (geom.group_le hmover)
  have hfixed : Γ.act mover⁻¹ cp.firstStep = cp.firstStep := by
    exact Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) mover⁻¹ |>.mp hmoverNext
  have hlam : lam ∈ Neighborhood Γ cp.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    have hh := adjacent_act Γ mover⁻¹ (Γ.adjacent_symm cp.firstStep_adj)
    simpa only [hfixed] using hh
  refine ⟨lam,hlam,?_,?_⟩
  · intro heq
    exact hCne (hC.symm.trans (congrArg (ZAt Γ) heq))
  · have hspan : ZAt Γ lam ⊔ ZAt Γ cp.a = U := by rw [hC,sup_comm]; exact hjoin
    change QuotientIsModel
      (Subgroup.normalizer ((ZAt Γ lam ⊔ ZAt Γ cp.a : Subgroup G) : Set G))
      (Subgroup.centralizer ((ZAt Γ lam ⊔ ZAt Γ cp.a : Subgroup G) : Set G)) L3Two
    rw [hspan]
    exact hmodel

end Stellmacher.SectionEight
