module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood
public import Theory.GroupAction.RankTwoCosetGeometry.PathKernelTransport
public import Theory.GroupTheory.Commutator.PointCentralizers
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Transporting the radius-two core profile

The second-radius core, its neighborhood centralizer and the odd-actor
commutator bound transport around a vertex orbit. Coprime action splits
this kernel into the neighborhood span and the same literal fixed group.
Two-path transitivity identifies any pair of distinct neighboring cores
with that intrinsic kernel. These are the order-comparison inputs in
DGS, *Groups and Graphs* (1985), 9.10(4), printed pp.148--149.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original centralizer and residual-displacement profile transports to every vertex of the same type. -/
theorem radius_two_profile_transport
    (h : LocallyRankOneTriple P B) {beta : Vertex (family P)}
    (hcentral : Q (family P) beta ⊓ ballKernel (family P) beta 2 =
      Q (family P) beta ⊓ centralizer (V (family P) beta 1 : Set G))
    (hV : V (family P) beta 1 ≤ Q (family P) beta ⊓ ballKernel (family P) beta 2)
    (hres : ⁅Q (family P) beta ⊓ ballKernel (family P) beta 2,
      (pResidual 2 (graphLocalGroup (family P) beta)).map
        (graphLocalGroup (family P) beta).subtype⁆ ≤ V (family P) beta 1)
    (v : Vertex (family P)) (hv : beta.type = v.type) :
    Q (family P) v ⊓ ballKernel (family P) v 2 =
      Q (family P) v ⊓ centralizer (V (family P) v 1 : Set G) ∧
    V (family P) v 1 ≤ Q (family P) v ⊓ ballKernel (family P) v 2 ∧
    ∀ T : Subgroup G, T ≤ graphLocalGroup (family P) v → Odd (Nat.card T) →
      ⁅Q (family P) v ⊓ ballKernel (family P) v 2,T⁆ ≤ V (family P) v 1 := by
  let := finite_endpoints h
  let Γ := family P
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ v beta).mpr hv.symm
  let f := (MulAut.conj g).toMonoidHom
  have hJ : (Q Γ v ⊓ ballKernel Γ v 2).map f = Q Γ beta ⊓ ballKernel Γ beta 2 := by
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Q_translate,←ballKernel_translate,hg]
  have hVmap : (V Γ v 1).map f = V Γ beta 1 := by rw [←V_translate,hg]
  have hQmap : (Q Γ v).map f = Q Γ beta := by rw [←Q_translate,hg]
  have hlocal : (graphLocalGroup Γ v).map f = graphLocalGroup Γ beta := by
    rw [←graphLocalGroup_conjugate h g v,hg]
  refine ⟨?_,?_,?_⟩
  · apply Subgroup.map_injective (f := f) (MulAut.conj g).injective
    rw [hJ,←map_inf_centralizer_of_injective f (MulAut.conj g).injective,hQmap,hVmap]
    exact hcentral
  · apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    change (V Γ v 1).map f ≤ (Q Γ v ⊓ ballKernel Γ v 2).map f
    rw [hVmap,hJ]
    exact hV
  · intro T hTH ho
    let T' := T.map f
    have hTH' : T' ≤ graphLocalGroup Γ beta := hlocal ▸ map_mono hTH
    have ho' : Odd (Nat.card T') := by rwa [card_map_of_injective (MulAut.conj g).injective]
    have hTR : T' ≤ (pResidual 2 (graphLocalGroup Γ beta)).map
        (graphLocalGroup Γ beta).subtype := by
      intro t ht
      let l : graphLocalGroup Γ beta := ⟨t,hTH' ht⟩
      change (graphLocalGroup Γ beta).subtype l ∈ _
      apply mem_map_of_mem
      apply mem_pResidual_of_orderOf_coprime
      have htodd : Odd (orderOf l) := by
        rw [Subgroup.orderOf_mk]
        simpa only [Subgroup.orderOf_mk] using
          ho'.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨t,ht⟩ : T'))
      exact htodd.coprime_two_left
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rw [map_commutator,hJ,hVmap]
    exact (commutator_mono le_rfl hTR).trans hres

/-- Coprime decomposition uses the original radius-two fixed-point bound. -/
theorem radius_two_odd_decomposition
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    (T : Subgroup G) (hTH : T ≤ graphLocalGroup (family P) v)
    (ho : Odd (Nat.card T))
    (hV : V (family P) v 1 ≤ Q (family P) v ⊓ ballKernel (family P) v 2)
    (hmove : ⁅Q (family P) v ⊓ ballKernel (family P) v 2,T⁆ ≤ V (family P) v 1)
    (hfixed : Q (family P) v ⊓ centralizer (T : Set G) ≤ ballKernel (family P) v 2) :
    Q (family P) v ⊓ ballKernel (family P) v 2 =
      V (family P) v 1 ⊔ (Q (family P) v ⊓ centralizer (T : Set G)) := by
  let := finite_endpoints h
  let Γ := family P
  let J := Q Γ v ⊓ ballKernel Γ v 2
  let D := Q Γ v ⊓ centralizer (T : Set G)
  let : Finite J := Finite.of_injective (inclusion (inf_le_left.trans (Q_le_stabilizer Γ v)))
    (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion (hTH.trans (sylowGenerated_le _)))
    (inclusion_injective _)
  have hDJ : D ≤ J := le_inf inf_le_left hfixed
  have hTJ : T ≤ normalizer (J : Set G) :=
    (hTH.trans (sylowGenerated_le _)).trans
      ((le_inf (stabilizer_normalizes_Q Γ v) (stabilizer_le_normalizer_ballKernel Γ v 2)).trans
        inf_normalizer_le_normalizer_inf)
  have he := sup_eq_commutator_sup_of_fixed_le J D T
    ((isPGroup_pCoreIn 2 _).to_le inf_le_left) ho hTJ
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  rw [sup_eq_left.mpr hDJ] at he
  exact le_antisymm (he.le.trans (sup_le_sup_right hmove _)) (sup_le hV hDJ)

/-- Two-path transitivity preserves the literal intersection of the two endpoint cores. -/
theorem neighbor_core_intersection_radius_transport
    {a beta x u v w : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hbx : (graph (family P)).Adj beta x)
    (hax : x ≠ a) (huv : (graph (family P)).Adj u v)
    (hvw : (graph (family P)).Adj v w) (huw : w ≠ u)
    (htype : a.type = u.type)
    (ht : RootPathTransitive (graph (family P)) G u 2)
    (hN : Q (family P) a ⊓ Q (family P) x = Q (family P) beta ⊓ ballKernel (family P) beta 2) :
    Q (family P) u ⊓ Q (family P) w = Q (family P) v ⊓ ballKernel (family P) v 2 := by
  let Γ := family P
  let p : BasedWalk (graph Γ) 2 a := ⟨⟨beta,hab⟩,⟨⟨x,hbx⟩,PUnit.unit⟩⟩
  let q : BasedWalk (graph Γ) 2 u := ⟨⟨v,huv⟩,⟨⟨w,hvw⟩,PUnit.unit⟩⟩
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ a u).mpr htype
  let p' := BasedWalk.rebase hg (p.map (Subgroup.CosetGeometry.translationGraphIso Γ g).toHom)
  have hp : p.Nonbacktracking := ⟨hax,trivial⟩
  have hp' : p'.Nonbacktracking := (nonbacktracking_rebase _ _).mpr
    ((nonbacktracking_map_iff (Subgroup.CosetGeometry.translationGraphIso Γ g).toHom
      (fun z => (Subgroup.CosetGeometry.translationGraphIso Γ g).mapNeighborSet z |>.injective) p).mpr hp)
  obtain ⟨k,hk,hkpath⟩ := ht p' q hp' ⟨huw,trivial⟩
  have hpv : p'.vertices = p.vertices.map (g • ·) :=
    (vertices_rebase hg _).trans (vertices_map _ p)
  rw [hpv,List.map_map] at hkpath
  have hverts : (k*g) • a = u ∧ (k*g) • beta = v ∧ (k*g) • x = w := by
    simpa only [p,q,BasedWalk.vertices,List.map_cons,List.map_nil,List.cons.injEq,
      Function.comp_def,←mul_smul,and_true] using hkpath
  have he := congrArg (map (MulAut.conj (k*g)).toMonoidHom) hN
  rwa [map_inf _ _ _ (MulAut.conj (k*g)).injective,
    map_inf _ _ _ (MulAut.conj (k*g)).injective,
    ←Q_translate,←Q_translate,←Q_translate,←ballKernel_translate,
    hverts.1,hverts.2.1,hverts.2.2] at he

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
