module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ShiftedSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CommutatorSpan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathLength

/-!
# The large-distance commutator centralizer supplement

In the b > 3 branch of DGS 9.8, put R = [V_beta,V_alpha-prime] and
W = V_alpha^(2). The shifted critical pair gives W the full Sylow index
at w = alpha-prime-2. The actual linear markings and source 6.5 give
two-edge path transitivity. Moving the initial two edges of the geodesic
from w to alpha onto (w,alpha-prime-1,alpha-prime) constructs g fixing w
such that W^g centralizes V_alpha-prime. The critical-distance estimate
uses only connectedness, without a tree assumption.

The two actors W and W^g fix distinct neighbors of w. Their quotient
images are distinct Sylows of SL2, so they generate L_w modulo Q_w.
Both centralize R; consequently L_w = C_{L_w}(R) Q_w. This also proves
that [R,Q_w] is a normal subgroup of L_w contained in Q_w.

The original F1.11 application constructs both endpoint markings and
retains both original natural sections and their equal field orders.
The genuine catalogue, Chapter 8 and 6.5 inputs remain explicit. The
remaining geometric bounds on [R,Q_w], the whole-span conclusion of
9.8, and the terminal distance and field conclusions remain to be proved.

Source: DGS, Groups and Graphs (1985), 9.8, printed p.146, using 6.8
on pp.123--124 and 9.3--9.7 on pp.142--145.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem linear_full_image
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G) (hAH : A ≤ graphLocalGroup (family P) v) (hpA : IsPGroup 2 A)
    (hi : (Q (family P) v).relIndex A = Nat.card F) :
    ∃ T : Sylow 2 SL(2,F), (A.subgroupOf (graphLocalGroup (family P) v)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))) = T := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  let I := (A.subgroupOf H).map q
  obtain ⟨T,hT⟩ := (hpA.comap_subtype.map q).exists_le_sylow
  refine ⟨T,eq_of_le_of_card_ge hT ?_⟩
  have hc : Nat.card I = Nat.card F := by
    rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
      hkmap,map_subgroupOf_eq_of_le hAH,hi]
  rw [hc]
  exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).ge

/-- Two full-index two-actors fixing distinct neighbors generate the actual local quotient. -/
theorem linear_local_two_actor_generation
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y) (hne : x ≠ y)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A C : Subgroup G) (hAH : A ≤ graphLocalGroup (family P) v)
    (hCH : C ≤ graphLocalGroup (family P) v) (hpA : IsPGroup 2 A) (hpC : IsPGroup 2 C)
    (hiA : (Q (family P) v).relIndex A = Nat.card F)
    (hiC : (Q (family P) v).relIndex C = Nat.card F)
    (hAx : A ≤ stabilizer (family P) x) (hCy : C ≤ stabilizer (family P) y) :
    graphLocalGroup (family P) v = Q (family P) v ⊔ A ⊔ C := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let J := Q Γ v ⊔ A ⊔ C
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q Γ v := hk ▸ graphLocalGroup_core h v
  obtain ⟨T,hT⟩ := linear_full_image h v e A hAH hpA hiA
  obtain ⟨U,hU⟩ := linear_full_image h v e C hCH hpC hiC
  change (A.subgroupOf H).map q = T at hT
  change (C.subgroupOf H).map q = U at hU
  have hneTU : T ≠ U := by
    intro he
    have hAC : A ≤ C ⊔ Q Γ v := by
      have hm := congrArg (Subgroup.comap q) (hT.trans (he ▸ hU.symm))
      rw [Subgroup.comap_map_eq,Subgroup.comap_map_eq] at hm
      intro a ha
      have hm' : (⟨a,hAH ha⟩ : H) ∈ C.subgroupOf H ⊔ q.ker := by
        rw [←hm]
        exact (show A.subgroupOf H ≤ A.subgroupOf H ⊔ q.ker from le_sup_left) ha
      have ht := mem_map_of_mem H.subtype hm'
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCH,hkmap] at ht
      exact ht
    have hAy : A ≤ stabilizer Γ y := hAC.trans (sup_le hCy
      ((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge Γ hy).trans inf_le_right)))
    exact hne (linear_local_full_index_unique_neighbor h hB hS hx hy e A hAH hpA hiA hAx hAy).symm
  have hm : (J.subgroupOf H).map q = ⊤ := top_unique (by
    rw [←Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 T U hneTU]
    apply sup_le
    · rw [←hT]; exact map_mono (comap_mono (le_sup_right.trans le_sup_left))
    · rw [←hU]; exact map_mono (comap_mono le_sup_right))
  have hkJ : q.ker ≤ J.subgroupOf H := by
    intro a ha
    exact (show Q Γ v ≤ J from le_sup_left.trans le_sup_left)
      (hkmap ▸ mem_map_of_mem H.subtype ha)
  have hJtop : J.subgroupOf H = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hm
    simpa only [comap_map_eq_self hkJ,Subgroup.comap_top] using hh
  apply le_antisymm
  · intro a ha
    exact (show (⟨a,ha⟩ : H) ∈ J.subgroupOf H by rw [hJtop]; trivial)
  · exact sup_le (sup_le (core_le_graphLocalGroup h v) hAH) hCH


private theorem linear_full_index_of_contains
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A W : Subgroup G) (hAW : A ≤ W) (hWH : W ≤ graphLocalGroup (family P) v)
    (hpW : IsPGroup 2 W) (hi : (Q (family P) v).relIndex A = Nat.card F) :
    (Q (family P) v).relIndex W = Nat.card F := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  obtain ⟨T,hT⟩ := linear_full_image h v e A (hAW.trans hWH) (hpW.to_le hAW) hi
  change (A.subgroupOf H).map q = T at hT
  have hTW : (T : Subgroup SL(2,F)) ≤ (W.subgroupOf H).map q := by
    rw [←hT]; exact map_mono (comap_mono hAW)
  have he : (W.subgroupOf H).map q = T :=
    T.3 (hpW.comap_subtype.map q) hTW
  have hc := congrArg (fun D : Subgroup SL(2,F) => Nat.card D) he
  rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
    hkmap,map_subgroupOf_eq_of_le hWH] at hc
  exact hc.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).symm

private theorem spans_commute_of_distance
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (v w : Vertex (family P)) (r s : ℕ)
    (hd : (graph (family P)).dist v w + r + s < b (family P)) :
    ⁅V (family P) v r,V (family P) w s⁆ = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply le_centralizer_iff.mp
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hx' := (mem_ball_iff Γ h.generate v x r).mp hx
  have hy' := (mem_ball_iff Γ h.generate w y s).mp hy
  have ht := (connected Γ h.generate).dist_triangle (u := y) (v := w) (w := x)
  have ht' := (connected Γ h.generate).dist_triangle (u := w) (v := v) (w := x)
  rw [SimpleGraph.dist_comm (u := y) (v := w)] at ht
  rw [SimpleGraph.dist_comm (u := w) (v := v)] at ht'
  exact short_centers_commute Γ (fun z => (source_Z_Q_U h z).1)
    (source_kernel_sylow h hB hS) y x (by change (graph Γ).dist v w + r + s < b Γ at hd; omega)

/-- The actual linear markings and source 6.5 make every two-edge rooted path transitive. -/
theorem linear_root_two_path_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eα : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hpath : CriticalPathOrbit (family P) a') (v : Vertex (family P)) :
    RootPathTransitive (graph (family P)) G v 2 := by
  obtain ⟨s,hs,hshort,htrans,⟨x,p,hp,hbad⟩,_⟩ := hpath
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hnot : ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val := by
    intro hh
    apply hbad
    intro x y hx hy
    exact hh ⟨x,hx.1⟩ ⟨y,hy.1⟩ hx.2 hy.2
  have hcore : (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint := by
    by_cases ht : a.type = p.endpoint.type
    · obtain ⟨g,hg⟩ := (same_orbit_iff (family P) a p.endpoint).mpr ht
      obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
      exact source_path_core_le_endpoint_core h hB hS (source_rankOne_branching h)
        (htrans _ _ le_rfl) p hp (f.symm.trans eα) hnot
    · have ht' : beta.type = p.endpoint.type := by
        have hh := hab.1
        cases ha : a.type <;> cases hb : beta.type <;> cases he : p.endpoint.type <;> simp_all
      obtain ⟨g,hg⟩ := (same_orbit_iff (family P) beta p.endpoint).mpr ht'
      obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
      exact source_path_core_le_endpoint_core h hB hS (source_rankOne_branching h)
        (htrans _ _ le_rfl) p hp (f.symm.trans eβ) hnot
  have hfour := source_path_length_ge_four_of_core h hB p hp hcore hob
  exact htrans v 2 (by omega)


/-- Move the radius-two span along the actual two-edge path. The moved span
centralizes the terminal neighborhood span by the global critical-distance bound. -/
theorem radius_two_conjugate_centralizes
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a a' v w : Vertex (family P)}
    (hc : (graph (family P)).dist a a' = b (family P))
    (hb : 4 < b (family P))
    (hv : (graph (family P)).Adj a' v) (hw : (graph (family P)).Adj v w)
    (hdv : (graph (family P)).dist a v + 1 = b (family P))
    (hdw : (graph (family P)).dist a w + 2 = b (family P))
    (htrans : RootPathTransitive (graph (family P)) G w 2) :
    ∃ r : Vertex (family P), (graph (family P)).Adj w r ∧ r ≠ v ∧
      V (family P) a 2 ≤ stabilizer (family P) r ∧
      ∃ g : G, g • w = w ∧ g • r = v ∧
        ⁅V (family P) a' 1,(V (family P) a 2).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  change (graph Γ).dist a a' = b Γ at hc
  change 4 < b Γ at hb
  change (graph Γ).dist a v + 1 = b Γ at hdv
  change (graph Γ).dist a w + 2 = b Γ at hdw
  have hne : a ≠ w := by intro he; rw [he,SimpleGraph.dist_self] at hdw; omega
  obtain ⟨r,hr,hrd⟩ := exists_predecessor Γ h.generate a w hne
  have hne' : a ≠ r := by
    intro he
    have hh : (graph Γ).dist a r = 0 := by rw [he,SimpleGraph.dist_self]
    rw [hh] at hrd
    omega
  obtain ⟨z,hz,hzd⟩ := exists_predecessor Γ h.generate a r hne'
  have hrne : r ≠ v := by intro he; rw [he] at hrd; omega
  have hzw : z ≠ w := by intro he; rw [he] at hzd; omega
  have ha'w : a' ≠ w := by intro he; rw [he] at hc; omega
  let p : BasedWalk (graph Γ) 2 w := ⟨⟨r,hr⟩,⟨⟨z,hz⟩,PUnit.unit⟩⟩
  let q : BasedWalk (graph Γ) 2 w := ⟨⟨v,hw.symm⟩,⟨⟨a',hv.symm⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := by exact ⟨hzw,True.intro⟩
  have hq : q.Nonbacktracking := by exact ⟨ha'w,True.intro⟩
  obtain ⟨g,hgw,hg⟩ := htrans p q hp hq
  change [g • w,g • r,g • z] = [w,v,a'] at hg
  have hgr : g • r = v := (List.cons.inj (List.cons.inj hg).2).1
  have hgz : g • z = a' := (List.cons.inj (List.cons.inj (List.cons.inj hg).2).2).1
  refine ⟨r,hr,hrne,V_le_stabilizer Γ h.generate a r (by omega),g,hgw,hgr,?_⟩
  rw [←V_translate]
  apply spans_commute_of_distance h hB hS
  have hdist : (graph Γ).dist a' (g • a) = (graph Γ).dist a z := by
    rw [←hgz,Subgroup.CosetGeometry.RankTwo.dist_smul,SimpleGraph.dist_comm]
  change (graph Γ).dist a' (g • a) + 1 + 2 < b Γ
  rw [hdist]
  omega


private theorem neighbor_span_le_two
    (h : LocallyRankOneTriple P B) {a t : Vertex (family P)}
    (hat : (graph (family P)).Adj a t) : V (family P) t 1 ≤ V (family P) a 2 := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  have hz' := (mem_ball_iff (family P) h.generate t z 1).mp hz
  have ht := (connected (family P) h.generate).dist_triangle (u := a) (v := t) (w := z)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hat] at ht
  exact le_iSup_of_le z (le_iSup_of_le
    ((mem_ball_iff (family P) h.generate a z 2).mpr (by omega)) le_rfl)

private theorem commutator_normalized_of_centralizer_supplement
    (H N R : Subgroup G) (hN : H ≤ normalizer (N : Set G))
    (hgen : H = (H ⊓ centralizer (R : Set G)) ⊔ N) :
    H ≤ normalizer (⁅R,N⁆ : Subgroup G) := by
  apply hgen.le.trans
  apply sup_le ?_ (normalizer_commutator_ge_right R N)
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp ((centralizer_le_normalizer (R : Set G)) hg.2),
    mem_normalizer_iff_map_conj_eq.mp (hN hg.1)]

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The centralizer supplement in the large-distance proof of 9.8. Both
full quotient actors are constructed from the actual radius-two span. -/
theorem reduced_linear_commutator_centralizer_supplement
    (h : HypothesisF11 L S₀)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' v w : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,K))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hi : (Q (Reduction.reducedFamily L S₀) a').relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) = Nat.card F)
    (hi' : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (hpath : CriticalPathOrbit (Reduction.reducedFamily L S₀) a')
    (hv : (graph (Reduction.reducedFamily L S₀)).Adj a' v)
    (hw : (graph (Reduction.reducedFamily L S₀)).Adj v w)
    (hdv : (graph (Reduction.reducedFamily L S₀)).dist a v + 1 = b (Reduction.reducedFamily L S₀))
    (hdw : (graph (Reduction.reducedFamily L S₀)).dist a w + 2 = b (Reduction.reducedFamily L S₀)) :
    let Γ := Reduction.reducedFamily L S₀
    let R := ⁅V Γ beta 1,V Γ a' 1⁆
    let W := V Γ a 2
    let H := graphLocalGroup Γ w
    ∃ ew : (H ⧸ pCore 2 H) ≃* SL(2,F), NaturalResidualSection h w ew n ∧
      (Q Γ w).relIndex W = Nat.card F ∧
      (∃ g : Reduction.G₀ L S₀, g • w = w ∧
        ⁅V Γ a' 1,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        H = Q Γ w ⊔ W ⊔ W.map (MulAut.conj g).toMonoidHom) ∧
      H = (H ⊓ centralizer (R : Set (Reduction.G₀ L S₀))) ⊔ Q Γ w ∧
      H ≤ normalizer (⁅R,Q Γ w⁆ : Subgroup (Reduction.G₀ L S₀)) ∧
      ⁅R,Q Γ w⁆ ≤ Q Γ w := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hZ := fun z => (source_Z_Q_U ht z).1
  have hSyl := Reduction.reduced_kernel_sylow h
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  obtain ⟨hodd,_,_,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  have hb4 : 4 < b Γ := by
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    change 3 < b Γ at hb
    omega
  obtain ⟨hW,_,hRW,t,z,hat,_,_,_,_,_,_,et,ew,_,_,hit,_,_,hnatw⟩ :=
    reduced_linear_shifted_sections h h8 hob hc hab hd hb hcomm hn hF eα eβ hi hi' hpath hv hw hdv hdw
  let W := V Γ a 2
  let R := ⁅V Γ beta 1,V Γ a' 1⁆
  let H := graphLocalGroup Γ w
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer Γ a)).to_le
    (V_le_Q Γ ht.generate hZ hSyl a (r := 2) (by omega))
  have hiW : (Q Γ w).relIndex W = Nat.card F :=
    linear_full_index_of_contains ht w ew (V Γ t 1) W (neighbor_span_le_two ht hat) hW hpW hit
  obtain ⟨r,hr,hrne,hWr,g,hgw,hgr,hgcentral⟩ := radius_two_conjugate_centralizes ht hB hS
    hc.1 hb4 hv hw hdv hdw (linear_root_two_path_transitive ht hB hS hab hob eα eβ hpath w)
  change (g • w : Vertex Γ) = w at hgw
  change (g • r : Vertex Γ) = v at hgr
  change W ≤ stabilizer Γ r at hWr
  let f := (MulAut.conj g).toMonoidHom
  have hWgH : W.map f ≤ H := by
    have hh := graphLocalGroup_conjugate ht g w
    change graphLocalGroup Γ (g • w) = H.map f at hh
    rw [hgw] at hh
    exact (map_mono hW).trans_eq hh.symm
  have hiWg : (Q Γ w).relIndex (W.map f) = Nat.card F := by
    have hh := relIndex_map_map_of_injective (Q Γ w) W
      (f := f) (MulAut.conj g).injective
    change (Subgroup.map f (Q Γ w)).relIndex (W.map f) = (Q Γ w).relIndex W at hh
    rw [←Q_translate,hgw,hiW] at hh
    exact hh
  have hWgv : W.map f ≤ stabilizer Γ v := by
    have hh := stabilizer_translate Γ g r
    change stabilizer Γ (g • r) = (stabilizer Γ r).map f at hh
    rw [hgr] at hh
    exact (map_mono hWr).trans_eq hh.symm
  have hgen : H = Q Γ w ⊔ W ⊔ W.map f := linear_local_two_actor_generation ht hB hS
    hr hw.symm hrne ew W (W.map f) hW hWgH hpW (hpW.map f) hiW hiWg hWr hWgv
  refine ⟨ew,hnatw,hiW,⟨g,hgw,hgcentral,hgen⟩,?_⟩
  have hRA' : R ≤ V Γ a' 1 := le_normalizer_iff_commutator_le_right.mp
    ((V_le_stabilizer Γ ht.generate beta a' hd.le).trans (stabilizer_normalizes_V Γ a' 1))
  have hWC : W ≤ centralizer (R : Set (Reduction.G₀ L S₀)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hRW)
  have hWgC : W.map f ≤ centralizer (R : Set (Reduction.G₀ L S₀)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hgcentral)).trans
      (centralizer_le hRA')
  have hsupp : H = (H ⊓ centralizer (R : Set (Reduction.G₀ L S₀))) ⊔ Q Γ w := by
    apply le_antisymm
    · exact hgen.le.trans (sup_le (sup_le le_sup_right ((le_inf hW hWC).trans le_sup_left))
        ((le_inf hWgH hWgC).trans le_sup_left))
    · exact sup_le inf_le_left (core_le_graphLocalGroup ht w)
  have hnQ : H ≤ normalizer (Q Γ w : Set (Reduction.G₀ L S₀)) :=
    (sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ w)
  have hA'H : V Γ a' 1 ≤ H := by
    apply span_le_localGroup_of_distance ht
    have hh := (connected Γ ht.generate).dist_triangle (u := a') (v := v) (w := w)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hv,SimpleGraph.dist_eq_one_iff_adj.mpr hw] at hh
    change (graph Γ).dist a' w + 1 ≤ b Γ
    omega
  exact ⟨hsupp,commutator_normalized_of_centralizer_supplement H (Q Γ w) R hnQ hsupp,
    le_normalizer_iff_commutator_le_right.mp ((hRA'.trans hA'H).trans hnQ)⟩

/-- Original F1.11 application of the large-distance centralizer supplement.
The two quotient markings and both original natural sections are constructed;
Chapter 8 discharges the zero-displacement premises at distance greater than three. -/
theorem reduced_critical_commutator_centralizer_supplement
    (h : HypothesisF11 L S₀)
    {a beta a' v w : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (hv : (graph (Reduction.reducedFamily L S₀)).Adj a' v)
    (hw : (graph (Reduction.reducedFamily L S₀)).Adj v w)
    (hdv : (graph (Reduction.reducedFamily L S₀)).dist a v + 1 = b (Reduction.reducedFamily L S₀))
    (hdw : (graph (Reduction.reducedFamily L S₀)).dist a w + 2 = b (Reduction.reducedFamily L S₀)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧ NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            (let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
             letI : Algebra (ZMod 2) K := ZMod.algebra K 2
             ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
               (T : Sylow 2 SL(2,K)),
               (∀ (l : H) (z : Additive (Z Γ a)),
                 ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                   (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
               Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
               ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                 ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ ew : (graphLocalGroup Γ w ⧸ pCore 2 (graphLocalGroup Γ w)) ≃* SL(2,F),
              NaturalResidualSection h w ew n ∧
              (Q Γ w).relIndex (V Γ a 2) = Nat.card F ∧
              (∃ g : Reduction.G₀ L S₀, g • w = w ∧
                ⁅V Γ a' 1,(V Γ a 2).map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
                graphLocalGroup Γ w = Q Γ w ⊔ V Γ a 2 ⊔
                  (V Γ a 2).map (MulAut.conj g).toMonoidHom) ∧
              graphLocalGroup Γ w = (graphLocalGroup Γ w ⊓
                centralizer ((⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀))) ⊔ Q Γ w ∧
              graphLocalGroup Γ w ≤ normalizer
                (⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ : Subgroup (Reduction.G₀ L S₀)) ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ ≤ Q Γ w := by
  let Γ := Reduction.reducedFamily L S₀
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥ := by
    by_contra he
    exact Nat.ne_of_gt hb (h8 a beta a' hc hab hd hb1 hcomm he)
  have hzero (z : Vertex Γ) (hz : (graph Γ).Adj z a')
      (hzc : IsCriticalPair Γ z beta) (hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥)
      (he : ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥) : False :=
    Nat.ne_of_gt hb (h8 z a' beta hzc hz
      (by rwa [SimpleGraph.dist_comm]) hb1 hzcomm he)
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,_,_,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,_,_,hi,hpath,hcQ,hcV,hnat⟩ :=
    reduced_critical_reciprocal_sections h hc hab hd hb1 hcomm htriv
      (fun z hz hzc hzcomm he => (hzero z hz hzc hzcomm he).elim) hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hres,K,instK,finK,charK,m,hm,hK,eα,
    heq,hcQ,hcV,hnat,reduced_linear_commutator_centralizer_supplement h h8 hob hc hab hd hb hcomm hn hF eα eβ
      hx hi hpath hv hw hdv hdw⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
