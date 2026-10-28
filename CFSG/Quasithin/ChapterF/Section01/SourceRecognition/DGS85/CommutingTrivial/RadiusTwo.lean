module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.RadiusTwoPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReciprocalEscape

/-!
# The unrestricted radius-two escape in the commuting-trivial branch

The actual indices and path-orbit implication from 9.3--9.6 prove 9.7:
W = V_alpha^(2) lies in L_(alpha'-2) and escapes Q_(alpha'-2).
In the short-path case, the terminal quotient index gives
W = V_beta (W intersect Q_alpha-prime). Its second factor centralizes
V_alpha-prime, so the reciprocal span normalizes W. Its full field index
and two distinct neighbors force the whole beta stabilizer to normalize W.
Faithfulness then contradicts the original critical center.

The original F1.11 consumer constructs both markings and all indices before
applying this argument. The genuine earlier catalogue, Chapter 8 and 6.5
inputs remain explicit. A generator escaping the second predecessor core
also constructs the shifted critical pair and its two new edges used by 9.8.
No distance-three or field-two conclusion is assumed.
Source: DGS, Groups and Graphs (1985), 9.7--9.8, printed pp.144--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Source 9.7 with the exact indices from 9.3 and 9.6: the radius-two span
lies in the second predecessor's local group and escapes its two-core. -/
theorem linear_radius_two_escape_at_predecessor
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' v w : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 2 < b (family P)) (hodd : Odd (b (family P)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hi : (Q (family P) a').relIndex (V (family P) beta 1) = Nat.card F)
    (hi' : (Q (family P) beta).relIndex (V (family P) a' 1) = Nat.card F)
    (hpath : CriticalPathOrbit (family P) a')
    (hv : (graph (family P)).Adj a' v) (hw : (graph (family P)).Adj v w)
    (hdv : (graph (family P)).dist a v + 1 = b (family P))
    (hdw : (graph (family P)).dist a w + 2 = b (family P)) :
    V (family P) a 2 ≤ graphLocalGroup (family P) w ∧
      ¬ V (family P) a 2 ≤ Q (family P) w := by
  let Γ := family P
  let := finite_endpoints h
  have hZ := fun z => (source_Z_Q_U h z).1
  have hSyl := source_kernel_sylow h hB hS
  change (graph Γ).dist a v + 1 = b Γ at hdv
  change (graph Γ).dist a w + 2 = b Γ at hdw
  refine ⟨span_le_localGroup_of_distance h a w hdw.le,?_⟩
  obtain ⟨n,hn⟩ : ∃ n, b Γ = n+3 := ⟨b Γ-3,by change 2 < b Γ at hb; omega⟩
  have hlen : (graph Γ).dist a w = n+1 := by omega
  obtain ⟨p,hp,hpe⟩ : ∃ p : BasedWalk (graph Γ) (n+1) a,
      p.Nonbacktracking ∧ p.endpoint = w := by
    rw [←hlen]
    exact BasedWalk.exists_geodesic ((connected Γ h.generate) a w)
  have hwp : (graph Γ).Adj p.endpoint v := hpe.symm ▸ hw.symm
  obtain ⟨s,hs,hshort,htrans,hbad,horbit⟩ := hpath
  intro htrap
  have htrap' : V Γ a 2 ≤ Q Γ p.endpoint := hpe.symm ▸ htrap
  by_cases hlong : b Γ ≤ s
  · exact radius_two_escape_of_long_path h hS hc hn hlong hshort p hwp hv.symm htrap'
  have hsb : s < b Γ := by omega
  obtain ⟨hWQ,hcentral⟩ := radius_two_trapped_path_centralizes h hB hS hc hn hsb
    (horbit hsb) p hwp hv.symm htrap'
  let W := V Γ a 2
  let A := V Γ beta 1
  let C := W ⊓ Q Γ a'
  have hWA : W ≤ Q Γ a := V_le_Q Γ h.generate hZ hSyl a (r := 2) hb
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer Γ a)).to_le hWA
  have hAW : A ≤ W := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    have hz' := (mem_ball_iff Γ h.generate beta z 1).mp hz
    have ht := (connected Γ h.generate).dist_triangle (u := a) (v := beta) (w := z)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab] at ht
    exact le_iSup_of_le z (le_iSup_of_le
      ((mem_ball_iff Γ h.generate a z 2).mpr (by omega)) le_rfl)
  have hat : a.type ≠ a'.type := (odd_dist_iff Γ h.generate a a').mp (hc.1.symm ▸ hodd)
  have hbt : beta.type = a'.type := by
    have hh := hab.1
    cases ha : a.type <;> cases hb : beta.type <;> cases ha' : a'.type <;> simp_all
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta a').mpr hbt
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
  have hWH : W ≤ graphLocalGroup Γ a' := hWQ.trans (neighbor_core_le_localGroup h hB hS hv)
  have hprod : W = A ⊔ C := linear_local_pgroup_saturation h a' (f.symm.trans eβ)
    A W hAW hWH hpW hi
  have hnd : V Γ a' 1 ≤ normalizer (W : Set G) := by
    rw [hprod]
    apply le_trans (le_inf ?_ ?_) (normalizer_inf_normalizer_le_normalizer_sup A C)
    · exact (V_le_stabilizer Γ h.generate a' beta
        (by rw [SimpleGraph.dist_comm]; exact hd.le)).trans (stabilizer_normalizes_V Γ beta 1)
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcentral)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hnA : stabilizer Γ a ≤ normalizer (W : Set G) := stabilizer_normalizes_V Γ a 2
  have hndβ : V Γ a' 1 ≤ stabilizer Γ beta := V_le_stabilizer Γ h.generate a' beta
    (by rw [SimpleGraph.dist_comm]; exact hd.le)
  have hnβ : stabilizer Γ beta ≤ normalizer (W : Set G) := by
    rcases source_edge_maximal h hab.symm
      (stabilizer Γ beta ⊓ normalizer (W : Set G))
      (le_inf inf_le_left (inf_le_right.trans hnA)) inf_le_left with he | he
    · exfalso
      have hDa : V Γ a' 1 ≤ stabilizer Γ a := (le_inf hndβ hnd).trans (he.le.trans inf_le_right)
      have hnβ' : a' ≠ beta := by
        intro heq
        have hh := hd
        rw [heq,SimpleGraph.dist_self] at hh
        omega
      obtain ⟨c,hcβ,hdc⟩ := exists_predecessor Γ h.generate a' beta hnβ'
      have hDc : V Γ a' 1 ≤ Q Γ c := by
        apply iSup_le
        intro z
        apply iSup_le
        intro hz
        apply Z_le_Q_of_dist_lt_b Γ hZ hSyl z c
        have hz' := (mem_ball_iff Γ h.generate a' z 1).mp hz
        have ht := (connected Γ h.generate).dist_triangle (u := z) (v := a') (w := c)
        rw [SimpleGraph.dist_comm (u := z) (v := a')] at ht
        have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
        omega
      have hDH := neighbor_le_graphLocalGroup h hSyl a' beta (by omega)
        (by rw [SimpleGraph.dist_comm]; exact hd.le)
      have hpD : IsPGroup 2 (V Γ a' 1) := (isPGroup_pCoreIn 2 (stabilizer Γ a')).to_le
        (V_le_Q Γ h.generate hZ hSyl a' (r := 1) (by omega))
      have hca : c = a := linear_local_full_index_unique_neighbor h hB hS hab.symm hcβ
        eβ (V Γ a' 1) hDH hpD hi' hDa (hDc.trans (Q_le_stabilizer Γ c))
      rw [hca,SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hdc
      change b Γ + 1 = (graph Γ).dist a' beta at hdc
      have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
      omega
    · exact he.ge.trans inf_le_right
  have hbot : W = ⊥ := CommutingNontrivial.source_normalized_edge_eq_bot h hab W
    (le_inf (hWA.trans (Q_le_stabilizer Γ a))
      (hWA.trans ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge Γ hab).trans inf_le_right))))
    (by intro z hz; obtain ⟨g,hg,hgz⟩ := locally_transitive Γ hab hz; exact ⟨g,hnA hg,hgz⟩)
    (by intro z hz; obtain ⟨g,hg,hgz⟩ := locally_transitive Γ hab.symm hz; exact ⟨g,hnβ hg,hgz⟩)
  exact hc.2 ((Z_le_V Γ a 2).trans (hbot.le.trans bot_le))

/-- Construct the last two predecessors and apply the unrestricted 9.7
escape on that literal critical geodesic. -/
theorem linear_radius_two_escape
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 2 < b (family P)) (hodd : Odd (b (family P)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hi : (Q (family P) a').relIndex (V (family P) beta 1) = Nat.card F)
    (hi' : (Q (family P) beta).relIndex (V (family P) a' 1) = Nat.card F)
    (hpath : CriticalPathOrbit (family P) a') :
    ∃ v w : Vertex (family P), (graph (family P)).Adj v a' ∧
      (graph (family P)).Adj w v ∧
      (graph (family P)).dist a v + 1 = b (family P) ∧
      (graph (family P)).dist a w + 2 = b (family P) ∧
      V (family P) a 2 ≤ graphLocalGroup (family P) w ∧
      ¬ V (family P) a 2 ≤ Q (family P) w := by
  let Γ := family P
  let := finite_endpoints h
  have hZ := fun z => (source_Z_Q_U h z).1
  have hSyl := source_kernel_sylow h hB hS
  have hne : a ≠ a' := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self] at hh
    omega
  obtain ⟨v,hv,hvd⟩ := exists_predecessor Γ h.generate a a' hne
  have hdv : (graph Γ).dist a v + 1 = b Γ := hvd.trans hc.1
  have hne' : a ≠ v := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdv
    change 2 < b Γ at hb
    omega
  obtain ⟨w,hw,hwd⟩ := exists_predecessor Γ h.generate a v hne'
  have hdw : (graph Γ).dist a w + 2 = b Γ := by omega
  obtain ⟨hW,heW⟩ := linear_radius_two_escape_at_predecessor h hB hS hc hab hd hb hodd
    eβ hi hi' hpath hv hw hdv hdw
  exact ⟨v,w,hv.symm,hw.symm,hdv,hdw,hW,heW⟩


/-- An escaping radius-two span supplies an actual shifted critical pair,
with the two new edges and all exact distances retained. This is the
critical-pair input to the b > 3 argument of 9.8. -/
theorem radius_two_escape_critical_extension
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a w : Vertex (family P)}
    (hd : (graph (family P)).dist a w + 2 = b (family P))
    (he : ¬ V (family P) a 2 ≤ Q (family P) w) :
    ∃ t z : Vertex (family P), (graph (family P)).Adj a t ∧
      (graph (family P)).Adj t z ∧ (graph (family P)).dist a z = 2 ∧
      IsCriticalPair (family P) z w := by
  let Γ := family P
  let := finite_endpoints h
  have hZ := fun v => (source_Z_Q_U h v).1
  have hSyl := source_kernel_sylow h hB hS
  obtain ⟨z,hz,hzQ⟩ : ∃ z, z ∈ ball Γ a 2 ∧ ¬ Z Γ z ≤ Q Γ w := by
    by_contra! hall
    apply he
    exact iSup_le fun z => iSup_le fun hz => hall z hz
  let := Z_elementary Γ hZ z
  have hzU : ¬ Z Γ z ≤ U Γ w := fun hh => hzQ
    (two_subgroup_le_Q Γ w (hSyl w) (IsElementaryAbelian.isPGroup 2 _) hh)
  have hmin : b Γ ≤ (graph Γ).dist z w := Nat.sInf_le ⟨z,w,rfl,hzU⟩
  have htri := (connected Γ h.generate).dist_triangle (u := z) (v := a) (w := w)
  rw [SimpleGraph.dist_comm (u := z) (v := a)] at htri
  have haz := (mem_ball_iff Γ h.generate a z 2).mp hz
  change (graph Γ).dist a w + 2 = b Γ at hd
  have haz2 : (graph Γ).dist a z = 2 := by omega
  have hzw : (graph Γ).dist z w = b Γ := by omega
  have hne : a ≠ z := by intro hh; rw [hh,SimpleGraph.dist_self] at haz2; omega
  obtain ⟨t,ht,hdt⟩ := exists_predecessor Γ h.generate a z hne
  have hat : (graph Γ).Adj a t := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  exact ⟨t,z,hat,ht.symm,haz2,hzw,hzU⟩


universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- Apply 9.7 to the actual source graph in both initial-recognition branches,
and construct the shifted critical pair used in 9.8. Earlier source inputs
are exactly those of the recognized-sections theorem. -/
theorem reduced_critical_radius_two_escape
    (h : HypothesisF11 L S₀)
    {a beta a' v w : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))
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
    V Γ a 2 ≤ graphLocalGroup Γ w ∧ (¬ V Γ a 2 ≤ Q Γ w) ∧
      ∃ t z : Vertex Γ, (graph Γ).Adj a t ∧ (graph Γ).Adj t z ∧
        (graph Γ).dist a z = 2 ∧ IsCriticalPair Γ z w := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,he,hrev,hi,hpath,hcQ,hcV,hnat⟩ :=
    reduced_critical_reciprocal_sections h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  obtain ⟨hodd,hb3,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hb2 : 2 < b (Reduction.reducedFamily L S₀) := Nat.lt_of_lt_of_le (by decide) hb3
  obtain ⟨hW,heW⟩ := linear_radius_two_escape_at_predecessor ht hB hS hc hab hd hb2 hodd
    eβ hx hi hpath hv hw hdv hdw
  exact ⟨hW,heW,radius_two_escape_critical_extension ht hB hS hdw heW⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
