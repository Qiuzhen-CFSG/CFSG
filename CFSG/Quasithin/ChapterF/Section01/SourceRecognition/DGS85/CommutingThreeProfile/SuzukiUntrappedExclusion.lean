module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiThreePathExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NinePathUntrappedCentralizer
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NinePathUntrappedCentralizer
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiEscapingCentralizer

/-!
# Excluding the untrapped centralizer on the source nine-path

Two remote critical centers generate the Suzuki star at the fifth
vertex modulo its core. This constructs, inside the centralizer of the
actual path two-subgroup, the required transitive neighborhood action.
The previously proved untrapped propagation centralizes the spans at
both the third and fifth vertices.

The middle core transports a moved center of the nonzero branch
commutator to the selected linear neighbor. The existing (12.3)(a)
calculation then gives the first second index, and the constructed
three-path exchange gives the other. Conjugators in the actual
centralizer place these full root images at distinct neighbors of the
intervening linear vertex. Their join is transitive there, so faithful
graph normalizer propagation (3.2)(c) kills the original path element.

Consequently every nonidentity two-element lies in the trapped case;
the last theorem also proves that containment after the original
completion inclusion, with the literal singleton centralizer. The
common Sylows, shared parameter, critical placements and nonzero branch
commutator remain genuine earlier source inputs. No index, transitivity,
center-movement or centralization conclusion is an extra hypothesis.

This completes the nonbinary untrapped case of (12.7). Its trapped case,
the odd-order path bound, Suzuki selection, binary alternatives, full
kernel conclusions and final (12.8)--(12.9)/(13.1) premise discharge
remain obligations of this source family. Implementation imports reuse
private coordinate and orbit lemmas without widening their public APIs.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7), printed p.184, using (3.2)(c), (12.3)(a), (12.4)(b), and (12.5).
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem interior_center_transitivity
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T₀ : Sylow 2 (star L S i))
    (hT₀ : (T₀ : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {v2 v3 v4 v5 v6 v7 v8 : Vertex (reducedFamily L S)}
    (h23 : (graph (reducedFamily L S)).Adj v2 v3)
    (h34 : (graph (reducedFamily L S)).Adj v3 v4)
    (h45 : (graph (reducedFamily L S)).Adj v4 v5)
    (h56 : (graph (reducedFamily L S)).Adj v5 v6)
    (h67 : (graph (reducedFamily L S)).Adj v6 v7)
    (h78 : (graph (reducedFamily L S)).Adj v7 v8)
    (hne64 : v6 ≠ v4) (htype : v5.type = i)
    (hca : IsCriticalPair (reducedFamily L S) v2 v5)
    (hcc : IsCriticalPair (reducedFamily L S) v8 v5)
    (D : Subgroup (G₀ L S))
    (hD2 : D ≤ Q (reducedFamily L S) v2)
    (hD4 : D ≤ Q (reducedFamily L S) v4)
    (hD5 : D ≤ Q (reducedFamily L S) v5)
    (hD8 : D ≤ Q (reducedFamily L S) v8) :
    ∀ v, (graph (reducedFamily L S)).Adj v5 v →
      ∃ a ∈ stabilizer (reducedFamily L S) v5 ⊓ centralizer (D : Set (G₀ L S)), a • v4 = v := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hcommon := common_sylow_neighbors h i T₀ hT₀
  have ht4 : v4.type = !i := Bool.eq_not_iff.mpr (htype ▸ h45.1)
  obtain ⟨g,hg4,hg5⟩ := incident_common_translate F h45.2
  rw [ht4] at hg4
  rw [htype] at hg5
  let c := (MulAut.conj g⁻¹).toMonoidHom
  have hm : g⁻¹ • v4 = base F (!i) := by rw [←hg4,inv_smul_smul]
  have hy : g⁻¹ • v5 = base F i := by rw [←hg5,inv_smul_smul]
  have hca' : IsCriticalPair F (g⁻¹ • v2) (base F i) := by
    simpa only [hy] using criticalPair_translate F hca g⁻¹
  have hcc' : IsCriticalPair F (g⁻¹ • v8) (base F i) := by
    simpa only [hy] using criticalPair_translate F hcc g⁻¹
  have ha {u v : Vertex F} (huv : (graph F).Adj u v) :
      (graph F).Adj (g⁻¹ • u) (g⁻¹ • v) :=
    (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr huv
  have hy6 : (graph F).Adj (base F i) (g⁻¹ • v6) := by simpa only [hy] using ha h56
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨R,hR⟩ := hcommon _ hy6
  have hia := source_suzuki_critical_center_index h i hb hca' (ha h23.symm)
    (by simpa only [hm] using ha h34) hadj hn eSuz eLin T₀ hT₀
  have hic := source_suzuki_critical_center_index h i hb hcc' (ha h78)
    (ha h67.symm) hy6 hn eSuz eLin R hR
  have hZn (u v : Vertex F) (hd : (graph F).dist u v ≤ 2) : Z F u ≤ Q F v :=
    CommutingNontrivial.Z_le_Q_of_dist_lt_b F (fun v => (source_Z_Q_U (reduced_triple h) v).1)
      u v (lt_of_le_of_lt hd hb) (reduced_kernel_sylow h v)
  have hZa : Z F (g⁻¹ • v2) ≤ Q F (base F (!i)) := by
    have hh := map_mono (f := c) (hZn v2 v4
      (SimpleGraph.dist_le (SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34 .nil))))
    change (Z F v2).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (Q F v4).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Z_translate F,←Q_translate F,hm] at hh
  have hZc : Z F (g⁻¹ • v8) ≤ Q F (g⁻¹ • v6) := by
    have hh := map_mono (f := c) (hZn v8 v6
      (SimpleGraph.dist_le (SimpleGraph.Walk.cons h78.symm (SimpleGraph.Walk.cons h67.symm .nil))))
    change (Z F v8).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (Q F v6).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Z_translate F,←Q_translate F] at hh
  have hDq (v : Vertex F) (hv : D ≤ Q F v) :
      D.map c ≤ Q F (g⁻¹ • v) := by
    have hh := map_mono (f := c) hv
    change D.map c ≤ (Q F v).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Q_translate F] at hh
  have hDy : D.map c ≤ Q F (base F i) := by simpa only [hy] using hDq v5 hD5
  have hDm : D.map c ≤ Q F (base F (!i)) := by simpa only [hm] using hDq v4 hD4
  have hCa : Z F (g⁻¹ • v2) ≤ centralizer (D.map c : Set (G₀ L S)) :=
    (Z_centralizes_Q F _ (source_Z_Q_U (reduced_triple h) _).1).trans
      (centralizer_le (hDq v2 hD2))
  have hCc : Z F (g⁻¹ • v8) ≤ centralizer (D.map c : Set (G₀ L S)) :=
    (Z_centralizes_Q F _ (source_Z_Q_U (reduced_triple h) _).1).trans
      (centralizer_le (hDq v8 hD8))
  have hne : g⁻¹ • v6 ≠ base F (!i) := by
    rw [←hm]
    exact fun he => hne64 ((MulAction.injective g⁻¹) he)
  have hgen := (source_suzuki_remote_center_pair h i hn eSuz hy6 hne T₀ R hT₀ hR
    hZa hZc hia hic).1
  let E := Z F (g⁻¹ • v2) ⊔ Z F (g⁻¹ • v8)
  have hEC : E ≤ centralizer (D.map c : Set (G₀ L S)) := sup_le hCa hCc
  have hEP : E ≤ star L S i := le_sup_left.trans hgen.le
  intro v hv
  have hv' : (graph F).Adj (base F i) (g⁻¹ • v) := by
    simpa only [hy] using ha hv
  obtain ⟨a,haE,hea⟩ := star_supplement_transitive h i E hgen hv'
  have hafix : a • base F i = base F i := star_le_stabilizer i (hEP haE)
  have hact : c (g * a * g⁻¹) = a := by
    change g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a
    group
  refine ⟨g * a * g⁻¹,⟨?_,?_⟩,?_⟩
  · change (g * a * g⁻¹) • v5 = v5
    rw [mul_smul,mul_smul,hy,hafix,hg5]
  · intro d hd
    apply (MulAut.conj g⁻¹).injective
    change c (d * (g * a * g⁻¹)) = c ((g * a * g⁻¹) * d)
    rw [map_mul c d (g * a * g⁻¹),map_mul c (g * a * g⁻¹) d,hact]
    exact hEC haE (c d) (mem_map_of_mem c hd)
  · rw [mul_smul,mul_smul,hm,hea,smul_inv_smul]

set_option backward.isDefEq.respectTransparency false in
/-- In the nonbinary untrapped case the actual nine-path two-element is
identity. Both second indices and the two local centralizer actions are
constructed from the retained earlier source inputs. -/
theorem source_suzuki_nine_path_untrapped_eq_one
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T₀ : Sylow 2 (star L S i))
    (hT₀ : (T₀ : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hq : Nat.card k = 2^(2*n+1))
    (Tlin : Sylow 2 (star L S (!i)))
    (hTlin : (Tlin : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hca : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hcc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p)
    (t : G₀ L S) (ht : t ∈ D)
    (hesc : ¬ V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1 ⊓
      centralizer ({t} : Set (G₀ L S)) ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hbranch : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) i),
      V (reducedFamily L S) (base (reducedFamily L S) i) 1⁆ ≠ ⊥) : t = 1 := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let c : Vertex F := p.2.2.2.2.2.1
  let C := centralizer ({t} : Set (G₀ L S))
  have hcore := source_mixed_path_two_subgroup_core h (!i) eLin
    (by cases i <;> exact eSuz) p hp D hD hfix
  have htype : w.type = i := by
    have h3 : (p.2.2.1 : Vertex F).type = i := congrArg Subgroup.CosetGeometry.Vertex.type hy
    have h4 : i ≠ z.type := h3 ▸ p.2.2.2.1.property.1
    exact (Bool.eq_not_iff.mpr p.2.2.2.2.1.property.1.symm).trans (Bool.not_eq_iff.mpr h4.symm)
  have hzy : (graph F).Adj z y := by
    have hh : (graph F).Adj z (p.2.2.1 : Vertex F) := p.2.2.2.1.property.symm
    simpa only [hy] using hh
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwc : (graph F).Adj w c := p.2.2.2.2.2.1.property
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have hzn : z ≠ m := by simpa only [hm] using hp.2.2.1
  have hlocal := interior_center_transitivity h i hb hn eSuz eLin T₀ hT₀
    p.2.2.1.property p.2.2.2.1.property p.2.2.2.2.1.property
    p.2.2.2.2.2.1.property p.2.2.2.2.2.2.1.property p.2.2.2.2.2.2.2.1.property
    hp.2.2.2.2.1 htype hca hcc D
    (hcore _ (by simp [SimpleGraph.BasedWalk.vertices]))
    (hcore _ (by simp [SimpleGraph.BasedWalk.vertices]))
    (hcore _ (by simp [SimpleGraph.BasedWalk.vertices]))
    (hcore _ (by simp [SimpleGraph.BasedWalk.vertices]))
  have hlocalC : ∀ v, (graph F).Adj w v → ∃ a ∈ stabilizer F w ⊓ C, a • z = v := by
    intro v hv
    obtain ⟨a,ha,he⟩ := hlocal v hv
    exact ⟨a,⟨ha.1,mem_centralizer_singleton_iff.mpr (ha.2 t ht).symm⟩,he⟩
  have hVW : V F w 1 ≤ C := by
    have hh := (source_suzuki_nine_path_span_centralizer_at h i hb hn eSuz eLin T₀ hT₀
      p hp htype hca hcc D hD hfix).1
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hh ha t ht).symm
  obtain ⟨htrans,hVY,_⟩ := source_suzuki_nine_path_untrapped_span h i hb hn eSuz eLin T₀ hT₀
    p hp hm hy hca hcc hc D hD hfix t ht hesc
  obtain ⟨a,ha,hac⟩ := hlocalC c hwc
  obtain ⟨b,hbE,hbm⟩ := htrans z hzy.symm
  have hbC : b ∈ C := (sup_le inf_le_right hVW) hbE
  have hqm : Q F m ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) m).2.trans
      (ballKernel_one_le_edge F (show (graph F).Adj m y from
        ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩))).trans inf_le_right
  have hqz : Q F z ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) z).2.trans (ballKernel_one_le_edge F hzy)).trans inf_le_right
  have hxm : (graph F).Adj (p.1 : Vertex F) m := by
    have hh : (graph F).Adj (p.1 : Vertex F) (p.2.1 : Vertex F) := p.2.1.property
    simpa only [hm] using hh
  have hXQ := V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hxm
  have hWQ := V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hzw.symm
  have hby : b • y = y := (sup_le (inf_le_left.trans (hXQ.trans hqm)) (hWQ.trans hqz)) hbE
  obtain ⟨R,hR⟩ := common_sylow_neighbors h i T₀ hT₀ z hzy.symm
  have hstar : V F w 1 ⊓ Q F y ≤ star L S (!i) :=
    inf_le_right.trans ((le_sup_left.trans hTlin.ge).trans (map_subtype_le _))
  have hmove := source_suzuki_intersection_moves_other_center h i hb hn eSuz T₀ hT₀
    hzw.symm hzy.symm hzn hbranch
  obtain ⟨_,hiW',_,_⟩ := source_suzuki_second_index h i hb hzw.symm hzy.symm hzn
    hn hq eSuz T₀ R hT₀ hR eLin hstar hmove
  have hiW : (Q F m).relIndex (V F w 1 ⊓ Q F y) = Nat.card k := by
    have he : (V F w 1 ⊓ Q F m).subgroupOf (V F w 1 ⊓ Q F y) =
        (Q F m).subgroupOf (V F w 1 ⊓ Q F y) := by
      ext g
      exact and_iff_right g.property.1
    change ((Q F m).subgroupOf (V F w 1 ⊓ Q F y)).index = Nat.card k
    rw [←he]
    exact hiW'.trans hq.symm
  have hiY : (Q F c).relIndex (V F y 1 ⊓ Q F w) = Nat.card k :=
    (source_suzuki_second_index_exchange h i hn eSuz eLin T₀ hT₀ hzy.symm hzw.symm hwc
      hzn hwy hp.2.2.2.2.1).trans hiW
  have hlinear := source_linear_conjugate_intersections_transitive h (!i) eLin Tlin
    (by simpa only [Bool.not_not] using hTlin)
    (Bool.eq_not_iff.mpr (by simpa only [htype] using hzw.1)) hzy hzw hwy hiY hiW
    a⁻¹ b ((stabilizer F w).inv_mem ha.1) (inv_smul_eq_iff.mpr hac.symm) hby hbm
  have hmap (A : Subgroup (G₀ L S)) (hAC : A ≤ C) (g : G₀ L S) (hg : g ∈ C) :
      A.map (MulAut.conj g).toMonoidHom ≤ C := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hAC
    have he : C.map (MulAut.conj g).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer hg)
    exact hh.trans he.le
  have hlinearC : ∀ v, (graph F).Adj z v → ∃ g ∈ C, g • w = v := by
    intro v hv
    obtain ⟨g,hg,he⟩ := hlinear v hv
    exact ⟨g,(sup_le (inf_le_left.trans (hmap _ hVY _ (C.inv_mem ha.2)))
      (inf_le_left.trans (hmap _ hVW _ hbC))) hg,he⟩
  have hCN : C ≤ normalizer (zpowers t : Set (G₀ L S)) := by
    rw [zpowers_eq_closure]
    exact (show C ≤ centralizer (closure ({t} : Set (G₀ L S)) : Set (G₀ L S)) by
      rw [centralizer_closure]).trans (Subgroup.centralizer_le_normalizer _)
  have htz : t ∈ Q F z := hcore _ (by simp [SimpleGraph.BasedWalk.vertices,z]) ht
  have htw : t ∈ Q F w := hcore _ (by simp [SimpleGraph.BasedWalk.vertices,w]) ht
  have hbot := source_normalized_edge_eq_bot (reduced_triple h) hzw (zpowers t)
    (zpowers_le.mpr ⟨Q_le_stabilizer F z htz,Q_le_stabilizer F w htw⟩)
    (fun v hv => by obtain ⟨g,hg,he⟩ := hlinearC v hv; exact ⟨g,hCN hg,he⟩)
    (fun v hv => by obtain ⟨g,hg,he⟩ := hlocalC v hv; exact ⟨g,hCN hg.2,he⟩)
  exact mem_bot.mp (hbot ▸ mem_zpowers t)

set_option backward.isDefEq.respectTransparency false in
/-- Every nonidentity element of the actual path two-subgroup lies in the
trapped branch of (12.7), also in the original completion. This is the
literal premise of the existing trapped-centralizer escape calculation. -/
theorem source_suzuki_nine_path_nonidentity_trapped
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T₀ : Sylow 2 (star L S i))
    (hT₀ : (T₀ : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hq : Nat.card k = 2^(2*n+1))
    (Tlin : Sylow 2 (star L S (!i)))
    (hTlin : (Tlin : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hca : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hcc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p)
    (t : G₀ L S) (ht : t ∈ D) (htne : t ≠ 1)
    (hbranch : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) i),
      V (reducedFamily L S) (base (reducedFamily L S) i) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    (V F (p.1 : Vertex F) 1 ⊓ centralizer ({t} : Set (G₀ L S))) ≤ Q F (base F i) ∧
      (V F (p.1 : Vertex F) 1).map (G₀ L S).subtype ⊓ centralizer ({(t : G)} : Set G) ≤
        (Q F (base F i)).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  have htrap : V F (p.1 : Vertex F) 1 ⊓ centralizer ({t} : Set (G₀ L S)) ≤ Q F (base F i) := by
    by_contra hesc
    exact htne (source_suzuki_nine_path_untrapped_eq_one h i hb hn eSuz eLin T₀ hT₀
      hq Tlin hTlin p hp hm hy hca hcc hc D hD hfix t ht hesc hbranch)
  refine ⟨htrap,?_⟩
  rintro u ⟨⟨v,hv,rfl⟩,hcomm⟩
  apply mem_map_of_mem (G₀ L S).subtype
  apply htrap
  refine ⟨hv,?_⟩
  intro a ha
  have he : a = t := Set.mem_singleton_iff.mp ha
  subst a
  apply (G₀ L S).subtype_injective
  exact hcomm (t : G) (Set.mem_singleton (t : G))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
