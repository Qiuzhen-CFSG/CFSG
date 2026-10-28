module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiThreePathExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiRemoteCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionTransitivity
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNinePathOdd

/-!
# Terminal normalizer step for the small-Suzuki nine-path

This leaf isolates the part of the nine-path argument which is independent
of the positive Suzuki parameter.  Once the actual small-Suzuki source has
constructed the two local transitivity actions and the two binary indices,
the centralizer of a path fixer normalizes its cyclic subgroup on an edge;
the faithful cubic tree then kills that cyclic subgroup.  The remaining
source duty is to construct those actions from the zero-parameter quotient.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- The final faithful-tree contradiction in the zero-parameter untrapped
branch.  The hypotheses `htrans` and `hlocalC` are the exact two source
actions still to be produced from the literal `SuzukiMatrixGroup 0`; this
theorem does not assume any positive Suzuki parameter or generation claim. -/
theorem source_small_suzuki_untrapped_terminal
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (Tlin : Sylow 2 (star L S (!i)))
    (hTlin : (Tlin : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p)
    (t : G₀ L S) (ht : t ∈ D)
    (htrans : ∀ v, (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v →
      ∃ g ∈ (V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1 ⊓
        centralizer ({t} : Set (G₀ L S))) ⊔
        V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1,
        g • base (reducedFamily L S) (!i) = v)
    (hlocalC : ∀ v, (graph (reducedFamily L S)).Adj
      (p.2.2.2.2.1 : Vertex (reducedFamily L S)) v →
      ∃ a ∈ stabilizer (reducedFamily L S)
          (p.2.2.2.2.1 : Vertex (reducedFamily L S)) ⊓
        centralizer ({t} : Set (G₀ L S)),
        a • (p.2.2.2.1 : Vertex (reducedFamily L S)) = v)
    (hiY : (Q (reducedFamily L S) (p.2.2.2.2.2.1 : Vertex (reducedFamily L S))).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) i) 1 ⊓
        Q (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S))) = Nat.card k)
    (hiW : (Q (reducedFamily L S) (base (reducedFamily L S) (!i))).relIndex
      (V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k)
    (hVW : V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ≤
      centralizer ({t} : Set (G₀ L S)))
    (hVY : V (reducedFamily L S) (base (reducedFamily L S) i) 1 ≤
      centralizer ({t} : Set (G₀ L S))) :
    t = 1 := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let c : Vertex F := p.2.2.2.2.2.1
  let C := centralizer ({t} : Set (G₀ L S))
  let A := V F (p.1 : Vertex F) 1 ⊓ C
  let E := A ⊔ V F w 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hcore := source_mixed_path_two_subgroup_core h (!i) eLin
    (by cases i <;> exact eSuz) p hp D hD hfix
  have htype : w.type = i := by
    have h3 : (p.2.2.1 : Vertex F).type = i := congrArg
      Subgroup.CosetGeometry.Vertex.type hy
    have h4 : i ≠ z.type := h3 ▸ p.2.2.2.1.property.1
    exact (Bool.eq_not_iff.mpr p.2.2.2.2.1.property.1.symm).trans
      (Bool.not_eq_iff.mpr h4.symm)
  have hzy : (graph F).Adj z y := by
    have hh : (graph F).Adj z (p.2.2.1 : Vertex F) := p.2.2.2.1.property.symm
    simpa only [hy] using hh
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwc : (graph F).Adj w c := p.2.2.2.2.2.1.property
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have htz : t ∈ Q F z := hcore z (by simp [BasedWalk.vertices, z]) ht
  have htw : t ∈ Q F w := hcore w (by simp [BasedWalk.vertices, w]) ht
  have hCN : C ≤ normalizer (zpowers t : Set (G₀ L S)) := by
    rw [zpowers_eq_closure]
    exact (show C ≤ centralizer (closure ({t} : Set (G₀ L S)) : Set (G₀ L S)) by
      rw [centralizer_closure]).trans (Subgroup.centralizer_le_normalizer _)
  have hxm : (graph F).Adj (p.1 : Vertex F) m := by
    have hh : (graph F).Adj (p.1 : Vertex F) (p.2.1 : Vertex F) := p.2.1.property
    simpa only [hm] using hh
  have hXQ := V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1)
    (reduced_kernel_sylow h) hb hxm
  have hWQ := V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1)
    (reduced_kernel_sylow h) hb hzw.symm
  have hqm : Q F m ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) m).2.trans
      (ballKernel_one_le_edge F (show (graph F).Adj m y from
        ⟨by change (!i) ≠ i; cases i <;> decide,
          Subgroup.CosetGeometry.incident_base F (!i) i⟩))).trans inf_le_right
  have hqz : Q F z ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) z).2.trans
      (ballKernel_one_le_edge F hzy)).trans inf_le_right
  obtain ⟨b,hbE,hbm⟩ := htrans z hzy.symm
  have hAfix : A ≤ stabilizer F y := (inf_le_left.trans hXQ).trans hqm
  have hWfix : V F w 1 ≤ stabilizer F y := hWQ.trans hqz
  have hEfix : E ≤ stabilizer F y := sup_le hAfix hWfix
  have hby : b • y = y := hEfix hbE
  obtain ⟨a,ha,hac⟩ := hlocalC c hwc
  have hlinear0 := source_linear_conjugate_intersections_transitive h (!i) eLin Tlin
    (by simpa only [Bool.not_not] using hTlin)
    (Bool.eq_not_iff.mpr (by simpa only [htype] using hzw.1)) hzy hzw hwy hiY hiW
    a⁻¹ b ((stabilizer F w).inv_mem ha.1) (inv_smul_eq_iff.mpr hac.symm) hby hbm
  have hmap (B : Subgroup (G₀ L S)) (hBC : B ≤ C) (g : G₀ L S) (hg : g ∈ C) :
      B.map (MulAut.conj g).toMonoidHom ≤ C := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hBC
    have he : C.map (MulAut.conj g).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer hg)
    exact hh.trans he.le
  have hlinear : ∀ v, (graph F).Adj z v → ∃ g ∈ C, g • w = v := by
    intro v hv
    obtain ⟨g,hg,he⟩ := hlinear0 v hv
    have hAC : A ≤ C := inf_le_right
    have hEcentral : V F w 1 ≤ C := hVW
    have hEC : E ≤ C := sup_le hAC hEcentral
    have hbC : b ∈ C := hEC hbE
    have hsup :
        ((V F y 1).map (MulAut.conj a⁻¹).toMonoidHom ⊓ Q F w) ⊔
          ((V F w 1).map (MulAut.conj b).toMonoidHom ⊓ Q F y) ≤ C := by
      apply sup_le
      · exact inf_le_left.trans (hmap _ hVY _ (C.inv_mem ha.2))
      · exact inf_le_left.trans (hmap _ hEcentral _ hbC)
    exact ⟨g, hsup hg, he⟩
  have hlocal : ∀ v, (graph F).Adj w v → ∃ a ∈ C, a • z = v := by
    intro v hv
    obtain ⟨a,ha,he⟩ := hlocalC v hv
    exact ⟨a, ha.2, he⟩
  have hbot := source_normalized_edge_eq_bot (reduced_triple h) hzw (zpowers t)
    (zpowers_le.mpr ⟨Q_le_stabilizer F z htz, Q_le_stabilizer F w htw⟩)
    (fun v hv => by obtain ⟨g,hg,he⟩ := hlinear v hv; exact ⟨g,hCN hg,he⟩)
    (fun v hv => by obtain ⟨g,hg,he⟩ := hlocal v hv; exact ⟨g,hCN hg,he⟩)
  exact mem_bot.mp (hbot ▸ mem_zpowers t)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
