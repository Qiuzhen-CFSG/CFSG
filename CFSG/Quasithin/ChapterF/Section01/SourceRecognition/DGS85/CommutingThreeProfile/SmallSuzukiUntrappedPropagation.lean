module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiEscapingTransitivity

/-!
# The actual small-Suzuki untrapped span

An escaping element of the incoming centralizer and the critical remote
center have nontrivial images in distinct quotient Sylows. Their join is
transitive on the five neighbors, without generating the full quotient.
Because the join centralizes the original path element, this action
propagates centralization to the entire middle span.
-/

public noncomputable section
open Subgroup
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original untrapped subgroup supplies the base-neighborhood action
and centralizes the whole base span at parameter zero. -/
theorem source_small_suzuki_untrapped_centralizer_propagation
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {x c w z : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) i))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (t : G₀ L S)
    (htm : t ∈ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hty : t ∈ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hW : V (reducedFamily L S) w 1 ≤ centralizer ({t} : Set (G₀ L S)))
    (hesc : ¬ V (reducedFamily L S) x 1 ⊓ centralizer ({t} : Set (G₀ L S)) ≤
      Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let E := (V F x 1 ⊓ centralizer ({t} : Set (G₀ L S))) ⊔ V F w 1
    (∀ v, (graph F).Adj (base F i) v → ∃ g ∈ E, g • base F (!i) = v) ∧
      V F (base F i) 1 ≤ centralizer ({t} : Set (G₀ L S)) ∧
      (V F (base F i) 1).map (G₀ L S).subtype ≤ centralizer ({(t : G)} : Set G) := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let A := V F x 1 ⊓ centralizer ({t} : Set (G₀ L S))
  let E := A ⊔ V F w 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hAm : A ≤ Q F m := inf_le_left.trans (V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hxm)
  have hWz : V F w 1 ≤ Q F z := V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hwz
  have hZc : Z F c ≤ V F w 1 :=
    le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F w c).mpr (.inl hwc)) le_rfl)
  have hWesc : ¬ V F w 1 ≤ Q F y := by
    intro he
    exact hc.2 ((hZc.trans he).trans (source_Z_Q_U (reduced_triple h) y).2)
  have htrans := source_small_suzuki_two_core_escape_transitive h i eSuz hyz hzn
    T R hT hR A (V F w 1) hAm hWz hesc hWesc
  have hEP : E ≤ star L S i := sup_le
    (hAm.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _)))
    (hWz.trans ((le_sup_left.trans hR.ge).trans (map_subtype_le _)))
  have hEC : E ≤ centralizer ({t} : Set (G₀ L S)) := sup_le inf_le_right hW
  have hZC (v : Vertex F) (htv : t ∈ Q F v) : Z F v ≤ centralizer ({t} : Set (G₀ L S)) := by
    intro u hu a ha
    have he : a = t := Set.mem_singleton_iff.mp ha
    subst a
    exact Z_centralizes_Q F v (source_Z_Q_U (reduced_triple h) v).1 hu t htv
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hV : V F y 1 ≤ centralizer ({t} : Set (G₀ L S)) := by
    rw [V_eq_center_sup_neighbor_conjugates F E
      (hEP.trans (star_le_stabilizer i)) hadj htrans]
    exact sup_le (hZC y hty) (conjugateSpanBy_le (hZC m htm)
      (hEC.trans (centralizer ({t} : Set (G₀ L S))).le_normalizer))
  refine ⟨htrans,hV,?_⟩
  rintro u ⟨v,hv,rfl⟩ a ha
  have he : a = (t : G) := Set.mem_singleton_iff.mp ha
  subst a
  exact congrArg (fun q : G₀ L S => (q : G)) (hV hv t (Set.mem_singleton t))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
