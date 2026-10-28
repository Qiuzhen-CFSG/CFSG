module

public import Theory.GroupTheory.CentralLayerMovement
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralChiefResidual
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCoreAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralComparison
public import Theory.GroupAction.CubicTree.CentralReflection

/-!
# The radius-one odd-interval exclusion

At the right fixed endpoint, the translated involution lies in the actual
Ω₁(Z(O₂)) and has different actions under two conjugate involutions. The
normal central layer is therefore moved by the two-residual. Its chief bound
forces the residual to be A₄, contradicting the standing local exclusion.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5), p.398.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupTheory
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- A one-edge central interval of radius one supplies the moving central
binary layer in the two-core of its right fixed endpoint. -/
theorem CubicTreeAction.odd_radius_one_residual_alternatingFour
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G) (href : t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (hwidth : d.centralRight = d.centralLeft + 1)
    (hl : d.leftMargin = 1) (hr : d.rightMargin = 1) :
    Nonempty ((pResidual 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))) ≃*
      alternatingGroup (Fin 4)) := by
  let : ∀ i, Finite (F i) := h.finite
  let b := d.fixedRight
  let H := RankTwo.stabilizer F (t.vertex b)
  let Q := pCore 2 H
  let QG := Q.map H.subtype
  let w := (MulAut.conj (t.translation ^ (1 : ℤ))) z
  let e := d.shift 1
  have hw := hz.shift 1
  have hlcast := d.leftMargin_cast
  have hrcast := d.rightMargin_cast
  have hFL : d.fixedLeft = b - 3 := by dsimp [b]; omega
  have hCL : d.centralLeft = b - 2 := by dsimp [b]; omega
  have hCR : d.centralRight = b - 1 := by dsimp [b]; omega
  have heFL : e.fixedLeft = b - 1 := by dsimp [e, Track.CentralInterval.shift]; omega
  have heFR : e.fixedRight = b + 2 := by dsimp [e, Track.CentralInterval.shift, b]
  have heCL : e.centralLeft = b := by dsimp [e, Track.CentralInterval.shift]; omega
  have heCR : e.centralRight = b + 1 := by dsimp [e, Track.CentralInterval.shift]; omega
  have hwE : t.CentralEdge w b := e.central b (by omega) (by omega)
  have hwH : w ∈ H := hwE.fixes_left
  have hzH : z ∈ H := (d.fixed_iff b).2 ⟨by dsimp [b]; omega, le_rfl⟩
  obtain ⟨g, hg⟩ := href.exists_center b
  have hgH : g ∈ H := by
    change g • t.vertex b = t.vertex b
    simpa only [show 2*b-b = b by omega] using hg b
  let y := (MulAut.conj g) z
  let f := d.reflection g b hg
  have hyE : y ∈ t.edgeStabilizer b := by
    refine ⟨(f.fixed_iff b).2 ⟨?_, ?_⟩, (f.fixed_iff (b+1)).2 ⟨?_, ?_⟩⟩ <;>
      dsimp only [f, Track.CentralInterval.reflection] <;> dsimp only [b] at * <;> omega
  have hwcy : Commute w y := hwE.2 y hyE
  have hnc : ¬ Commute w z := by
    have hh := h.not_commute_of_right_boundary hs hshort t hz d e
      ⟨by omega, by omega⟩
    exact fun hc => hh hc.symm
  obtain ⟨q⟩ := h.stabilizer_quotient_symmetricThree_of_large_residual hC hA (t.vertex b)
  have hQeq : QG = t.edgeStabilizer (b-1) ⊓ t.edgeStabilizer b := by
    let P : ℤ → Prop := fun c =>
      (pCore 2 (RankTwo.stabilizer F (t.vertex c))).map
        (RankTwo.stabilizer F (t.vertex c)).subtype =
      t.edgeStabilizer (b-1) ⊓ t.edgeStabilizer c
    have eq' : ((RankTwo.stabilizer F (t.vertex (b-1+1))) ⧸
        pCore 2 (RankTwo.stabilizer F (t.vertex (b-1+1)))) ≃* Equiv.Perm (Fin 3) := by
      let R : ℤ → Type _ := fun c =>
        ((RankTwo.stabilizer F (t.vertex c)) ⧸ pCore 2 (RankTwo.stabilizer F (t.vertex c))) ≃*
          Equiv.Perm (Fin 3)
      exact (congrArg R (show b = b-1+1 by omega)).mp q
    have hh : P (b-1+1) := h.vertexTwoCore_eq_twoEdges (by omega) hshort t (b-1) eq'
    exact (congrArg P (sub_add_cancel b 1)).mp hh
  have hwQG : w ∈ QG := by
    rw [hQeq]
    refine ⟨⟨(e.fixed_iff (b-1)).2 ⟨by omega, by omega⟩, ?_⟩, hwE.1⟩
    change w • t.vertex (b-1+1) = t.vertex (b-1+1)
    simpa only [sub_add_cancel] using hwE.fixes_left
  let wH : H := ⟨w, hwH⟩
  let xH : H := ⟨z, hzH⟩
  let gH : H := ⟨g, hgH⟩
  have hwQ : wH ∈ Q := by
    obtain ⟨a, ha, hea⟩ := hwQG
    have haeq : a = wH := Subtype.ext hea
    exact haeq ▸ ha
  have hwQcentral : ∀ a ∈ Q, a * wH = wH * a := by
    intro a ha
    apply Subtype.ext
    exact (hwE.2 a ((hQeq ▸ (show (a : G) ∈ QG from ⟨a, ha, rfl⟩)).2)).symm.eq
  let W := Stellmacher.omegaOneCenterAmbient Q
  let : W.Normal := omega_center_normal Q
  let : IsElementaryAbelian 2 W := Stellmacher.omegaOneCenterAmbient_elementaryAbelian Q
  have hwW : wH ∈ W := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff Q wH).2
    refine ⟨hwQ, ?_, hwQcentral⟩
    apply Subtype.ext
    change w ^ 2 = 1
    rw [← hw.1]
    exact pow_orderOf_eq_one w
  have hWQ : W ≤ Q := fun a ha =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff Q a).1 ha).1
  have hWcentral : W ≤ centralizer (Q : Set H) := fun a ha =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff Q a).1 ha).2.2
  have hmove : ⁅W, pResidual 2 H⁆ ≠ ⊥ := by
    apply central_layer_moved_of_conjugate_actions q W hWcentral hwW (x := xH) (g := gH)
    · intro hh
      exact hnc (congrArg Subtype.val hh.eq)
    · apply Subtype.ext
      exact hwcy.eq
  exact h.centralInterval_right_residual_alternatingFour t hz d q
    (h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA _) hr W hWQ hWcentral hmove

theorem CubicTreeAction.odd_radius_one_impossible
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G) (href : t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (hwidth : d.centralRight = d.centralLeft + 1)
    (hl : d.leftMargin = 1) (hr : d.rightMargin = 1) : False := by
  obtain ⟨e⟩ := h.odd_radius_one_residual_alternatingFour hs hshort hC hA t href hz d hwidth hl hr
  let v := t.vertex d.fixedRight
  obtain ⟨g, hg⟩ := exists_smul_base F v
  let f : F v.type ≃* RankTwo.stabilizer F v :=
    (MulEquiv.subgroupCongr (stabilizer_base F v.type).symm).trans
      (MulAction.stabilizerEquivStabilizer hg.symm)
  let r := (f.subgroupMap (pResidual 2 (F v.type))).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 f))
  exact hA v.type ⟨r.trans e⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
