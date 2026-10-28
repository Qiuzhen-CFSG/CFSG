module
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Transitivity
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry.Basic

/-!
# Transitivity in the actual natural and dual models of G.2.5

A natural marking transports the concrete SL₃ frame, point-pair, and flag
orbits through its group and coordinate equivalences. The action-image
identity is proved for the exact representation, so the transport applies
also to the published inverse-transpose marking of the genuine F-linear dual.

The final applications use the literal natural frame, its three annihilator
marks, and the natural and dual center-axis pairs of the printed root. Their
flag stabilizers act transitively on the other points of the axis, supplying
the orbit input used to propagate the root-fixed condition in Remark G.1.4.
The binary quotient point map and recognition criterion remain with their
source assembly owner; no such map or criterion is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.1.1–4 and
G.2.5(6–7), printed pp.327–328,335–336, PDF pp.338–339,346–347.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Projective Matrix.SpecialLinearGroup Module
open scoped MatrixGroups
namespace Projective.NaturalMarking
variable {F K V : Type*} [Field F] [Group K] [AddCommGroup V] [Module F V]
  {γ : Representation F K V} (m : NaturalMarking γ)
include m

/-- Coordinate transport respects the exact represented action. -/
theorem map_action (A : Submodule F V) (a : K) :
    (A.map (γ a)).map m.coordinates.toLinearMap =
      (A.map m.coordinates.toLinearMap).map (FrameGeometry.natural (m.groupEquiv a)) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext (m.equivariant a)

private theorem map_eq_of_model_map (a : SL(3, F)) (A B : Submodule F V)
    (ha : (A.map m.coordinates.toLinearMap).map (FrameGeometry.natural a) =
      B.map m.coordinates.toLinearMap) :
    A.map (γ (m.groupEquiv.symm a)) = B := by
  apply Submodule.map_injective_of_injective m.coordinates.injective
  rw [m.map_action, m.groupEquiv.apply_symm_apply]
  exact ha

/-- Transitivity on actual one-dimensional submodules of the marked action. -/
theorem exists_point_map (A B : Point F V) : ∃ a : K, A.val.map (γ a) = B.val := by
  obtain ⟨a, ha⟩ := FrameGeometry.exists_point_map
    (A.val.map m.coordinates.toLinearMap) (B.val.map m.coordinates.toLinearMap)
    ((m.coordinates.finrank_map_eq _).trans A.property)
    ((m.coordinates.finrank_map_eq _).trans B.property)
  exact ⟨m.groupEquiv.symm a, m.map_eq_of_model_map a A.val B.val ha⟩

/-- Two-transitivity on the exact projective points, transported through the marking. -/
theorem exists_point_pair_map (A B C D : Point F V) (hAB : A ≠ B) (hCD : C ≠ D) :
    ∃ a : K, A.val.map (γ a) = C.val ∧ B.val.map (γ a) = D.val := by
  have hinj := Submodule.map_injective_of_injective m.coordinates.injective
  obtain ⟨a, ha, hb⟩ := FrameGeometry.exists_point_pair_map
    (A.val.map m.coordinates.toLinearMap) (B.val.map m.coordinates.toLinearMap)
    (C.val.map m.coordinates.toLinearMap) (D.val.map m.coordinates.toLinearMap)
    ((m.coordinates.finrank_map_eq _).trans A.property)
    ((m.coordinates.finrank_map_eq _).trans B.property)
    ((m.coordinates.finrank_map_eq _).trans C.property)
    ((m.coordinates.finrank_map_eq _).trans D.property)
    (fun he => hAB (Subtype.ext (hinj he))) (fun he => hCD (Subtype.ext (hinj he)))
  exact ⟨m.groupEquiv.symm a, m.map_eq_of_model_map a _ _ ha,
    m.map_eq_of_model_map a _ _ hb⟩

/-- Transitivity on point-plane flags for the exact marked representation. -/
theorem exists_flag_map (A C : Point F V) (B D : Submodule F V)
    (hB : finrank F B = 2) (hD : finrank F D = 2) (hAB : A.val ≤ B) (hCD : C.val ≤ D) :
    ∃ a : K, A.val.map (γ a) = C.val ∧ B.map (γ a) = D := by
  obtain ⟨a, ha, hb⟩ := FrameGeometry.exists_flag_map
    (A.val.map m.coordinates.toLinearMap) (B.map m.coordinates.toLinearMap)
    (C.val.map m.coordinates.toLinearMap) (D.map m.coordinates.toLinearMap)
    ((m.coordinates.finrank_map_eq _).trans A.property)
    ((m.coordinates.finrank_map_eq _).trans hB) (Submodule.map_mono hAB)
    ((m.coordinates.finrank_map_eq _).trans C.property)
    ((m.coordinates.finrank_map_eq _).trans hD) (Submodule.map_mono hCD)
  exact ⟨m.groupEquiv.symm a, m.map_eq_of_model_map a _ _ ha,
    m.map_eq_of_model_map a _ _ hb⟩

/-- The actor fixes both members of the flag and sends either other plane point to the other.
This is the stabilizer orbit used to transfer the root-fixed clause of G.1.3. -/
theorem exists_flag_stabilizer_map (A C D : Point F V) (B : Submodule F V)
    (hB : finrank F B = 2) (hAB : A.val ≤ B) (hCB : C.val ≤ B) (hDB : D.val ≤ B)
    (hAC : A ≠ C) (hAD : A ≠ D) :
    ∃ a : K, A.val.map (γ a) = A.val ∧ B.map (γ a) = B ∧ C.val.map (γ a) = D.val := by
  have hinj := Submodule.map_injective_of_injective m.coordinates.injective
  obtain ⟨a, ha, hCD⟩ := FrameGeometry.exists_flag_stabilizer_map
    (A.val.map m.coordinates.toLinearMap) (B.map m.coordinates.toLinearMap)
    (C.val.map m.coordinates.toLinearMap) (D.val.map m.coordinates.toLinearMap)
    ((m.coordinates.finrank_map_eq _).trans A.property)
    ((m.coordinates.finrank_map_eq _).trans hB) (Submodule.map_mono hAB)
    ((m.coordinates.finrank_map_eq _).trans C.property)
    ((m.coordinates.finrank_map_eq _).trans D.property)
    (Submodule.map_mono hCB) (Submodule.map_mono hDB)
    (fun he => hAC (Subtype.ext (hinj he))) (fun he => hAD (Subtype.ext (hinj he)))
  exact ⟨m.groupEquiv.symm a,
    m.map_eq_of_model_map a _ _ ((FrameGeometry.mem_stabilizer_iff _ a).mp ha.1),
    m.map_eq_of_model_map a _ _ ((FrameGeometry.mem_stabilizer_iff _ a).mp ha.2),
    m.map_eq_of_model_map a _ _ hCD⟩

private def coordinateFrame (b : Fin 3 → Submodule F V)
    (hdim : ∀ i, finrank F (b i) = 1) (h01 : Disjoint (b 0) (b 1))
    (h2 : Disjoint (b 0 ⊔ b 1) (b 2)) (hs : (b 0 ⊔ b 1) ⊔ b 2 = ⊤) :
    FrameGeometry.Frame F where
  point i := (b i).map m.coordinates.toLinearMap
  dimension i := (m.coordinates.finrank_map_eq _).trans (hdim i)
  disjoint := Submodule.disjoint_map m.coordinates.injective h01
  third_disjoint := by
    rw [← Submodule.map_sup]
    exact Submodule.disjoint_map m.coordinates.injective h2
  span := by
    rw [← Submodule.map_sup, ← Submodule.map_sup, hs, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr m.coordinates.surjective

/-- Ordered direct-frame transitivity under a genuine natural marking. -/
theorem exists_frame_map (b c : Fin 3 → Submodule F V)
    (hbdim : ∀ i, finrank F (b i) = 1) (hb01 : Disjoint (b 0) (b 1))
    (hb2 : Disjoint (b 0 ⊔ b 1) (b 2)) (hbs : (b 0 ⊔ b 1) ⊔ b 2 = ⊤)
    (hcdim : ∀ i, finrank F (c i) = 1) (hc01 : Disjoint (c 0) (c 1))
    (hc2 : Disjoint (c 0 ⊔ c 1) (c 2)) (hcs : (c 0 ⊔ c 1) ⊔ c 2 = ⊤) :
    ∃ a : K, ∀ i, (b i).map (γ a) = c i := by
  obtain ⟨a, ha⟩ := FrameGeometry.exists_frame_map
    (m.coordinateFrame b hbdim hb01 hb2 hbs) (m.coordinateFrame c hcdim hc01 hc2 hcs)
  exact ⟨m.groupEquiv.symm a, fun i => m.map_eq_of_model_map a _ _ (ha i)⟩
end Projective.NaturalMarking

namespace DualGeometry.ModelGeometry
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

/-- Ordered direct frames for the literal natural action of the source starred group. -/
theorem natural_exists_frame_map (b c : FrameGeometry.Frame F) :
    ∃ a : D.star D.L, ∀ i, (b.point i).map (naturalAction d a) = c.point i :=
  (naturalMarking d).exists_frame_map b.point c.point
    b.dimension b.disjoint b.third_disjoint b.span
    c.dimension c.disjoint c.third_disjoint c.span

/-- In particular the actual G.2.5 frame can be sent to any ordered direct frame. -/
theorem marked_frame_map (c : FrameGeometry.Frame F) :
    ∃ a : D.star D.L, ∀ i, ((frame d).point i).map (naturalAction d a) = c.point i :=
  natural_exists_frame_map d (frame d) c

/-- Ordered direct frames for the genuine contragredient action. -/
theorem dual_exists_frame_map
    (b c : Fin 3 → Submodule F (Module.Dual F (Fin 3 → F)))
    (hbdim : ∀ i, finrank F (b i) = 1) (hb01 : Disjoint (b 0) (b 1))
    (hb2 : Disjoint (b 0 ⊔ b 1) (b 2)) (hbs : (b 0 ⊔ b 1) ⊔ b 2 = ⊤)
    (hcdim : ∀ i, finrank F (c i) = 1) (hc01 : Disjoint (c 0) (c 1))
    (hc2 : Disjoint (c 0 ⊔ c 1) (c 2)) (hcs : (c 0 ⊔ c 1) ⊔ c 2 = ⊤) :
    ∃ a : D.star D.L, ∀ i, (b i).map (dualAction d a) = c i :=
  (dualMarking d).exists_frame_map b c hbdim hb01 hb2 hbs hcdim hc01 hc2 hcs

/-- The three literal annihilator marks in G.2.5 form a single full frame orbit. -/
theorem marked_dual_frame_map
    (c : Fin 3 → Submodule F (Module.Dual F (Fin 3 → F)))
    (hcdim : ∀ i, finrank F (c i) = 1) (hc01 : Disjoint (c 0) (c 1))
    (hc2 : Disjoint (c 0 ⊔ c 1) (c 2)) (hcs : (c 0 ⊔ c 1) ⊔ c 2 = ⊤) :
    ∃ a : D.star D.L, ∀ i,
      (![ (dualPoint d).val, (dualPointH d).val, (dualPointGH d).val] i).map
        (dualAction d a) = c i := by
  apply dual_exists_frame_map d _ c
  · intro i
    fin_cases i
    · exact (dualPoint d).property
    · exact (dualPointH d).property
    · exact (dualPointGH d).property
  · exact dual_points_disjoint d
  · exact (dual_third_complement d).disjoint
  · exact dual_points_span d
  · exact hcdim
  · exact hc01
  · exact hc2
  · exact hcs

/-- Point transitivity in the source's actual natural representation. -/
theorem natural_exists_point_map (A B : Point F (Fin 3 → F)) :
    ∃ a : D.star D.L, A.val.map (naturalAction d a) = B.val :=
  (naturalMarking d).exists_point_map A B

/-- Ordered distinct point-pair transitivity for the actual natural action. -/
theorem natural_exists_point_pair_map (A B C E : Point F (Fin 3 → F))
    (hAB : A ≠ B) (hCE : C ≠ E) :
    ∃ a : D.star D.L, A.val.map (naturalAction d a) = C.val ∧
      B.val.map (naturalAction d a) = E.val :=
  (naturalMarking d).exists_point_pair_map A B C E hAB hCE

/-- Incident point-plane flag transitivity for the actual natural action. -/
theorem natural_exists_flag_map (A C : Point F (Fin 3 → F))
    (B E : Submodule F (Fin 3 → F)) (hB : finrank F B = 2) (hE : finrank F E = 2)
    (hAB : A.val ≤ B) (hCE : C.val ≤ E) :
    ∃ a : D.star D.L, A.val.map (naturalAction d a) = C.val ∧
      B.map (naturalAction d a) = E :=
  (naturalMarking d).exists_flag_map A C B E hB hE hAB hCE

/-- The natural flag stabilizer orbit required by Remark G.1.4. -/
theorem natural_exists_flag_stabilizer_map (A C E : Point F (Fin 3 → F))
    (B : Submodule F (Fin 3 → F)) (hB : finrank F B = 2)
    (hAB : A.val ≤ B) (hCB : C.val ≤ B) (hEB : E.val ≤ B) (hAC : A ≠ C) (hAE : A ≠ E) :
    ∃ a : D.star D.L, A.val.map (naturalAction d a) = A.val ∧
      B.map (naturalAction d a) = B ∧ C.val.map (naturalAction d a) = E.val :=
  (naturalMarking d).exists_flag_stabilizer_map A C E B hB hAB hCB hEB hAC hAE

/-- Point transitivity in the source's actual dual representation. -/
theorem dual_exists_point_map (A B : Point F (Module.Dual F (Fin 3 → F))) :
    ∃ a : D.star D.L, A.val.map (dualAction d a) = B.val :=
  (dualMarking d).exists_point_map A B

/-- Ordered distinct point-pair transitivity for the actual dual action. -/
theorem dual_exists_point_pair_map (A B C E : Point F (Module.Dual F (Fin 3 → F)))
    (hAB : A ≠ B) (hCE : C ≠ E) :
    ∃ a : D.star D.L, A.val.map (dualAction d a) = C.val ∧
      B.val.map (dualAction d a) = E.val :=
  (dualMarking d).exists_point_pair_map A B C E hAB hCE

/-- Incident point-plane flag transitivity for the actual dual action. -/
theorem dual_exists_flag_map (A C : Point F (Module.Dual F (Fin 3 → F)))
    (B E : Submodule F (Module.Dual F (Fin 3 → F))) (hB : finrank F B = 2) (hE : finrank F E = 2)
    (hAB : A.val ≤ B) (hCE : C.val ≤ E) :
    ∃ a : D.star D.L, A.val.map (dualAction d a) = C.val ∧
      B.map (dualAction d a) = E :=
  (dualMarking d).exists_flag_map A C B E hB hE hAB hCE

/-- The dual flag stabilizer orbit required by Remark G.1.4. -/
theorem dual_exists_flag_stabilizer_map (A C E : Point F (Module.Dual F (Fin 3 → F)))
    (B : Submodule F (Module.Dual F (Fin 3 → F))) (hB : finrank F B = 2)
    (hAB : A.val ≤ B) (hCB : C.val ≤ B) (hEB : E.val ≤ B) (hAC : A ≠ C) (hAE : A ≠ E) :
    ∃ a : D.star D.L, A.val.map (dualAction d a) = A.val ∧
      B.map (dualAction d a) = B ∧ C.val.map (dualAction d a) = E.val :=
  (dualMarking d).exists_flag_stabilizer_map A C E B hB hAB hCB hEB hAC hAE

/-- The exact natural center-axis pair of the printed root has the required stabilizer orbit. -/
theorem marked_natural_flag_orbit (C E : Point F (Fin 3 → F))
    (hC : C.val ≤ pairPlane d) (hE : E.val ≤ pairPlane d)
    (hnC : naturalPoint d ≠ C) (hnE : naturalPoint d ≠ E) :
    ∃ a : D.star D.L, d.point.map (naturalAction d a) = d.point ∧
      (pairPlane d).map (naturalAction d a) = pairPlane d ∧
      C.val.map (naturalAction d a) = E.val :=
  natural_exists_flag_stabilizer_map d (naturalPoint d) C E (pairPlane d)
    (pairPlane_dimension d) le_sup_left hC hE hnC hnE

/-- The printed dual root has the same stabilizer orbit on the other points of its axis.
This supplies the orbit input for transporting its checked root-fixed condition. -/
theorem marked_dual_flag_orbit (C E : Point F (Module.Dual F (Fin 3 → F)))
    (hC : C.val ≤ d.point.dualAnnihilator) (hE : E.val ≤ d.point.dualAnnihilator)
    (hnC : dualPoint d ≠ C) (hnE : dualPoint d ≠ E) :
    ∃ a : D.star D.L, (dualPoint d).val.map (dualAction d a) = (dualPoint d).val ∧
      d.point.dualAnnihilator.map (dualAction d a) = d.point.dualAnnihilator ∧
      C.val.map (dualAction d a) = E.val := by
  apply dual_exists_flag_stabilizer_map d (dualPoint d) C E d.point.dualAnnihilator
  · rw [Subspace.finrank_dualAnnihilator, d.point_dimension]
    simp
  · exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.mpr
      (show d.point ≤ pairPlane d from le_sup_left)
  · exact hC
  · exact hE
  · exact hnC
  · exact hnE

end DualGeometry.ModelGeometry

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
