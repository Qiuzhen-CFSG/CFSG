module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Marking
/-!
# The standard paired natural and dual binary pencil

The natural value plane is the first two-coordinate plane, with the first
coordinate line as neighboring value space. Coordinate reversal in the diagram
automorphism identifies the dual seed and neighboring plane with these same
coordinate subgroups, while keeping their actions distinct. A cubic actor and
its diagram image supply the two decompositions and factored opposite actors.
Small vector checks supplement orbit arguments; no subgroups or automorphisms
are enumerated.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(ii), printed p.848.
-/

@[expose] public section
open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry.ModelProof
open FixedGeometry.ValueConstruction FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
abbrev L := pointLine
abbrev H := incidentPlane
abbrev c := lineCycle
def d : SL := ⟨!![1,0,0;0,0,1;0,1,1], by decide⟩
theorem diagram_c : diagram c = d := by decide
theorem diagram_d : diagram d = c := by decide

theorem fixed_point : fixedSpace pointParabolicSL = L := by
  apply le_antisymm
  · intro v hv
    apply (fixed_pointCore.le)
    intro a ha
    exact hv a (by rw [← MarkedProduct.pointParabolic_core] at ha; exact pCoreIn_le 2 _ ha)
  · exact line_fixed_by_point

theorem line_stable (a : SL) (ha : a ∈ pointParabolicSL) :
    L.map (vectorAction a).toMonoidHom = L := by
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    change vectorAction a w ∈ L
    rwa [line_fixed_by_point hw a ha]
  · intro v hv
    exact ⟨v, hv, line_fixed_by_point hv a ha⟩

theorem plane_stable (a : SL) (ha : a ∈ lineParabolicSL) :
    H.map (vectorAction a).toMonoidHom = H := by
  have maps (b : SL) (hb : b ∈ lineParabolicSL) (v : Space) (hv : v ∈ H) :
      vectorAction b v ∈ H := by
    obtain ⟨h0,h1⟩ := (mem_lineParabolicSL_iff b).mp hb
    change b.val.mulVec v.toAdd 2 = 0
    change v.toAdd 2 = 0 at hv
    simp [mulVec, dotProduct, Fin.sum_univ_three, h0, h1, hv]
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact maps a ha w hw
  · intro v hv
    exact ⟨vectorAction a⁻¹ v, maps a⁻¹ (inv_mem ha) v hv, action_inv_cancel a v⟩

theorem plane_span : H = L ⊔ L.map (vectorAction c).toMonoidHom := by
  apply le_antisymm
  · intro v hv
    have test : ∀ v : Fin 3 → ZMod 2, v 2 = 0 →
        ∃ w z : Fin 3 → ZMod 2, (w 1 = 0 ∧ w 2 = 0) ∧
          (z 1 = 0 ∧ z 2 = 0) ∧ v = w + c.val.mulVec z := by decide
    obtain ⟨w,z,hw,hz,he⟩ := test v.toAdd hv
    change v.toAdd = w + c.val.mulVec z at he
    have he' : v = Multiplicative.ofAdd w * vectorAction c (Multiplicative.ofAdd z) := he
    rw [he']
    exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_map_of_mem _ hz))
  · refine sup_le line_le_plane ?_
    change L.map _ ≤ H
    rw [← plane_stable c lineCycle_mem]
    exact map_mono line_le_plane

theorem plane_span_sq : H = L ⊔ L.map (vectorAction (c^2)).toMonoidHom := by
  apply le_antisymm
  · intro v hv
    have test : ∀ v : Fin 3 → ZMod 2, v 2 = 0 →
        ∃ w z : Fin 3 → ZMod 2, (w 1 = 0 ∧ w 2 = 0) ∧
          (z 1 = 0 ∧ z 2 = 0) ∧ v = w + (c^2).val.mulVec z := by decide
    obtain ⟨w,z,hw,hz,he⟩ := test v.toAdd hv
    have he' : v = Multiplicative.ofAdd w * vectorAction (c^2) (Multiplicative.ofAdd z) := he
    rw [he']
    exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_map_of_mem _ hz))
  · refine sup_le line_le_plane ?_
    change L.map _ ≤ H
    rw [← plane_stable (c^2) (pow_mem lineCycle_mem 2)]
    exact map_mono line_le_plane

theorem diagram_line (a : SL) : diagram a ∈ pointParabolicSL ↔ a ∈ lineParabolicSL := by
  have hh := diagram_point_line (diagram a)
  rw [diagram_apply_twice] at hh
  exact hh.symm

theorem d_mem : d ∈ pointParabolicSL := by decide

theorem orbit_plane : orbitSpan diagram pointParabolicSL L = H := by
  apply le_antisymm
  · apply iSup_le
    intro a
    rw [← plane_stable (diagram a) ((diagram_point_line a).mpr a.property)]
    exact map_mono line_le_plane
  · rw [plane_span]
    apply sup_le
    · apply le_trans _ (le_iSup (fun a : pointParabolicSL => L.map (vectorAction (diagram a)).toMonoidHom) 1)
      change L ≤ L.map (vectorAction (diagram 1)).toMonoidHom
      rw [map_one, map_action_one]
    · apply le_trans _ (le_iSup (fun a : pointParabolicSL => L.map (vectorAction (diagram a)).toMonoidHom) ⟨d,d_mem⟩)
      change L.map (vectorAction c).toMonoidHom ≤ L.map (vectorAction (diagram d)).toMonoidHom
      rw [diagram_d]

theorem plane_inter : H.map (vectorAction d).toMonoidHom ⊓
    H.map (vectorAction (d^2)).toMonoidHom ≤ L := by
  rintro v ⟨⟨w,hw,he⟩,z,hz,hzv⟩
  have test : ∀ w z : Fin 3 → ZMod 2, w 2 = 0 → z 2 = 0 →
      d.val.mulVec w = (d^2).val.mulVec z →
      (d.val.mulVec w) 1 = 0 ∧ (d.val.mulVec w) 2 = 0 := by decide
  subst v
  exact test w.toAdd z.toAdd hw hz hzv.symm

theorem opposite_one : H ⊔ H.map (vectorAction d).toMonoidHom = ⊤ := by
  apply top_unique
  intro v _
  have test : ∀ v : Fin 3 → ZMod 2, ∃ w z : Fin 3 → ZMod 2,
      w 2 = 0 ∧ z 2 = 0 ∧ v = w + d.val.mulVec z := by decide
  obtain ⟨w,z,hw,hz,he⟩ := test v.toAdd
  have he' : v = Multiplicative.ofAdd w * vectorAction d (Multiplicative.ofAdd z) := he
  rw [he']
  exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_map_of_mem _ hz))

theorem opposite_two : H ⊔ H.map (vectorAction (c*d)).toMonoidHom = ⊤ := by
  have hh := congrArg (fun A : Subgroup Space => A.map (vectorAction c).toMonoidHom) opposite_one
  simpa only [Subgroup.map_sup, plane_stable c lineCycle_mem, map_action_mul,
    Subgroup.map_top_of_surjective (vectorAction c).toMonoidHom (vectorAction c).surjective] using hh

theorem opposite_lines : L.map (vectorAction c).toMonoidHom ⊓
    L.map (vectorAction (d*c)).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro v ⟨⟨w,hw,he⟩,z,hz,hzv⟩
  have test : ∀ w z : Fin 3 → ZMod 2, (w 1 = 0 ∧ w 2 = 0) →
      (z 1 = 0 ∧ z 2 = 0) → c.val.mulVec w = (d*c).val.mulVec z → c.val.mulVec w = 0 := by decide
  subst v
  exact test w.toAdd z.toAdd hw hz hzv.symm

private def shear (t : ZMod 2 × ZMod 2) : SL := BinaryLinearThree.shear (Multiplicative.ofAdd t)
private theorem shear_mem : ∀ t, shear t ∈ lineParabolicSL := by decide
private theorem outside_transitive : ∀ v w : Fin 3 → ZMod 2,
    v 2 ≠ 0 → w 2 ≠ 0 → ∃ t : ZMod 2 × ZMod 2, (shear t).val.mulVec v = w := by decide
private def five : Fin 5 → Space := fun j => Multiplicative.ofAdd
  (![![0,0,0], ![0,0,1], ![1,0,1], ![0,1,1], ![1,1,1]] j)

theorem small_line (A : Subgroup Space) (hc : Nat.card A ≤ 4)
    (hi : ∀ a ∈ lineParabolicSL, A.map (vectorAction a).toMonoidHom = A) : A ≤ H := by
  intro v hv
  by_contra hn
  have hm (j : Fin 5) : five j ∈ A := by
    by_cases hj : j = 0
    · subst j
      have hh : five 0 = 1 := by decide
      rw [hh]
      exact A.one_mem
    · have hw : ∀ j : Fin 5, j ≠ 0 → (five j).toAdd 2 ≠ 0 := by decide
      obtain ⟨t,ht⟩ := outside_transitive v.toAdd (five j).toAdd hn (hw j hj)
      have he : vectorAction (shear t) v = five j := ht
      rw [← he, ← hi _ (shear_mem t)]
      exact mem_map_of_mem _ hv
  let f : Fin 5 → A := fun j => ⟨five j, hm j⟩
  have hf : Function.Injective f := by
    intro j k he
    have hh : Function.Injective five := by decide
    exact hh (congrArg Subtype.val he)
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at hh
  omega

theorem plane_irreducible (D : Subgroup Space) (hle : D ≤ H)
    (hi : ∀ a ∈ lineParabolicSL, D.map (vectorAction a).toMonoidHom = D) :
    D = ⊥ ∨ D = H := by
  by_cases he : D = ⊥
  · exact Or.inl he
  right
  apply le_antisymm hle
  obtain ⟨⟨v,hv⟩,hvn⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp he
  have hvn : v ≠ 1 := fun hh => hvn (Subtype.ext hh)
  intro w hw
  by_cases hwn : w = 1
  · exact hwn ▸ D.one_mem
  have test : ∀ v w : Fin 3 → ZMod 2,
      v 2 = 0 → v ≠ 0 → w 2 = 0 → w ≠ 0 →
      ∃ t : Fin 3, (c ^ t.val).val.mulVec v = w := by decide
  obtain ⟨t,ht⟩ := test v.toAdd w.toAdd (hle hv) hvn hw hwn
  have het : vectorAction (c^t.val) v = w := ht
  rw [← het, ← hi _ (pow_mem lineCycle_mem _)]
  exact mem_map_of_mem _ hv

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry.ModelProof
