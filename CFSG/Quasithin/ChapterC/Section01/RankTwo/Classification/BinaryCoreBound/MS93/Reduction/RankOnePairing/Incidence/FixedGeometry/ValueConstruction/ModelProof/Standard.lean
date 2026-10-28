module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore
/-!
# Coordinates for the fixed line and its incident plane

The full point-parabolic radical fixes the first coordinate line; the full
line-parabolic radical fixes the plane with last coordinate zero. Twelve
explicit point-parabolic actors act transitively on the six vectors outside
the line, excluding an invariant subgroup of order at most four there.
An explicit cubic actor in the line parabolic gives the three distinct lines
of the incident plane. All finite checks concern vectors and these explicit
matrices, without enumerating subgroups or automorphisms.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (1.7)(i), p.847.
-/

@[expose] public section
open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

def pointLine : Subgroup VectorGroup where
  carrier := {v | v.toAdd 1 = 0 ∧ v.toAdd 2 = 0}
  one_mem' := by exact ⟨rfl, rfl⟩
  mul_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    constructor
    · change v.toAdd 1 + w.toAdd 1 = 0
      rw [hv1, hw1, add_zero]
    · change v.toAdd 2 + w.toAdd 2 = 0
      rw [hv2, hw2, add_zero]
  inv_mem' := by
    rintro v ⟨hv1, hv2⟩
    constructor
    · change -v.toAdd 1 = 0
      rw [hv1, neg_zero]
    · change -v.toAdd 2 = 0
      rw [hv2, neg_zero]

def incidentPlane : Subgroup VectorGroup where
  carrier := {v | v.toAdd 2 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro v w hv hw
    change v.toAdd 2 + w.toAdd 2 = 0
    rw [hv, hw, add_zero]
  inv_mem' := by
    intro v hv
    change -v.toAdd 2 = 0
    rw [hv, neg_zero]

private def translation (a b : ZMod 2) : SL :=
  ⟨!![1, a, b; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
private def levi : Fin 3 → SL := ![
  1,
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩,
  ⟨!![1, 0, 0; 0, 1, 1; 0, 1, 0], by decide⟩]
private def orbitActor (t : ZMod 2 × ZMod 2 × Fin 3) : SL := translation t.1 t.2.1 * levi t.2.2

private theorem actor_mem : ∀ t, orbitActor t ∈ pointParabolicSL := by decide +kernel

private theorem outside_transitive : ∀ v w : Fin 3 → ZMod 2,
    ¬ (v 1 = 0 ∧ v 2 = 0) → ¬ (w 1 = 0 ∧ w 2 = 0) →
    ∃ t : ZMod 2 × ZMod 2 × Fin 3, (orbitActor t).val.mulVec v = w := by
  decide +kernel

theorem fixed_pointCore : fixedSpace pointV = pointLine := by
  apply le_antisymm
  · intro v hv
    have h1 := hv (translation 1 0) (by decide)
    have h2 := hv (translation 0 1) (by decide)
    have test : ∀ v : Fin 3 → ZMod 2,
        (translation 1 0).val.mulVec v = v →
        (translation 0 1).val.mulVec v = v → v 1 = 0 ∧ v 2 = 0 := by decide
    exact test v.toAdd h1 h2
  · rintro v ⟨hv1, hv2⟩ a ha
    change pointCorePred a at ha
    rcases ha with ⟨h00, h10, h20, h11, h12, h21, h22⟩
    change a.val.mulVec v.toAdd = v.toAdd
    ext j
    fin_cases j <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2, h00, h10, h20, h11, h12, h21, h22]

theorem line_fixed_by_point : pointLine ≤ fixedSpace pointParabolicSL := by
  rintro v ⟨hv1, hv2⟩ a ha
  obtain ⟨h10, h20⟩ := (mem_pointParabolicSL_iff a).mp ha
  have h00 : a.val 0 0 = 1 := by
    have hd := a.property
    rw [det_fin_three] at hd
    have hn : a.val 0 0 ≠ 0 := by
      intro hz
      simp [hz, h10, h20] at hd
    have test : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact test _ hn
  change a.val.mulVec v.toAdd = v.toAdd
  ext j
  fin_cases j <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2, h00, h10, h20]

theorem fixed_lineCore : fixedSpace BinaryLinearThree.R = incidentPlane := by
  apply le_antisymm
  · intro v hv
    have hh := hv (BinaryLinearThree.shear (Multiplicative.ofAdd (1, 0))) ⟨_, rfl⟩
    have test : ∀ v : Fin 3 → ZMod 2,
        (BinaryLinearThree.shear (Multiplicative.ofAdd (1, 0))).val.mulVec v = v → v 2 = 0 := by decide
    exact test v.toAdd hh
  · intro v hv a ha
    obtain ⟨c, rfl⟩ := ha
    change !![1, 0, c.toAdd.1; 0, 1, c.toAdd.2; 0, 0, 1].mulVec v.toAdd = v.toAdd
    change v.toAdd 2 = 0 at hv
    ext j
    fin_cases j <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hv]

def lineCycle : SL := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩
theorem lineCycle_mem : lineCycle ∈ lineParabolicSL := by decide
theorem line_fixed_bot : fixedSpace lineParabolicSL = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have h1 := hv (translation 1 0) (by decide)
  have h2 := hv (translation 0 1) (by decide)
  have h3 := hv lineCycle lineCycle_mem
  have test : ∀ v : Fin 3 → ZMod 2,
      (translation 1 0).val.mulVec v = v →
      (translation 0 1).val.mulVec v = v →
      lineCycle.val.mulVec v = v → v = 0 := by decide
  exact test v.toAdd h1 h2 h3

theorem line_card : Nat.card pointLine = 2 := by
  let e : pointLine ≃ ZMod 2 := {
    toFun v := v.val.toAdd 0
    invFun a := ⟨Multiplicative.ofAdd ![a, 0, 0], by exact ⟨rfl, rfl⟩⟩
    left_inv v := by
      apply Subtype.ext
      change ![v.val.toAdd 0, 0, 0] = v.val.toAdd
      ext j
      fin_cases j
      · rfl
      · exact v.property.1.symm
      · exact v.property.2.symm
    right_inv a := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

theorem line_le_plane : pointLine ≤ incidentPlane := fun _ hv => hv.2
theorem plane_ne_top : incidentPlane ≠ ⊤ := by
  intro h
  have : Multiplicative.ofAdd (![0, 0, 1] : Fin 3 → ZMod 2) ∈ incidentPlane := h ▸ mem_top _
  exact (by decide : ¬ ((1 : ZMod 2) = 0)) this

private def fiveOutside : Fin 5 → VectorGroup := fun i => Multiplicative.ofAdd
    (![![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1]] i)
theorem small_invariant (A : Subgroup VectorGroup) (hc : Nat.card A ≤ 4)
    (hi : ∀ a ∈ pointParabolicSL, A.map (vectorAction a).toMonoidHom = A) :
    A ≤ pointLine := by
  intro v hv
  by_contra h
  have hm (j : Fin 5) : fiveOutside j ∈ A := by
    have hw : ∀ j : Fin 5, ¬ ((fiveOutside j).toAdd 1 = 0 ∧ (fiveOutside j).toAdd 2 = 0) := by decide
    obtain ⟨t, ht⟩ := outside_transitive v.toAdd (fiveOutside j).toAdd h (hw j)
    have hh : vectorAction (orbitActor t) v ∈ A := by
      rw [← hi _ (actor_mem t)]
      exact mem_map_of_mem _ hv
    have he : vectorAction (orbitActor t) v = fiveOutside j := ht
    exact he ▸ hh
  let f : Fin 5 → A := fun j => ⟨fiveOutside j, hm j⟩
  have hf : Function.Injective f := by
    intro j k he
    have hinj : Function.Injective fiveOutside := by decide
    exact hinj (congrArg Subtype.val he)
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at hh
  omega

theorem line_neighbors :
    pointLine ⊓ pointLine.map (vectorAction lineCycle).toMonoidHom = ⊥ ∧
    pointLine ⊓ pointLine.map (vectorAction (lineCycle ^ 2)).toMonoidHom = ⊥ ∧
    pointLine.map (vectorAction lineCycle).toMonoidHom ⊓
      pointLine.map (vectorAction (lineCycle ^ 2)).toMonoidHom = ⊥ := by
  have test1 : ∀ v w : Fin 3 → ZMod 2, v 1 = 0 ∧ v 2 = 0 →
      w 1 = 0 ∧ w 2 = 0 → lineCycle.val.mulVec w = v → v = 0 := by decide
  have test2 : ∀ v w : Fin 3 → ZMod 2, v 1 = 0 ∧ v 2 = 0 →
      w 1 = 0 ∧ w 2 = 0 → (lineCycle ^ 2).val.mulVec w = v → v = 0 := by decide
  have test3 : ∀ v w : Fin 3 → ZMod 2, v 1 = 0 ∧ v 2 = 0 →
      w 1 = 0 ∧ w 2 = 0 → lineCycle.val.mulVec v = (lineCycle ^ 2).val.mulVec w →
      lineCycle.val.mulVec v = 0 := by decide
  refine ⟨eq_bot_iff.mpr ?_, eq_bot_iff.mpr ?_, eq_bot_iff.mpr ?_⟩
  · rintro v ⟨hv, w, hw, he⟩
    exact test1 v.toAdd w.toAdd hv hw he
  · rintro v ⟨hv, w, hw, he⟩
    exact test2 v.toAdd w.toAdd hv hw he
  · rintro v ⟨⟨w, hw, rfl⟩, z, hz, he⟩
    exact test3 w.toAdd z.toAdd hw hz he.symm
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
