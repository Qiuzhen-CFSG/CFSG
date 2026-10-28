module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.Representation.PSL3Two.SmallModules
/-!
# Binary planes and their pointwise fixers

Every order-four subgroup of the literal binary three-space is the image of
`v₂ = 0` under a determinant-one matrix: choose two distinct nonzero vectors
and complete their columns to a basis. The standard pointwise fixer is the
four-element shear group. Its common fixed space recovers the plane, so its
normalizer is exactly the setwise stabilizer. Conjugation then transports the
known maximality of the standard line parabolic to every plane.

Only the basis completion on 64 vector pairs is checked by finite reduction.
The standard shear calculation follows the coordinate proof in
`Theory.SpecificGroups.PSL3Two.Parabolics.LineCore`.

Source: Meierfrankenfeld--Stellmacher (1993), relative-normalizer notation on
p.881 and the choices in (4.3.7)(i), p.887. This is concrete model geometry;
the source amalgam assembly remains separate.
-/

@[expose] public section

open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
abbrev move (g : SL) (A : Subgroup Space) := A.map (modelAction g).toMonoidHom
abbrev conjugate (g : SL) (H : Subgroup SL) := H.map (MulAut.conj g).toMonoidHom

theorem action_conj (g t : SL) (v : Space) :
    modelAction (MulAut.conj g t) (modelAction g v) = modelAction g (modelAction t v) := by
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem move_mul (g h : SL) (A : Subgroup Space) : move g (move h A) = move (g * h) A := by
  simp only [move]
  rw [Subgroup.map_map]
  congr 1
  ext v
  simp

@[simp] theorem move_one (A : Subgroup Space) : move 1 A = A := by
  change A.map (modelAction 1).toMonoidHom = A
  rw [map_one]
  exact Subgroup.map_id A

@[simp] theorem move_cancel (g : SL) (A : Subgroup Space) : move g⁻¹ (move g A) = A := by
  rw [move_mul, inv_mul_cancel, move_one]

@[simp] theorem move_cancel' (g : SL) (A : Subgroup Space) : move g (move g⁻¹ A) = A := by
  rw [move_mul, mul_inv_cancel, move_one]

theorem move_card (g : SL) (A : Subgroup Space) : Nat.card (move g A) = Nat.card A :=
  Subgroup.card_map_of_injective (modelAction g).injective

theorem fixedSpace_conjugate (g : SL) (H : Subgroup SL) :
    fixedSpace (conjugate g H) = move g (fixedSpace H) := by
  ext v
  obtain ⟨v, rfl⟩ := (modelAction g).surjective v
  constructor
  · intro h
    refine ⟨v, ?_, rfl⟩
    intro t ht
    apply (modelAction g).injective
    rw [← action_conj]
    exact h _ (mem_map_of_mem _ ht)
  · rintro ⟨w, hw, he⟩
    have : w = v := (modelAction g).injective he
    subst w
    rintro t ⟨t, ht, rfl⟩
    change modelAction (MulAut.conj g t) (modelAction g v) = modelAction g v
    rw [action_conj, hw t ht]

theorem planeFixer_move (g : SL) (A : Subgroup Space) :
    planeFixer (move g A) = conjugate g (planeFixer A) := by
  ext t
  obtain ⟨t, rfl⟩ := (MulAut.conj g).surjective t
  change _ ↔ (MulAut.conj g).toMonoidHom t ∈ (planeFixer A).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.mem_map_iff_mem (MulAut.conj g).injective]
  constructor
  · intro h v hv
    apply (modelAction g).injective
    rw [← action_conj]
    exact h _ (mem_map_of_mem _ hv)
  · rintro h v ⟨w, hw, rfl⟩
    change modelAction (MulAut.conj g t) (modelAction g w) = modelAction g w
    rw [action_conj, h w hw]

theorem mem_planeStabilizer_iff (g : SL) (A : Subgroup Space) :
    g ∈ planeStabilizer A ↔ ∀ v ∈ A, modelAction g v ∈ A := by
  change move g A = A ↔ _
  constructor
  · intro h v hv
    rw [← h]
    exact mem_map_of_mem _ hv
  · intro h
    apply Subgroup.eq_of_le_of_card_ge
    · rintro v ⟨w, hw, rfl⟩
      exact h w hw
    · exact (move_card g A).ge

theorem planeStabilizer_move (g : SL) (A : Subgroup Space) :
    planeStabilizer (move g A) = conjugate g (planeStabilizer A) := by
  ext t
  obtain ⟨t, rfl⟩ := (MulAut.conj g).surjective t
  change _ ↔ (MulAut.conj g).toMonoidHom t ∈ (planeStabilizer A).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.mem_map_iff_mem (MulAut.conj g).injective,
    mem_planeStabilizer_iff, mem_planeStabilizer_iff]
  constructor
  · intro h v hv
    have hh := h _ (mem_map_of_mem (modelAction g).toMonoidHom hv)
    change modelAction (MulAut.conj g t) (modelAction g v) ∈ move g A at hh
    rw [action_conj] at hh
    exact (Subgroup.mem_map_iff_mem (modelAction g).injective).mp hh
  · rintro h v ⟨w, hw, rfl⟩
    change modelAction (MulAut.conj g t) (modelAction g w) ∈ move g A
    rw [action_conj]
    exact mem_map_of_mem _ (h w hw)

def standardPlane : Subgroup Space where
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

instance : DecidablePred (· ∈ standardPlane) := fun _ => inferInstanceAs (Decidable (_ = _))

theorem standardPlane_card : Nat.card standardPlane = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem standardPlane_stabilizer : planeStabilizer standardPlane = Matrix.PSL3Two.lineParabolicSL := by
  ext g
  rw [mem_planeStabilizer_iff, Matrix.PSL3Two.lineParabolicSL,
    MulAction.mem_stabilizer_set' (Set.toFinite _)]
  rfl

theorem standardPlane_fixer : planeFixer standardPlane = BinaryLinearThree.R := by
  ext g
  constructor
  · intro hf
    have h0 := hf (Multiplicative.ofAdd ![1, 0, 0]) (by rfl)
    have h1 := hf (Multiplicative.ofAdd ![0, 1, 0]) (by rfl)
    change g.val.mulVec ![1, 0, 0] = ![1, 0, 0] at h0
    change g.val.mulVec ![0, 1, 0] = ![0, 1, 0] at h1
    have hc0 : ∀ i, g.val i 0 = (![1, 0, 0] : Fin 3 → ZMod 2) i := by
      intro i
      simpa [mulVec, dotProduct, Fin.sum_univ_three] using congrFun h0 i
    have hc1 : ∀ i, g.val i 1 = (![0, 1, 0] : Fin 3 → ZMod 2) i := by
      intro i
      simpa [mulVec, dotProduct, Fin.sum_univ_three] using congrFun h1 i
    have h22 : g.val 2 2 = 1 := by
      have hd := g.property
      rw [det_fin_three] at hd
      simpa [hc0, hc1] using hd
    refine ⟨Multiplicative.ofAdd (g.val 0 2, g.val 1 2), ?_⟩
    apply Subtype.ext
    change !![1,0,g.val 0 2; 0,1,g.val 1 2; 0,0,1] = g.val
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc0, hc1, h22]
  · rintro ⟨c, rfl⟩ v hv
    change !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1].mulVec v.toAdd = v.toAdd
    change v.toAdd 2 = 0 at hv
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hv]

theorem standardPlane_fixed : fixedSpace (planeFixer standardPlane) = standardPlane := by
  rw [standardPlane_fixer]
  apply le_antisymm
  · intro v hv
    have h := hv (BinaryLinearThree.shear (Multiplicative.ofAdd (1, 0))) ⟨_, rfl⟩
    have test : ∀ v : Fin 3 → ZMod 2,
        (BinaryLinearThree.shear (Multiplicative.ofAdd (1, 0))).val.mulVec v = v → v 2 = 0 := by decide
    exact test v.toAdd h
  · intro v hv g hg
    have hh : g ∈ planeFixer standardPlane := standardPlane_fixer.symm ▸ hg
    exact hh v hv

-- Only 64 ordered pairs of vectors are examined; a third column completes a basis.
theorem complete_pair : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 → u ≠ v →
    ∃ w : Fin 3 → ZMod 2, Matrix.det (fun i => ![u i, v i, w i]) = 1 := by
  decide +kernel


def e0 : Space := Multiplicative.ofAdd ![1, 0, 0]
def e1 : Space := Multiplicative.ofAdd ![0, 1, 0]

theorem standardPlane_le (A : Subgroup Space) (h0 : e0 ∈ A) (h1 : e1 ∈ A) :
    standardPlane ≤ A := by
  have shape : ∀ v : Space, v ∈ standardPlane → v = 1 ∨ v = e0 ∨ v = e1 ∨ v = e0 * e1 := by decide
  intro v hv
  rcases shape v hv with rfl | rfl | rfl | rfl
  · exact A.one_mem
  · exact h0
  · exact h1
  · exact A.mul_mem h0 h1

theorem plane_transitive (A : Subgroup Space) (hA : Nat.card A = 4) :
    ∃ g : SL, move g standardPlane = A := by
  classical
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : A)
  obtain ⟨v, hv, hvu⟩ := ENat.exists_ne_ne_of_three_le
    (α := A) (by rw [ENat.card_eq_coe_natCard, hA]; decide) 1 u
  have hu0 : u.val.toAdd ≠ 0 := fun h => hu (Subtype.ext h)
  have hv0 : v.val.toAdd ≠ 0 := fun h => hv (Subtype.ext h)
  have huv : u.val.toAdd ≠ v.val.toAdd := fun h => hvu (Subtype.ext h.symm)
  obtain ⟨w, hw⟩ := complete_pair u.val.toAdd v.val.toAdd hu0 hv0 huv
  let g : SL := ⟨(fun i => ![u.val.toAdd i, v.val.toAdd i, w i]), hw⟩
  have hg0 : modelAction g e0 = u.val := by
    change g.val.mulVec ![1, 0, 0] = u.val.toAdd
    ext i
    simp [g, mulVec, dotProduct, Fin.sum_univ_three]
  have hg1 : modelAction g e1 = v.val := by
    change g.val.mulVec ![0, 1, 0] = v.val.toAdd
    ext i
    simp [g, mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply standardPlane_le
    · change modelAction g e0 ∈ A
      rw [hg0]
      exact u.property
    · change modelAction g e1 ∈ A
      rw [hg1]
      exact v.property
  · rw [move_card, standardPlane_card, hA]

theorem plane_fixed (A : Subgroup Space) (hA : Nat.card A = 4) :
    fixedSpace (planeFixer A) = A := by
  obtain ⟨g, rfl⟩ := plane_transitive A hA
  rw [planeFixer_move, fixedSpace_conjugate, standardPlane_fixed]

theorem planeFixer_card (A : Subgroup Space) (hA : Nat.card A = 4) :
    Nat.card (planeFixer A) = 4 := by
  obtain ⟨g, rfl⟩ := plane_transitive A hA
  rw [planeFixer_move, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    standardPlane_fixer, BinaryLinearThree.card_R]

theorem planeFixer_normalizer (A : Subgroup Space) (hA : Nat.card A = 4) :
    normalizer (planeFixer A : Set SL) = planeStabilizer A := by
  ext g
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjugate g (planeFixer A) = planeFixer A ↔ move g A = A
  rw [← planeFixer_move]
  constructor
  · intro h
    have he := congrArg fixedSpace h
    rwa [plane_fixed A hA, plane_fixed (move g A) (by rw [move_card, hA])] at he
  · intro h
    rw [h]

theorem planeStabilizer_isCoatom (A : Subgroup Space) (hA : Nat.card A = 4) :
    IsCoatom (planeStabilizer A) := by
  obtain ⟨g, rfl⟩ := plane_transitive A hA
  rw [planeStabilizer_move]
  apply ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr
  rw [standardPlane_stabilizer]
  exact Matrix.PSL3Two.isCoatom_lineParabolicSL

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
