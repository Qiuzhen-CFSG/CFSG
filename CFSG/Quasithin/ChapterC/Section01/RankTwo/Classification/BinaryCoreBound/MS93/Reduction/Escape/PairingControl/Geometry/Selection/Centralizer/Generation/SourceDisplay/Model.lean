module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
/-!
# Six dual vectors and differences of actual conjugates

The stabilizer of a nonzero binary covector is transitive on the other six
nonzero covectors. Complete each independent pair to a determinant-one basis;
the resulting change of basis fixes the first covector and moves the second.
The differences along this orbit generate the full binary three-space.

This difference form permits source assembly to use commutators of actual
neighboring elements, cancelling their component outside Vcirc. It requires
no individual native lift. Annihilator planes retain the same natural and
inverse-transpose actions throughout.

Source: Meierfrankenfeld--Stellmacher (1993), the local generation display
before (4.3.2)(4), printed p.884.
-/

@[expose] public section

open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.Model
open Propagation.Backward.Products.Selection.Choices
open Propagation.Backward.Products.Selection.Choices.FiniteGeometry
abbrev dualAction : SL →* MulAut Space :=
  modelAction.comp BinaryLinearThree.AutomorphismAction.graph.toMonoidHom

theorem dualAction_apply (g : SL) (v : Space) :
    (dualAction g v).toAdd = (g⁻¹).val.transpose.mulVec v.toAdd := rfl

theorem pair_orbit (d v w : Space) (hd : d ≠ 1) (hv : v ≠ 1) (hw : w ≠ 1)
    (hdv : d ≠ v) (hdw : d ≠ w) :
    ∃ g : SL, dualAction g d = d ∧ dualAction g v = w := by
  obtain ⟨z, hz⟩ := complete_pair d.toAdd v.toAdd hd hv hdv
  obtain ⟨z', hz'⟩ := complete_pair d.toAdd w.toAdd hd hw hdw
  let a : SL := ⟨(fun i => ![d.toAdd i, v.toAdd i, z i]), hz⟩
  let b : SL := ⟨(fun i => ![d.toAdd i, w.toAdd i, z' i]), hz'⟩
  have ha0 : modelAction a e0 = d := by
    change a.val.mulVec ![1,0,0] = d.toAdd
    ext i
    simp [a, mulVec, dotProduct, Fin.sum_univ_three]
  have ha1 : modelAction a e1 = v := by
    change a.val.mulVec ![0,1,0] = v.toAdd
    ext i
    simp [a, mulVec, dotProduct, Fin.sum_univ_three]
  have hb0 : modelAction b e0 = d := by
    change b.val.mulVec ![1,0,0] = d.toAdd
    ext i
    simp [b, mulVec, dotProduct, Fin.sum_univ_three]
  have hb1 : modelAction b e1 = w := by
    change b.val.mulVec ![0,1,0] = w.toAdd
    ext i
    simp [b, mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨BinaryLinearThree.AutomorphismAction.graph.symm (b*a⁻¹), ?_, ?_⟩
  · change modelAction (BinaryLinearThree.AutomorphismAction.graph
      (BinaryLinearThree.AutomorphismAction.graph.symm (b*a⁻¹))) d = d
    rw [MulEquiv.apply_symm_apply, ← ha0, map_mul, MulAut.mul_apply, map_inv,
      MulAut.inv_apply_self, hb0]
    exact ha0.symm
  · change modelAction (BinaryLinearThree.AutomorphismAction.graph
      (BinaryLinearThree.AutomorphismAction.graph.symm (b*a⁻¹))) v = w
    rw [MulEquiv.apply_symm_apply, ← ha1, map_mul, MulAut.mul_apply, map_inv,
      MulAut.inv_apply_self, hb1]

private theorem six_cover : ∀ d w : Space, ∃ x y : Space,
    x ≠ 1 ∧ x ≠ d ∧ y ≠ 1 ∧ y ≠ d ∧ x*y=w := by decide +kernel

private theorem square_one : ∀ v : Space, v*v=1 := by decide +kernel

theorem differences_generate (d v : Space) (hd : d ≠ 1) (hv : v ≠ 1) (hdv : d ≠ v)
    (J : Subgroup Space)
    (hJ : ∀ g : SL, dualAction g d = d → dualAction g v * v⁻¹ ∈ J) : J = ⊤ := by
  have hall (w : Space) (hw : w ≠ 1) (hdw : d ≠ w) : w*v⁻¹ ∈ J := by
    obtain ⟨g, hgd, hgv⟩ := pair_orbit d v w hd hv hw hdv hdw
    simpa only [hgv] using hJ g hgd
  apply top_unique
  intro w _
  obtain ⟨x, y, hx, hxd, hy, hyd, hxy⟩ := six_cover d w
  have h := J.mul_mem (hall x hx hxd.symm) (hall y hy hyd.symm)
  have he : (x*v⁻¹)*(y*v⁻¹)=w := by
    calc
      (x*v⁻¹)*(y*v⁻¹) = (x*y)*(v⁻¹*v⁻¹) := by ac_rfl
      _ = w := by rw [square_one, mul_one, hxy]
  exact he ▸ h

def annihilator (v : Space) : Subgroup Space where
  carrier := {u | dotProduct v.toAdd u.toAdd = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change dotProduct v.toAdd (x.toAdd + y.toAdd) = 0
    rw [dotProduct_add, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    change dotProduct v.toAdd (-x.toAdd) = 0
    rw [dotProduct_neg, hx, neg_zero]

instance (v : Space) : DecidablePred (· ∈ annihilator v) :=
  fun u => inferInstanceAs (Decidable (dotProduct v.toAdd u.toAdd = 0))

theorem annihilator_card (v : Space) (hv : v ≠ 1) : Nat.card (annihilator v) = 4 := by
  rw [Nat.card_eq_fintype_card]
  have h : ∀ v : Space, v ≠ 1 → Fintype.card (annihilator v) = 4 := by decide +kernel
  exact h v hv

theorem annihilator_injective : Function.Injective annihilator := by
  intro v w h
  have hc : ∀ v w : Space,
      (∀ u : Space, dotProduct v.toAdd u.toAdd = 0 ↔ dotProduct w.toAdd u.toAdd = 0) → v=w := by
    decide +kernel
  exact hc v w (fun u => show u ∈ annihilator v ↔ u ∈ annihilator w from h ▸ Iff.rfl)

theorem pairing_invariant (g : SL) (v u : Space) :
    dotProduct (dualAction g v).toAdd (modelAction g u).toAdd = dotProduct v.toAdd u.toAdd := by
  rw [dualAction_apply, modelAction_apply, dotProduct_comm,
    Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
  simp

theorem annihilator_move (g : SL) (v : Space) :
    (annihilator v).map (modelAction g).toMonoidHom = annihilator (dualAction g v) := by
  ext u
  obtain ⟨w, rfl⟩ := (modelAction g).surjective u
  constructor
  · rintro ⟨x, hx, he⟩
    have hxe : x = w := (modelAction g).injective he
    subst x
    change dotProduct (dualAction g v).toAdd (modelAction g w).toAdd = 0
    rwa [pairing_invariant]
  · intro hw
    refine ⟨w, ?_, rfl⟩
    change dotProduct (dualAction g v).toAdd (modelAction g w).toAdd = 0 at hw
    rwa [pairing_invariant] at hw
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.Model
