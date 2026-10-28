module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsLabels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsFrame
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsTrack

/-!
# Even local permutations centralize the folded label product

Each binary branch has two labels whose product is the center label.
Consequently a permutation with an even number of branch flips fixes the
product of one chosen label from each branch. Applied to the three literal
branches in the folded track, this makes Goldschmidt's corrected commutator
central and supplies the track relation (6.12.3).

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.1)--(6.12.3), printed pp.403--404.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
private theorem even_product {E : Type*} [CommGroup E] (z : E) (y : Fin 3 × ZMod 2 → E)
    (hz : z*z=1) (hy : ∀ i, y (i,1)=z*y (i,0))
    (m : Model) (hm : m ∈ evenModel) :
    (∏ i : Fin 3, y (coordinateHom m (i,0))) = ∏ i : Fin 3, y (i,0) := by
  have hh : (∏ i : Fin 3, y (i,m.left.toAdd i)) = ∏ i : Fin 3, y (i,0) := by
    have he := (mem_evenModel m).mp hm
    simp only [Fin.prod_univ_three] at ⊢
    generalize h0 : m.left.toAdd 0 = b0 at *
    generalize h1 : m.left.toAdd 1 = b1 at *
    generalize h2 : m.left.toAdd 2 = b2 at *
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) b0 with rfl | rfl <;>
      rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) b1 with rfl | rfl <;>
      rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) b2 with rfl | rfl <;>
      norm_num at he <;> first | exact ((by decide : (3 : ZMod 2) ≠ 0) he).elim | rfl | (simp only [hy]; calc
        _ = (z*z) * (y (0,0) * y (1,0) * y (2,0)) := by ac_rfl
        _ = _ := by rw [hz, one_mul])
  calc
    (∏ i : Fin 3, y (coordinateHom m (i,0))) =
        ∏ i : Fin 3, y (m.right i, m.left.toAdd (m.right i)) := by
      simp only [coordinateHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, zero_add]
    _ = ∏ i : Fin 3, y (i,m.left.toAdd i) := Equiv.prod_comp m.right (fun i => y (i,m.left.toAdd i))
    _ = _ := hh

open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
/-- Even block action fixes the product of the three chosen forward labels. -/
theorem CanonicalLabelSetup.labelTriple_commute_of_even
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    {a : RankTwo.Vertex F} (ha : a.type = d.side) (f : BranchFrame F a)
    (g : RankTwo.stabilizer F a) (hg : f.blockAction h.action.toCubicTreeAction g ∈ evenModel) :
    Commute (d.label (f.c 0) * d.label (f.c 1) * d.label (f.c 2)) g.val := by
  let A := d.labelBall a 2
  have hs : 4 ≤ s := by have := h.five_le; omega
  let : IsElementaryAbelian 2 A := (d.radiusTwo_card_le h.action.toCubicTreeAction (by omega) hs a ha).1
  let : CommGroup A := IsMulCommutative.instCommGroup
  have ht (x : Fin 3 × ZMod 2) : (f.point x).type = d.side := by
    dsimp only [BranchFrame.point]
    split_ifs
    · exact (f.c_type h.action.toCubicTreeAction _).trans ha
    · exact (f.d_type h.action.toCubicTreeAction _).trans ha
  let y : Fin 3 × ZMod 2 → A := fun x => ⟨d.label (f.point x),
    d.label_mem_labelBall (ht x) (le_of_eq (f.point_dist h.action.toCubicTreeAction x))⟩
  let z : A := ⟨d.label a, d.label_mem_labelBall ha (by simp)⟩
  have hz : z*z=1 := Subtype.ext (d.label_mul_self ha)
  have hy (i : Fin 3) : y (i,1) = z * y (i,0) := by
    have hp := d.neighbor_product (f.e i).val a (f.c i) (f.d i)
      (show (RankTwo.graph F).Adj a (f.e i).val from (f.e i).property).symm
      (f.c_adj i) (f.d_adj i) (f.c_ne_center i).symm (f.d_ne_center i).symm
      (f.c_ne_d i) ha
    have hp' : z * y (i,0) * y (i,1) = 1 := Subtype.ext (by
      change d.label a * d.label (f.point (i,0)) * d.label (f.point (i,1)) = 1
      simpa only [BranchFrame.point, ↓reduceIte, one_ne_zero] using hp)
    have hz' : (z*y (i,0))^2 = 1 := by
      rw [mul_pow, show z^2=1 from by simpa only [pow_two] using hz,
        show y (i,0)^2=1 from Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) _, one_mul]
    calc
      y (i,1) = (z*y (i,0))⁻¹ := (inv_eq_of_mul_eq_one_right hp').symm
      _ = z*y (i,0) := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz')
  have he := even_product z y hz hy (f.blockAction h.action.toCubicTreeAction g) hg
  rw [f.blockAction_coordinates] at he
  simp only [Fin.prod_univ_three] at he
  have he' := congrArg Subtype.val he
  change d.label (f.point (f.sphereAction h.action.toCubicTreeAction g (0,0))) *
      d.label (f.point (f.sphereAction h.action.toCubicTreeAction g (1,0))) *
      d.label (f.point (f.sphereAction h.action.toCubicTreeAction g (2,0))) =
      d.label (f.c 0) * d.label (f.c 1) * d.label (f.c 2) at he'
  rw [f.sphereAction_eval h.action.toCubicTreeAction g (0,0),
    f.sphereAction_eval h.action.toCubicTreeAction g (1,0),
    f.sphereAction_eval h.action.toCubicTreeAction g (2,0),
    d.conjugate g.val _ (ht (0,0)), d.conjugate g.val _ (ht (1,0)),
    d.conjugate g.val _ (ht (2,0))] at he'
  simp only [BranchFrame.point, ↓reduceIte] at he'
  have hc : (MulAut.conj g.val) (d.label (f.c 0) * d.label (f.c 1) * d.label (f.c 2)) =
      d.label (f.c 0) * d.label (f.c 1) * d.label (f.c 2) := by
    simpa only [map_mul, MulAut.conj_apply, mul_assoc] using he'
  change _ = _
  have hh := congrArg (fun x => x * g.val) hc
  simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using hh.symm
/-- The even-image branch of the source commutator argument, with the
literal folded branches and central correction both discharged. -/
theorem CanonicalLabelSetup.radiusThree_track_commutator_of_even
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    (f : BranchFrame F (d.track.vertex d.center))
    (hfc : f.c = ![d.track.vertex (d.center-2), d.track.vertex (d.center+2),
      d.label (d.track.vertex (d.center+4)) • d.track.vertex (d.center-2)])
    (he : (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel) :
    ⁅d.label (d.track.vertex (d.center-2)), d.label (d.track.vertex (d.center+4))⁆ =
      d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)) := by
  apply d.radiusThree_track_commutator_of_central_correction h hr
  intro g hg
  rw [← d.radiusThree_foldedBranchProduct hr f hfc]
  exact d.labelTriple_commute_of_even h hr d.center_type f ⟨g,hg⟩
    (he ⟨⟨g,hg⟩,rfl⟩)
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
