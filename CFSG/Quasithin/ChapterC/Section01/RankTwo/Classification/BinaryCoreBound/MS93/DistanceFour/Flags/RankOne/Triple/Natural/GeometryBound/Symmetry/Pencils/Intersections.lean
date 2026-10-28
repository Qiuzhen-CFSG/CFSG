module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils.Model
/-!
# The order-two intersection of incident binary parabolic cores

At the standard flag, the intersection of the point and line cores is
parametrized injectively by the (0,2) matrix entry. Conjugation retains this
bound at every flag. An incident coset has a representative in the first
parabolic, which normalizes its intrinsic core, so the same bound holds for
every incident opposite core.

Source: Meierfrankenfeld--Stellmacher (1993), the pencil selection in (4.6.8),
printed p.905.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
private theorem core_normalized (P : Subgroup SL) : P ≤ normalizer (P.pCoreIn 2) :=
  P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))

private theorem conjugate_mul {G : Type*} [Group G] (A : Subgroup G) (g p : G) :
    A.map (MulAut.conj (g*p)).toMonoidHom =
      (A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev, mul_assoc]

/-- Right multiplication by the stabilizing parabolic preserves the actual core. -/
theorem matrixCore_right_mul (t : SL) (i : Bool) (g p : SL)
    (hp : p ∈ modelParabolic t i) : matrixCore t i (g*p) = matrixCore t i g := by
  have he : ((modelParabolic t i).pCoreIn 2).map (MulAut.conj p).toMonoidHom =
      (modelParabolic t i).pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (core_normalized _ hp)
  change ((modelParabolic t i).pCoreIn 2).map (MulAut.conj (g*p)).toMonoidHom = _
  rw [conjugate_mul, he]
  rfl

private theorem standard_intersection_card :
    Nat.card ↥(pointV ⊓ BinaryLinearThree.R) ≤ 2 := by
  let f : ↥(pointV ⊓ BinaryLinearThree.R) → ZMod 2 := fun x => x.val.val 0 2
  have hf : Function.Injective f := by
    rintro ⟨x,hxp,hxl⟩ ⟨y,hyp,hyl⟩ h
    apply Subtype.ext
    obtain ⟨⟨a,b⟩,rfl⟩ := hxl
    obtain ⟨⟨c,d⟩,rfl⟩ := hyl
    have hb : b = 0 := hxp.2.2.2.2.1
    have hd : d = 0 := hyp.2.2.2.2.1
    have ha : a = c := h
    subst b; subst d; subst c
    rfl
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using Nat.card_le_card_of_injective f hf

private theorem base_intersection_card (t : SL) (i : Bool) :
    Nat.card ↥((modelParabolic t i).pCoreIn 2 ⊓
      (modelParabolic t (!i)).pCoreIn 2) ≤ 2 := by
  unfold modelParabolic
  rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj t).injective,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj t).injective,
    ← map_inf _ _ _ (MulAut.conj t).injective,
    card_map_of_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective]
  cases i
  · simpa only [Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      MarkedProduct.pointParabolic_core, lineParabolicSL_pCoreIn_two_eq_R]
      using standard_intersection_card
  · simpa only [↓reduceIte, Bool.not_true, Bool.false_eq_true,
      MarkedProduct.pointParabolic_core, lineParabolicSL_pCoreIn_two_eq_R, inf_comm]
      using standard_intersection_card

/-- Incident binary parabolic cores intersect in order at most two. -/
theorem matrix_intersection_card (t : SL) (i : Bool) (d : SL)
    (hd : matrixIncident t i 1 d) :
    Nat.card ↥(matrixCore t i 1 ⊓ matrixCore t (!i) d) ≤ 2 := by
  obtain ⟨m,hm,hdm⟩ := hd
  simp only [inv_one, one_mul] at hm
  have hr : matrixCore t (!i) m = matrixCore t (!i) d := by
    simpa only [mul_inv_cancel_left] using matrixCore_right_mul t (!i) d (d⁻¹*m) hdm
  have hf : ((modelParabolic t i).pCoreIn 2).map (MulAut.conj m).toMonoidHom =
      (modelParabolic t i).pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (core_normalized _ hm)
  rw [← hr, matrixCore_one, ← hf]
  unfold matrixCore
  rw [← map_inf _ _ _ (MulAut.conj m).injective,
    card_map_of_injective (f := (MulAut.conj m).toMonoidHom) (MulAut.conj m).injective]
  exact base_intersection_card t i
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
