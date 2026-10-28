module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import Theory.SpecificGroups.PSL3.CartanActions.FullTorusFixer
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# Full Hall-torus fixation at the marked diagram model

Transporting the actual overlap Borel and its odd Hall subgroup across the
source recognition map makes the intrinsic PSL3 and Sp4 full-torus theorems
applicable without replacing the Hall subgroup by a standard conjugate.
The derived symplectic marking is identified with its full matrix carrier at
field sizes greater than two. The PSL3 exception retains the literal model
point-parabolic residual intersection.

Source: Aschbacher--Smith, 14.2.12, printed pp.983--984.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.ProperDiagramHallFixer
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem hall_map_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (D : Subgroup X) (hD : IsHallSubgroup OddHall.oddPrimes D) :
    IsHallSubgroup OddHall.oddPrimes (D.map e.toMonoidHom) := by
  refine ⟨?_,?_⟩
  · intro p hp
    rw [card_map_of_injective e.injective] at hp
    exact hD.p_in_pi_of_p_dvd_card p hp
  · intro p hp
    exact hD.p_in_pi_of_p_dvd_index p ((index_map_equiv (H := D) e) ▸ hp)

private theorem map_congr {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (a : MulAut X) (P : Subgroup X) :
    (P.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom =
      (P.map a.toMonoidHom).map e.toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem map_conj {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (P : Subgroup X) (g : X) :
    (P.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom =
      (P.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv]

/-- Change the carrier of the actual parabolic conjugacy-class action. -/
theorem preservesParabolicClass_congr_iff {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (a : MulAut X) (P : Subgroup X) :
    PreservesParabolicClass (MulAut.congr e a) (P.map e.toMonoidHom) ↔
      PreservesParabolicClass a P := by
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨e.symm g,?_⟩
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [← map_congr, ← map_conj, MulEquiv.apply_symm_apply]
    exact hg
  · rintro ⟨g,hg⟩
    refine ⟨e g,?_⟩
    rw [map_congr,map_conj,hg]

variable {H : Type*} [Group H]

/-- A marked source actor fixing its actual odd Hall subgroup forces the
PSL3(4) diagram exception, including the literal residual intersection. -/
theorem psl3_exception_of_fixed_hall
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (M K : Subgroup H) (e : sourceImage M K ≃* PSL(3,F))
    (he : (componentOverlap M K).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F)
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (a : MulAut (sourceImage M K))
    (hB : (componentOverlap M K).map a.toMonoidHom = componentOverlap M K)
    (D : Subgroup (componentOverlap M K)) (hD : IsHallSubgroup OddHall.oddPrimes D)
    (hfix : ∀ d ∈ D, a d.val = d.val)
    (hmove : ¬ (PreservesParabolicClass (MulAut.congr e a) (Matrix.PSL3.LinearThree.pointParabolic F) ∧
      PreservesParabolicClass (MulAut.congr e a) (Matrix.PSL3.LinearThree.lineParabolic F))) :
    f = 2 ∧ Nat.card D = 3 ∧
      D.map (e.toMonoidHom.comp (componentOverlap M K).subtype) ⊓
        (solvableResidual (Matrix.PSL3.LinearThree.pointParabolic F)).map
          (Matrix.PSL3.LinearThree.pointParabolic F).subtype =
      D.map (e.toMonoidHom.comp (componentOverlap M K).subtype) := by
  let B := Matrix.PSL3.LinearThree.borel F
  let eB : componentOverlap M K ≃* B :=
    (e.subgroupMap (componentOverlap M K)).trans (MulEquiv.subgroupCongr he)
  let E := D.map eB.toMonoidHom
  have hE : IsHallSubgroup OddHall.oddPrimes E := hall_map_equiv eB D hD
  have hBF : B.map (MulAut.congr e a).toMonoidHom = B := by
    dsimp only [B]
    rw [← he,map_congr,hB,he]
  have hEF : ∀ d ∈ E, (MulAut.congr e a) d.val = d.val := by
    rintro d ⟨u,hu,rfl⟩
    change e (a (e.symm (e u.val))) = e u.val
    rw [e.symm_apply_apply,hfix u hu]
  have hf2 := Matrix.PSL3.CartanActions.FullTorusFixer.degree_eq_two_of_fixed_hall
    hF hf (MulAut.congr e a) hBF E hE hEF hmove
  have hcard : Nat.card F = 4 := by simpa [hf2] using hF
  obtain ⟨hcardE,hres⟩ :=
    Matrix.PSL3.CartanActions.FullTorusFixer.hall_card_and_inf_pointResidual_of_card_four
      hcard E hE
  have heD : E.map B.subtype =
      D.map (e.toMonoidHom.comp (componentOverlap M K).subtype) := by
    rw [map_map]
    rfl
  rw [heD] at hres
  refine ⟨hf2,?_,hres⟩
  exact (card_map_of_injective eB.injective).symm.trans hcardE

/-- At the full symplectic marking, a pointwise Hall fixer preserves each
of the source's actual maximal-parabolic conjugacy classes. -/
theorem sp4_preservesDiagram_of_fixed_hall
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (M K : Subgroup H) (e : sourceImage M K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (he : (componentOverlap M K).map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel)
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (a : MulAut (sourceImage M K))
    (hB : (componentOverlap M K).map a.toMonoidHom = componentOverlap M K)
    (D : Subgroup (componentOverlap M K)) (hD : IsHallSubgroup OddHall.oddPrimes D)
    (hfix : ∀ d ∈ D, a d.val = d.val) :
    PreservesParabolicClass (MulAut.congr e a) Theory.SpecificGroups.SymplecticFour.pointParabolic ∧
      PreservesParabolicClass (MulAut.congr e a) Theory.SpecificGroups.SymplecticFour.planeParabolic := by
  let B := Theory.SpecificGroups.SymplecticFour.borel (F := F)
  let eB : componentOverlap M K ≃* B :=
    (e.subgroupMap (componentOverlap M K)).trans (MulEquiv.subgroupCongr he)
  let E := D.map eB.toMonoidHom
  have hE : IsHallSubgroup OddHall.oddPrimes E := hall_map_equiv eB D hD
  have hBF : B.map (MulAut.congr e a).toMonoidHom = B := by
    dsimp only [B]
    rw [← he,map_congr,hB,he]
  have hEF : ∀ d ∈ E, (MulAut.congr e a) d.val = d.val := by
    rintro d ⟨u,hu,rfl⟩
    change e (a (e.symm (e u.val))) = e u.val
    rw [e.symm_apply_apply,hfix u hu]
  exact Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer.preservesDiagram_of_fixed_hall
    hF hf (MulAut.congr e a) hBF E hE hEF

/-- The original derived symplectic marking has the same Hall-fixer conclusion,
using the actual inclusion of the derived subgroup into the full group. -/
theorem sp4Derived_preservesDiagram_of_fixed_hall
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (M K : Subgroup H) (e : sourceImage M K ≃* Sp4Derived F)
    (he : (componentOverlap M K).map e.toMonoidHom = sp4DerivedBorel F)
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (a : MulAut (sourceImage M K))
    (hB : (componentOverlap M K).map a.toMonoidHom = componentOverlap M K)
    (D : Subgroup (componentOverlap M K)) (hD : IsHallSubgroup OddHall.oddPrimes D)
    (hfix : ∀ d ∈ D, a d.val = d.val) :
    PreservesParabolicClass (MulAut.congr e a)
      ((Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)).subgroupOf (Sp4Derived F)) ∧
      PreservesParabolicClass (MulAut.congr e a)
      ((Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)).subgroupOf (Sp4Derived F)) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hf
  let e₀ := Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hq
  have he₀ : e₀.toMonoidHom = (Sp4Derived F).subtype := by
    apply MonoidHom.ext
    intro g
    exact Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two_apply hq g
  have hm (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) :
      (P.subgroupOf (Sp4Derived F)).map e₀.toMonoidHom = P := by
    rw [he₀,map_subgroupOf_eq_of_le]
    let _ := Theory.SpecificGroups.SymplecticFour.perfect_of_card_gt_two hq
    rw [show Sp4Derived F = ⊤ from Group.IsPerfect.commutator_eq_top]
    exact le_top
  let eF := e.trans e₀
  have heF : (componentOverlap M K).map eF.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.borel := by
    change (componentOverlap M K).map (e₀.toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map,he,hm]
  have ha : MulAut.congr e₀ (MulAut.congr e a) = MulAut.congr eF a := by
    ext g
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rfl
  have h := sp4_preservesDiagram_of_fixed_hall M K eF heF hF hf a hB D hD hfix
  constructor
  · apply (preservesParabolicClass_congr_iff e₀ (MulAut.congr e a) _).mp
    rw [hm,ha]
    exact h.1
  · apply (preservesParabolicClass_congr_iff e₀ (MulAut.congr e a) _).mp
    rw [hm,ha]
    exact h.2

end CFSG.Quasithin.Chapter14.Section02.ProperDiagramHallFixer
