module
public import Theory.SpecificGroups.Triality.LeviRankOne
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Fixed parts of the two triality subsystems

From pinned rank-one maps and arm-curve commutation, multiply the three arm
images and restrict the central image to the q-Frobenius fixed field. In
characteristic two, centerlessness of SL₂ makes the commuting arm product
faithful. The graph-field map sends coordinates (a,b,c) to (F(c),F(a),F(b)),
so its fixed part is precisely (a,F(a),F²(a)). The central image is fixed
precisely on SL₂(GF(q)). Both exact ranges are proved inside `SplitGroup`.

The input interfaces still require construction from the genuine Geck
matrices. This module proves the descent implication and does not assert
that either interface is inhabited. Elementary restriction and central
quotient descent are handled in `LeviIdentification`.

Source: GLS3 Proposition 2.6.2(a,b), with the pinning and coefficient action
of §2.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.Parabolics

private theorem coprod_injective_of_center_eq_bot {A B G : Type*}
    [Group A] [Group B] [Group G] (f : A →* G) (g : B →* G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hA : Subgroup.center A = ⊥) (hc : ∀ a b, Commute (f a) (g b)) :
    Function.Injective (f.noncommCoprod g hc) := by
  apply (MonoidHom.noncommCoprod_injective f g hc).mpr
  refine ⟨hf, hg, ?_⟩
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  have ha : a ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply hf
    simp only [map_mul]
    rw [← hb]
    exact (hc c b).eq
  have ha1 : a = 1 := by simpa only [hA, Subgroup.mem_bot] using ha
  simp only [ha1, map_one, Subgroup.mem_bot]

/-- Entrywise q-Frobenius on the rank-one coefficient matrices. -/
def sl2Frobenius (P : Parameters) : SL(2, ExtensionField P) →* SL(2, ExtensionField P) :=
  SpecialLinearGroup.map (fieldFrobenius P).toRingHom

theorem sl2Frobenius_three (P : Parameters) (g : SL(2, ExtensionField P)) :
    sl2Frobenius P (sl2Frobenius P (sl2Frobenius P g)) = g := by
  ext i j
  exact fieldFrobenius_three P (g i j)

namespace PinnedRankOneMaps
variable {P : Parameters} (D : PinnedRankOneMaps P)

/-- The central root descends by restriction to the actual q-element subfield. -/
def centralFixedEmbedding : SL(2, GaloisField P.prime P.exponent) →* SplitGroup P :=
  (D.hom 1).comp (sl2BaseEmbedding P)

theorem centralFixedEmbedding_injective : Function.Injective D.centralFixedEmbedding :=
  (D.injective 1).comp (sl2BaseEmbedding_injective P)

theorem range_centralFixedEmbedding :
    D.centralFixedEmbedding.range = splitLevi P .central ⊓ fixedSubgroup P := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← D.range_central]
      exact ⟨sl2BaseEmbedding P g, rfl⟩
    · change graphFieldAutomorphism P (D.hom 1 (sl2BaseEmbedding P g)) = _
      exact (D.graphField_hom 1 _).trans
        (congrArg (D.hom 1) ((mem_range_sl2BaseEmbedding P _).mp ⟨g, rfl⟩))
  · rintro x ⟨hx, hfixed⟩
    rw [← D.range_central] at hx
    obtain ⟨g, rfl⟩ := hx
    have hg : SpecialLinearGroup.map (fieldFrobenius P).toRingHom g = g := by
      apply D.injective 1
      exact (D.graphField_hom 1 g).symm.trans hfixed
    obtain ⟨a, ha⟩ := (mem_range_sl2BaseEmbedding P g).mpr hg
    exact ⟨a, congrArg (D.hom 1) ha⟩

/-- Multiplication of the three commuting arm images, ordered as 0, 2, 3. -/
def armsProduct (C : ArmRootCommutation P) :
    (SL(2, ExtensionField P) × SL(2, ExtensionField P)) ×
      SL(2, ExtensionField P) →* SplitGroup P :=
  ((D.hom 0).noncommCoprod (D.hom 2)
    (D.commute C 0 2 (by decide) (by decide) (by decide))).noncommCoprod (D.hom 3) (fun a b =>
    (D.commute C 0 3 (by decide) (by decide) (by decide) a.1 b).mul_left
      (D.commute C 2 3 (by decide) (by decide) (by decide) a.2 b))

@[simp] theorem armsProduct_apply (C : ArmRootCommutation P)
    (a : (SL(2, ExtensionField P) × SL(2, ExtensionField P)) × SL(2, ExtensionField P)) :
    D.armsProduct C a = D.hom 0 a.1.1 * D.hom 2 a.1.2 * D.hom 3 a.2 := rfl

/-- Centerlessness of SL₂ in characteristic two eliminates all product kernels. -/
theorem armsProduct_injective (C : ArmRootCommutation P) [CharP (ExtensionField P) 2] :
    Function.Injective (D.armsProduct C) := by
  apply coprod_injective_of_center_eq_bot
  · exact coprod_injective_of_center_eq_bot _ _ (D.injective 0) (D.injective 2)
      (Theory.PSL2.sl2_center_eq_bot _) _
  · exact D.injective 3
  · rw [Subgroup.center_prod, Theory.PSL2.sl2_center_eq_bot]
    exact Subgroup.bot_prod_bot

/-- No larger split subgroup is introduced by multiplying the arm images. -/
theorem range_armsProduct (C : ArmRootCommutation P) :
    (D.armsProduct C).range = splitLevi P .arms := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    have h (i : Fin 4) (hi : i ≠ 1) (g : SL(2, ExtensionField P)) :
        D.hom i g ∈ splitLevi P .arms := by
      have hr : (D.hom i).range ≤ splitLevi P .arms := by
        rw [D.range_hom]
        apply Subgroup.closure_mono
        rintro x ⟨t, ht⟩
        exact ⟨i, hi, t, ht⟩
      exact hr ⟨g, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h 0 (by decide) a.1.1)
      (h 2 (by decide) a.1.2)) (h 3 (by decide) a.2)
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, hi, t, rfl | rfl⟩
    · have hh : positiveRoot P i t ∈ (D.hom i).range := ⟨_, D.positive i t⟩
      obtain ⟨a, ha⟩ := hh
      have hcases : i = 0 ∨ i = 2 ∨ i = 3 := by
        change i ≠ 1 at hi
        omega
      rcases hcases with rfl | rfl | rfl
      · exact ⟨((a, 1), 1), by simpa only [armsProduct_apply, map_one, mul_one, one_mul] using ha⟩
      · exact ⟨((1, a), 1), by simpa only [armsProduct_apply, map_one, mul_one, one_mul] using ha⟩
      · exact ⟨((1, 1), a), by simpa only [armsProduct_apply, map_one, mul_one, one_mul] using ha⟩
    · have hh : negativeRoot P i t ∈ (D.hom i).range := ⟨_, D.negative i t⟩
      obtain ⟨a, ha⟩ := hh
      have hcases : i = 0 ∨ i = 2 ∨ i = 3 := by
        change i ≠ 1 at hi
        omega
      rcases hcases with rfl | rfl | rfl
      · exact ⟨((a, 1), 1), by simpa only [armsProduct_apply, map_one, mul_one, one_mul] using ha⟩
      · exact ⟨((1, a), 1), by simpa only [armsProduct_apply, map_one, mul_one, one_mul] using ha⟩
      · exact ⟨((1, 1), a), by simpa only [armsProduct_apply, map_one, mul_one, one_mul] using ha⟩

/-- The specified graph action cycles 0→2→3→0, together with Frobenius. -/
theorem graphField_armsProduct (C : ArmRootCommutation P)
    (a : (SL(2, ExtensionField P) × SL(2, ExtensionField P)) × SL(2, ExtensionField P)) :
    graphFieldAutomorphism P (D.armsProduct C a) =
      D.armsProduct C ((sl2Frobenius P a.2, sl2Frobenius P a.1.1),
        sl2Frobenius P a.1.2) := by
  change graphFieldAutomorphism P (D.hom 0 a.1.1 * D.hom 2 a.1.2 * D.hom 3 a.2) =
    D.hom 0 (sl2Frobenius P a.2) * D.hom 2 (sl2Frobenius P a.1.1) *
      D.hom 3 (sl2Frobenius P a.1.2)
  calc
    _ = graphFieldAutomorphism P (D.hom 0 a.1.1) *
        graphFieldAutomorphism P (D.hom 2 a.1.2) *
        graphFieldAutomorphism P (D.hom 3 a.2) := by simp only [map_mul]
    _ = D.hom 2 (sl2Frobenius P a.1.1) * D.hom 3 (sl2Frobenius P a.1.2) *
        D.hom 0 (sl2Frobenius P a.2) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·) (D.graphField_hom 0 _) (D.graphField_hom 2 _))
        (D.graphField_hom 3 _)
    _ = _ :=
      ((D.commute C 0 2 (by decide) (by decide) (by decide) _ _).mul_right
        (D.commute C 0 3 (by decide) (by decide) (by decide) _ _)).symm.eq.trans
          (mul_assoc _ _ _).symm

/-- The fixed diagonal in the three factors has coordinates (g,F(g),F²(g)). -/
def armsDiagonal (P : Parameters) : SL(2, ExtensionField P) →*
    (SL(2, ExtensionField P) × SL(2, ExtensionField P)) × SL(2, ExtensionField P) where
  toFun g := ((g, sl2Frobenius P g), sl2Frobenius P (sl2Frobenius P g))
  map_one' := by simp
  map_mul' g h := by simp

/-- The arm embedding has the full cubic coefficient field. -/
def armsFixedEmbedding (C : ArmRootCommutation P) :
    SL(2, ExtensionField P) →* SplitGroup P :=
  (D.armsProduct C).comp (armsDiagonal P)

theorem armsFixedEmbedding_injective (C : ArmRootCommutation P)
    [CharP (ExtensionField P) 2] : Function.Injective (D.armsFixedEmbedding C) := by
  intro g h he
  have he' := D.armsProduct_injective C he
  exact congrArg (fun a => a.1.1) he'

/-- Exact fixed-part range, using product injectivity rather than an assumed
fixed-point generation assertion. -/
theorem range_armsFixedEmbedding (C : ArmRootCommutation P)
    [CharP (ExtensionField P) 2] :
    (D.armsFixedEmbedding C).range = splitLevi P .arms ⊓ fixedSubgroup P := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← D.range_armsProduct C]
      exact ⟨armsDiagonal P g, rfl⟩
    · change graphFieldAutomorphism P (D.armsProduct C (armsDiagonal P g)) = _
      exact (D.graphField_armsProduct C (armsDiagonal P g)).trans
        (congrArg (D.armsProduct C)
          (Prod.ext (Prod.ext (sl2Frobenius_three P g) rfl) rfl))
  · rintro x ⟨hx, hfixed⟩
    rw [← D.range_armsProduct C] at hx
    obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := hx
    have he := D.armsProduct_injective C
      ((D.graphField_armsProduct C ((a, b), c)).symm.trans hfixed)
    have hb : sl2Frobenius P a = b := congrArg (fun a => a.1.2) he
    have hc : sl2Frobenius P b = c := congrArg (fun a => a.2) he
    refine ⟨a, ?_⟩
    change D.armsProduct C ((a, sl2Frobenius P a),
      sl2Frobenius P (sl2Frobenius P a)) = D.armsProduct C ((a, b), c)
    exact congrArg (D.armsProduct C)
      (Prod.ext (Prod.ext rfl hb) ((congrArg (sl2Frobenius P) hb).trans hc))

end PinnedRankOneMaps
end Triality.Standard.Parabolics
