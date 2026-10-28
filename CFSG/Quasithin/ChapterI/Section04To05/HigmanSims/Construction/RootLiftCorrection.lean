module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreMatrixAction
public import Theory.LinearAlgebra.ZModFourRootCorrection
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreOverlapSquares
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedPointTypes

/-!
# Correcting actual plane lifts while retaining a point core

The correcting element has square in the first marked root line. The
original core-overlap square criterion therefore puts it in the matching
point core. Thus the corrected commuting involution retains the first
point-core membership, while the second lift is unchanged.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.HigmanSims

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem core_in_matrix_kernel (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4)) :
    pCore 2 (normalizer (V : Set G)) ≤ (h.coreMatrixAction e).ker := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let : IsMulCommutative P := ⟨⟨fun x y => e.injective ((e.map_mul x y).trans
    ((mul_comm (e x) (e y)).trans (e.map_mul y x).symm))⟩⟩
  intro g hg
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  let q := e.symm (Multiplicative.ofAdd v)
  have hq : MulAut.conjNormal g q = q := by
    apply Subtype.ext
    change g * (q : M) * g⁻¹ = (q : M)
    have hc : g * (q : M) = (q : M) * g :=
      congrArg Subtype.val (mul_comm (⟨g, hg⟩ : P) q)
    rw [hc, mul_inv_cancel_right]
  have hh := h.coreMatrixAction_apply e g q
  rw [hq] at hh
  simpa only [q, e.apply_symm_apply, toAdd_ofAdd, Matrix.one_mulVec] using hh

/-- Correct an actual first-root lift inside both its full-core coset and
its original point core, obtaining commuting square-one plane lifts. -/
theorem TypeAt.correct_plane_lifts_in_point_core (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (u : G) (hu : u ∈ V) (hu1 : u ≠ 1)
    (hcoord : (((e.symm (Multiplicative.ofAdd ![2, 0, 0]) :
      pCore 2 (normalizer (V : Set G))) : normalizer (V : Set G)) : G) = u)
    (a b t : normalizer (V : Set G))
    (haQ : (a : G) ∈ (involutionCentralizer u).pCoreIn 2)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ht : t ^ 2 = 1)
    (hcP : ⁅a, b⁆ ∈ pCore 2 (normalizer (V : Set G)))
    (hc2 : ⁅a, b⁆ ^ 2 = 1)
    (htP : t * (a * b)⁻¹ ∈ pCore 2 (normalizer (V : Set G)))
    (hAmod : (h.coreMatrixAction e a).map
        (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1])
    (hBmod : (h.coreMatrixAction e b).map
        (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1]) :
    ∃ p : pCore 2 (normalizer (V : Set G)),
      ((p : normalizer (V : Set G)) * a) ^ 2 = 1 ∧
      Commute ((p : normalizer (V : Set G)) * a) b ∧
      ((p : normalizer (V : Set G)) * a) * a⁻¹ ∈
        pCore 2 (normalizer (V : Set G)) ∧
      (((p : normalizer (V : Set G)) * a : normalizer (V : Set G)) : G) ∈
        (involutionCentralizer u).pCoreIn 2 := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let f := h.coreMatrixAction e
  let A := f a
  let B := f b
  let c : P := ⟨⁅a, b⁆, hcP⟩
  let d : P := ⟨t * (a * b)⁻¹, htP⟩
  let : IsMulCommutative P := ⟨⟨fun x y => e.injective ((e.map_mul x y).trans
    ((mul_comm (e x) (e y)).trans (e.map_mul y x).symm))⟩⟩
  have hA : A ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hB : B ^ 2 = 1 := by rw [← map_pow, hb, map_one]
  have hfc : f ⁅a, b⁆ = 1 := core_in_matrix_kernel h e hcP
  have hAB : A * B = B * A := by
    have he : a * b = ⁅a, b⁆ * (b * a) := by simp [commutatorElement_def, mul_assoc]
    have hh := congrArg f he
    simpa only [map_mul, hfc, one_mul] using hh
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have hci : (c : M)⁻¹ = c := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using hc2)
  have hce : (c : M) = (a * b) ^ 2 := by
    simp only [c, commutatorElement_def, hai, hbi, pow_two, mul_assoc]
  have hnorm : d * MulAut.conjNormal (a * b) d = c := by
    apply Subtype.ext
    change (t * (a * b)⁻¹) * ((a * b) * (t * (a * b)⁻¹) * (a * b)⁻¹) = (c : M)
    calc
      _ = t ^ 2 * ((a * b) ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev]; group
      _ = ((a * b) ^ 2)⁻¹ := by rw [ht, one_mul]
      _ = (c : M)⁻¹ := by rw [hce]
      _ = c := hci
  have hcv : (e c).toAdd + (e c).toAdd = 0 := by
    have he : c * c = 1 := by
      apply Subtype.ext
      change ⁅a, b⁆ * ⁅a, b⁆ = 1
      simpa only [pow_two] using hc2
    simpa only [map_mul, map_one, toAdd_mul, toAdd_one] using
      congrArg (fun q : P => (e q).toAdd) he
  have hnormv : ∃ v, (e c).toAdd = v + (A * B).mulVec v := by
    refine ⟨(e d).toAdd, ?_⟩
    have he := congrArg (fun q : P => (e q).toAdd) hnorm
    rw [map_mul, toAdd_mul, ← h.coreMatrixAction_apply e (a * b) d,
      map_mul] at he
    exact he.symm
  obtain ⟨v, hvA, hvB, hvroot⟩ := ZModFourRootCorrection.exists_root_inverted_displacement A B
    hA hB hAB (h.coreMatrixAction_det e a) (h.coreMatrixAction_det e b)
    hAmod hBmod (e c).toAdd hcv hnormv
  let p := e.symm (Multiplicative.ofAdd v)
  have hpA : p * MulAut.conjNormal a p = 1 := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_one, toAdd_mul, toAdd_one,
      ← h.coreMatrixAction_apply e a p]
    simpa only [p, e.apply_symm_apply, toAdd_ofAdd] using hvA
  have hpB : p * (MulAut.conjNormal b p)⁻¹ = c := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
      ← h.coreMatrixAction_apply e b p]
    simpa only [p, e.apply_symm_apply, toAdd_ofAdd, sub_eq_add_neg] using hvB
  have hpAm : (p : M) * (a * (p : M) * a⁻¹) = 1 := congrArg Subtype.val hpA
  have hpBm : (p : M) * (b * (p : M) * b⁻¹)⁻¹ = ⁅a, b⁆ := congrArg Subtype.val hpB
  have hpc : (p : M) * ⁅a, b⁆ = ⁅a, b⁆ * (p : M) :=
    congrArg Subtype.val (mul_comm p c)
  have hpQ : ((p : M) : G) ∈ (involutionCentralizer u).pCoreIn 2 := by
    apply ((h.at_seed_point u hu hu1).mem_point_core_iff_square_mem _
      (show ((p : M) : G) ∈ M.pCoreIn 2 from ⟨p, p.property, rfl⟩)).mpr
    have hep : (e (p ^ 2)).toAdd = v + v := by
      simp only [pow_two, map_mul, toAdd_mul, p, e.apply_symm_apply, toAdd_ofAdd]
    rcases hvroot with hvzero | hvpoint
    · have hpzero : p ^ 2 = 1 := e.injective (Multiplicative.toAdd.injective (by
        rw [map_one, toAdd_one, hep, hvzero]))
      have hh := congrArg (fun q : P => ((q : M) : G)) hpzero
      change (((p : M) : G) ^ 2) = 1 at hh
      rw [hh]
      exact (zpowers u).one_mem
    · have hppoint : p ^ 2 = e.symm (Multiplicative.ofAdd ![2, 0, 0]) :=
        e.injective (Multiplicative.toAdd.injective (by
          rw [e.apply_symm_apply, toAdd_ofAdd, hep, hvpoint]))
      have hh := congrArg (fun q : P => ((q : M) : G)) hppoint
      change (((p : M) : G) ^ 2) = _ at hh
      rw [hcoord] at hh
      rw [hh]
      exact mem_zpowers u
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · calc
      ((p : M) * a) ^ 2 = ((p : M) * (a * (p : M) * a⁻¹)) * a ^ 2 := by
        simp only [pow_two]
        group
      _ = 1 := by rw [hpAm, ha, one_mul]
  · apply commutatorElement_eq_one_iff_commute.mp
    calc
      ⁅(p : M) * a, b⁆ = (p : M) * ⁅a, b⁆ * (b * (p : M) * b⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      _ = ⁅a, b⁆ * ((p : M) * (b * (p : M) * b⁻¹)⁻¹) := by rw [hpc, mul_assoc]
      _ = ⁅a, b⁆ ^ 2 := by rw [hpBm, pow_two]
      _ = 1 := hc2
  · simpa only [mul_inv_cancel_right] using p.property
  · exact ((involutionCentralizer u).pCoreIn 2).mul_mem hpQ haQ

end CFSG.Quasithin.HigmanSims
