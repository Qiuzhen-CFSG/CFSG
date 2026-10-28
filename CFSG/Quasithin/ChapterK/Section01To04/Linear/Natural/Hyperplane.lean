module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.QuadraticBound
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Hyperplane centralizers on natural SL modules

The pointwise centralizer of a coordinate F-hyperplane consists exactly of
the shears v ↦ v + v_j w, with w in that hyperplane. This identifies the
literal subgroup with its additive parameter space and proves binary rank
r(n-1), fixed codimension r, quadraticity, and bestness. Every nontrivial
subgroup has the same fixed hyperplane. The resulting ratio is 1/(n-1).
The coordinate centralizers contain every elementary transvection, so the
best offenders generate SL. No abstract group tag replaces the matrix action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.1,
printed pp.454–455. The elementary generation theorem is reused from the
attributed ATLAS port Theory.AtlasPort.ExceptionalIsomorphisms.Elementary.
-/

@[expose] public section

open Representation Representation.BinaryOffender Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped ENNReal
namespace CFSG.Quasithin.ChapterK.Linear.Natural
variable (F : BinaryField) (n : ℕ) (j : Fin n)

noncomputable def coordinateHyperplane : Submodule F.Carrier (Fin n → F.Carrier) :=
  (LinearMap.proj j : (Fin n → F.Carrier) →ₗ[F.Carrier] F.Carrier).ker

@[simp] lemma mem_coordinateHyperplane (v : Fin n → F.Carrier) :
    v ∈ coordinateHyperplane F n j ↔ v j = 0 := Iff.rfl

noncomputable def hyperplaneCentralizer : Subgroup (SpecialLinearGroup (Fin n) F.Carrier) :=
  subspaceKernel (linearNatural F n) ((coordinateHyperplane F n j).restrictScalars (ZMod 2)) ⊤

noncomputable def shear (w : coordinateHyperplane F n j) : SpecialLinearGroup (Fin n) F.Carrier :=
  ⟨1 + vecMulVec w.val (Pi.single j 1), by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, single_dotProduct, one_mul]
    rw [(mem_coordinateHyperplane F n j w.val).mp w.property, add_zero]⟩

lemma shear_apply (w : coordinateHyperplane F n j) (v : Fin n → F.Carrier) :
    linearNatural F n (shear F n j w) v = v + v j • w.val := by
  change (1 + vecMulVec w.val (Pi.single j 1)).mulVec v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, single_dotProduct, one_mul]
  rw [op_smul_eq_smul]

lemma shear_mem (w : coordinateHyperplane F n j) : shear F n j w ∈ hyperplaneCentralizer F n j := by
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro v hv
  rw [shear_apply, (mem_coordinateHyperplane F n j v).mp hv, zero_smul, add_zero]

lemma shear_zero : shear F n j 0 = 1 := by
  apply natural_injective F n
  apply LinearMap.ext
  intro v
  rw [shear_apply]
  simp

lemma shear_add (w u : coordinateHyperplane F n j) :
    shear F n j (w + u) = shear F n j w * shear F n j u := by
  apply natural_injective F n
  apply LinearMap.ext
  intro v
  rw [map_mul, Module.End.mul_apply, shear_apply, shear_apply, shear_apply]
  have hu : (u : Fin n → F.Carrier) j = 0 := u.property
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu, mul_zero, add_zero,
    Submodule.coe_add, smul_add]
  abel

lemma shear_injective : Function.Injective (shear F n j) := by
  intro w u h
  have he := congrArg (fun g => linearNatural F n g (Pi.single j 1)) h
  rw [shear_apply, shear_apply] at he
  simp only [Pi.single_eq_same, one_smul] at he
  exact Subtype.ext (add_left_cancel he)

lemma centralizer_eq_shear {g : SpecialLinearGroup (Fin n) F.Carrier}
    (hg : g ∈ hyperplaneCentralizer F n j) : ∃ w, shear F n j w = g := by
  let e : Fin n → F.Carrier := Pi.single j 1
  let w := linearNatural F n g e - e
  have he : e j = 1 := Pi.single_eq_same j 1
  have hact (v : Fin n → F.Carrier) : linearNatural F n g v = v + v j • w := by
    have hfix := hg.2 (v - v j • e) (by
      change v j - v j * e j = 0
      rw [he, mul_one, sub_self])
    change specialLinearNatural n g (v - v j • e) = v - v j • e at hfix
    rw [map_sub, map_smul] at hfix
    change specialLinearNatural n g v = v + v j • (specialLinearNatural n g e - e)
    rw [smul_sub]
    linear_combination hfix
  have hmat : g.val = 1 + vecMulVec w e := by
    apply Matrix.mulVec_injective
    funext v
    rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec]
    rw [show e = Pi.single j 1 from rfl, single_dotProduct, one_mul, op_smul_eq_smul]
    exact hact v
  have hw : w ∈ coordinateHyperplane F n j := by
    have hd := g.property
    rw [hmat, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow] at hd
    change 1 + (Pi.single j 1) ⬝ᵥ w = 1 at hd
    rw [single_dotProduct, one_mul] at hd
    exact add_left_cancel (hd.trans (add_zero 1).symm)
  exact ⟨⟨w, hw⟩, Subtype.ext hmat.symm⟩

noncomputable def shearEquiv : Multiplicative (coordinateHyperplane F n j) ≃*
    hyperplaneCentralizer F n j := MulEquiv.ofBijective
  ({
    toFun := fun w => ⟨shear F n j w.toAdd, shear_mem F n j w.toAdd⟩
    map_one' := Subtype.ext (shear_zero F n j)
    map_mul' := fun w u => Subtype.ext (shear_add F n j w.toAdd u.toAdd) } :
    Multiplicative (coordinateHyperplane F n j) →* hyperplaneCentralizer F n j)
  ⟨fun w u h => Multiplicative.ext (shear_injective F n j (congrArg Subtype.val h)),
    fun g => by
      obtain ⟨w, hw⟩ := centralizer_eq_shear F n j g.property
      exact ⟨Multiplicative.ofAdd w, Subtype.ext hw⟩⟩

set_option backward.isDefEq.respectTransparency false in
lemma coordinateHyperplane_codim :
    Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ coordinateHyperplane F n j) = 1 := by
  let ev : (Fin n → F.Carrier) →ₗ[F.Carrier] F.Carrier := LinearMap.proj j
  have hev : Function.Surjective ev := fun c => ⟨(Pi.single j c : Fin n → F.Carrier), by
    change (Pi.single j c : Fin n → F.Carrier) j = c
    simp⟩
  have he := (LinearMap.quotKerEquivOfSurjective ev hev).finrank_eq
  simpa only [Module.finrank_self, ev, coordinateHyperplane] using he

lemma coordinateHyperplane_finrank :
    Module.finrank F.Carrier (coordinateHyperplane F n j) = n - 1 := by
  have h := (coordinateHyperplane F n j).finrank_quotient_add_finrank
  rw [coordinateHyperplane_codim, Module.finrank_pi, Fintype.card_fin] at h
  omega

lemma hyperplaneCentralizer_card :
    Nat.card (hyperplaneCentralizer F n j) = 2 ^ (F.degree * (n - 1)) := by
  rw [← Nat.card_congr (shearEquiv F n j).toEquiv]
  change Nat.card (coordinateHyperplane F n j) = _
  rw [Module.natCard_eq_pow_finrank (K := F.Carrier), F.card_eq,
    coordinateHyperplane_finrank, ← pow_mul]

lemma hyperplaneCentralizer_rank : rank (hyperplaneCentralizer F n j) = F.degree * (n - 1) := by
  rw [BinaryOffender.rank, hyperplaneCentralizer_card, Nat.log_pow (by decide : 1 < 2)]

lemma hyperplaneCentralizer_quadratic : IsQuadratic (linearNatural F n) (hyperplaneCentralizer F n j) := by
  intro a ha b hb v
  obtain ⟨u, rfl⟩ := centralizer_eq_shear F n j hb
  rw [shear_apply, add_sub_cancel_left]
  apply ha.2
  change v j * (u : Fin n → F.Carrier) j = 0
  rw [show (u : Fin n → F.Carrier) j = 0 from u.property, mul_zero]

lemma hyperplaneCentralizer_elementary (hn : 2 ≤ n) : IsElementaryTwo (hyperplaneCentralizer F n j) := by
  have he := shearEquiv F n j
  refine ⟨?_, ?_⟩
  · intro hb
    have hr := hyperplaneCentralizer_rank F n j
    rw [hb, BinaryOffender.rank_bot] at hr
    have hp := F.degree_pos
    have hp' : 0 < F.degree * (n - 1) := Nat.mul_pos hp (by omega)
    omega
  · refine {
      toIsMulCommutative := ⟨⟨fun a b => he.symm.injective (by simp only [map_mul, mul_comm])⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro a
    apply he.symm.injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.ext
    change (he.symm a).toAdd + (he.symm a).toAdd = 0
    apply Subtype.ext
    funext i
    exact CharTwo.add_self_eq_zero _

lemma subgroup_fixedSpace {A : Subgroup (SpecialLinearGroup (Fin n) F.Carrier)}
    (hA : A ≤ hyperplaneCentralizer F n j) (hne : A ≠ ⊥) :
    fixedSpace (linearNatural F n) A = (coordinateHyperplane F n j).restrictScalars (ZMod 2) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨w, hw⟩ := centralizer_eq_shear F n j (hA ha)
    have hw0 : w ≠ 0 := by
      intro hw0
      apply ha1
      apply Subtype.ext
      change a = 1
      rw [← hw, hw0, shear_zero]
    have hfix := hv ⟨a, ha⟩
    change linearNatural F n a v = v at hfix
    rw [← hw, shear_apply] at hfix
    have hz : v j • (w : Fin n → F.Carrier) = 0 := add_left_cancel (hfix.trans (add_zero v).symm)
    rcases smul_eq_zero.mp hz with hc | hwz
    · exact hc
    · exact False.elim (hw0 (Subtype.ext hwz))
  · intro v hv a
    exact (hA a.property).2 v hv

lemma subgroup_fixedCodim {A : Subgroup (SpecialLinearGroup (Fin n) F.Carrier)}
    (hA : A ≤ hyperplaneCentralizer F n j) (hne : A ≠ ⊥) :
    fixedCodim (linearNatural F n) A = F.degree := by
  unfold fixedCodim
  rw [subgroup_fixedSpace F n j hA hne,
    (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) (coordinateHyperplane F n j)).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F.Carrier, coordinateHyperplane_codim,
    field_finrank, mul_one]

lemma hyperplaneCentralizer_best (hn : 2 ≤ n) :
    IsBestOffender (linearNatural F n) (hyperplaneCentralizer F n j) := by
  have he := hyperplaneCentralizer_elementary F n j hn
  have hc := subgroup_fixedCodim F n j le_rfl he.1
  have hr := hyperplaneCentralizer_rank F n j
  have hoff : IsOffender (linearNatural F n) (hyperplaneCentralizer F n j) := by
    refine ⟨he, ?_⟩
    rw [hc, hr]
    exact Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨he, ?_⟩
  intro B hB
  by_cases hb : B = ⊥
  · rw [hb, weight_bot]
    exact (fixedCodim_le_rank_iff _ _).mp hoff.2
  · have hbC := subgroup_fixedSpace F n j hB hb
    have hXC := subgroup_fixedSpace F n j le_rfl he.1
    have hrB := Nat.log_monotone (b := 2) (Subgroup.card_le_of_le hB)
    unfold weight
    rw [hbC, hXC]
    exact Nat.add_le_add_right hrB _

lemma hyperplaneCentralizer_fullAxis : IsFullAxisGroup F n (hyperplaneCentralizer F n j) := by
  refine ⟨coordinateHyperplane F n j, coordinateHyperplane_codim F n j, ?_⟩
  intro g
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Subgroup.mem_top _, h⟩

lemma hyperplaneCentralizer_actionRatio (hn : 2 ≤ n) :
    actionRatio (linearNatural F n) (hyperplaneCentralizer F n j) = 1 / (n - 1 : ℕ) := by
  have hr : (F.degree : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt F.degree_pos)
  rw [actionRatio, subgroup_fixedCodim F n j le_rfl
    (hyperplaneCentralizer_elementary F n j hn).1, hyperplaneCentralizer_rank, Nat.cast_mul]
  simpa only [mul_one] using
    (ENNReal.mul_div_mul_left (1 : ℝ≥0∞) ((n - 1 : ℕ) : ℝ≥0∞) hr (by simp))

lemma quadraticRatio_eq (hn : 2 ≤ n) :
    quadraticRatio (linearNatural F n) = 1 / (n - 1 : ℕ) := by
  apply le_antisymm _ (quadraticRatio_ge F n hn)
  exact iInf_le_of_le (hyperplaneCentralizer F n ⟨0, by omega⟩)
    (iInf_le_of_le ⟨hyperplaneCentralizer_elementary F n _ hn,
      hyperplaneCentralizer_quadratic F n _⟩
      (hyperplaneCentralizer_actionRatio F n _ hn).le)

lemma transvection_mem_hyperplaneCentralizer (i : Fin n) (hij : i ≠ j) (c : F.Carrier) :
    SpecialLinearGroup.transvection hij c ∈ hyperplaneCentralizer F n j := by
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro v hv
  change (Matrix.transvection i j c).mulVec v = v
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec]
  have hvj : v j = 0 := hv
  simp [Matrix.single_mulVec, hvj]

lemma offenderSubgroup_eq_top (hn : 2 ≤ n) : offenderSubgroup (linearNatural F n) = ⊤ := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ offenderSubgroup (linearNatural F n))
    (fun i j hij c => ?_) (fun _ _ => (offenderSubgroup (linearNatural F n)).mul_mem) g
  exact (hyperplaneCentralizer_best F n j hn).le_offenderSubgroup _
    (transvection_mem_hyperplaneCentralizer F n j i hij c)

end CFSG.Quasithin.ChapterK.Linear.Natural
