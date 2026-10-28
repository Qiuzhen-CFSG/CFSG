module

public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity
public import Theory.GroupTheory.AutomorphismExtensionBorel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Concrete triangular Borels in PGL₃ and its automorphism realization

The Borel consists of invertible upper triangular matrices, projected into
PGL₃ or acting on the actual PSL₃ component. Triangular conjugation preserves
the upper-unitriangular subgroup; the converse follows from its fixed flag
and the characteristic-two trace calculation in `NormalizerForm.BorelKernel`.

Perfectness of SL₃ and the elementary matrices identify the kernel of its
projective conjugation action with the scalar center of GL₃. The resulting
whole-group equivalence PGL₃ ≃ InnDiag(PSL₃) preserves both the original
component embeddings and the concrete Borels. No automorphism coverage or
simple-group classification is assumed.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, Lemma A.3.18, printed pp.51–52,
and the diagonal case and Borel placement in 13.6.6, printed p.927. Matrix
conventions follow GLS3 §2.7. The imported ATLAS elementary-matrix proof of
SL₃ perfectness retains its original attribution and license.
-/

@[expose] public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.ExtensionBorel
variable (F : Type*) [Field F]
private theorem diagonal_ne_zero (g : GL (Fin 3) F)
    (hg : g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0) (i : Fin 3) :
    g.val i i ≠ 0 := by
  have hn := (GeneralLinearGroup.det g).ne_zero
  change Matrix.det g.val ≠ 0 at hn
  rw [Matrix.det_fin_three] at hn
  simp only [hg.1, hg.2.1, hg.2.2, mul_zero, zero_mul, sub_zero, add_zero] at hn
  fin_cases i
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  · exact (mul_ne_zero_iff.mp hn).2

/-- The invertible upper triangular matrices, defined by their three zero entries. -/
def glBorel : Subgroup (GL (Fin 3) F) where
  carrier := {g | g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨g10,g20,g21⟩ ⟨h10,h20,h21⟩
    change (g.val * h.val) 1 0 = 0 ∧ (g.val * h.val) 2 0 = 0 ∧ (g.val * h.val) 2 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, g10,g20,g21,h10,h20,h21]
  inv_mem' := by
    intro g hg
    have h20 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 0) g.val_inv
    have h21 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 1) g.val_inv
    simp only [Matrix.mul_apply, Fin.sum_univ_three, hg.2.1,hg.2.2,
      zero_mul,zero_add, Matrix.one_apply, Fin.reduceEq, if_false] at h20 h21
    have i20 : g.inv 2 0 = 0 := (mul_eq_zero.mp h20).resolve_left (diagonal_ne_zero F g hg 2)
    have i21 : g.inv 2 1 = 0 := (mul_eq_zero.mp h21).resolve_left (diagonal_ne_zero F g hg 2)
    have h10 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 1 0) g.val_inv
    simp only [Matrix.mul_apply, Fin.sum_univ_three, hg.1,i20,
      zero_mul,mul_zero,zero_add,add_zero, Matrix.one_apply, Fin.reduceEq, if_false] at h10
    exact ⟨(mul_eq_zero.mp h10).resolve_left (diagonal_ne_zero F g hg 1), i20, i21⟩

theorem mem_glBorel (g : GL (Fin 3) F) : g ∈ glBorel F ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := Iff.rfl

private theorem linearConjSL_val (g : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F g x).val = g.val * x.val * (g⁻¹).val :=
  congrArg Units.val (linearConjSL_toGL F g x)

private theorem triangular_preserves (g : GL (Fin 3) F) (hg : g ∈ glBorel F)
    (u : SL(3,F)) (hu : u ∈ unipotentSL F) :
    linearConjSL F g u ∈ unipotentSL F := by
  obtain ⟨g10,g20,g21⟩ := hg
  obtain ⟨i10,i20,i21⟩ := (glBorel F).inv_mem ⟨g10,g20,g21⟩
  have h00 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 0) g.val_inv
  have h22 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 2) g.val_inv
  change (g.val * (g⁻¹).val) 0 0 = 1 at h00
  change (g.val * (g⁻¹).val) 2 2 = 1 at h22
  simp only [Matrix.mul_apply, Fin.sum_univ_three,
    i10,i20,g20,g21,mul_zero,zero_mul,add_zero,zero_add] at h00 h22
  have hu' := (mem_unipotentSL_iff F u).mp hu
  rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
  rw [linearConjSL_val, hu']
  simp [-Matrix.coe_units_inv, Matrix.mul_apply,
    Fin.sum_univ_three, g10,g20,g21,i10,i20,i21,h00,h22]

/-- Upper triangular conjugation preserves the projective upper-unitriangular group. -/
theorem linearConj_preserves (g : GL (Fin 3) F) (hg : g ∈ glBorel F) :
    (unipotent F).map (linearConj F g).toMonoidHom = unipotent F := by
  have hf (a : GL (Fin 3) F) (ha : a ∈ glBorel F) :
      ∀ x ∈ unipotent F, linearConj F a x ∈ unipotent F := by
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨linearConjSL F a u, triangular_preserves F a ha u hu, rfl⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hf g hg x hx
  · intro x hx
    refine ⟨linearConj F g⁻¹ x, hf g⁻¹ ((glBorel F).inv_mem hg) x hx, ?_⟩
    change (linearConj F g * linearConj F g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

/-- The exact triangular-matrix criterion for preserving the projective root group. -/
theorem linearConj_preserves_iff [CharP F 2] (g : GL (Fin 3) F) :
    (unipotent F).map (linearConj F g).toMonoidHom = unipotent F ↔ g ∈ glBorel F :=
  ⟨NormalizerForm.linearConj_upperTriangular F g, linearConj_preserves F g⟩

private theorem scalar_action (a : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) a) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := projection_surjective F y
  change projection F (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) a) x) = projection F x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

/-- Projective conjugation is trivial exactly on scalar GL₃ matrices. -/
theorem linearConj_ker : (linearConj F).ker = center (GL (Fin 3) F) := by
  apply le_antisymm
  · intro g hg
    have hs : linearConjSL F g = 1 :=
      ActorCoverage.centerAction_injective F (hg.trans (map_one _).symm)
    have hc (x : SL(3,F)) : g * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * g := by
      have he := congrArg SpecialLinearGroup.toGL (DFunLike.congr_fun hs x)
      rw [linearConjSL_toGL] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact (congrArg Units.val (hc ⟨t.toMatrix, by simp⟩)).symm
  · intro g hg
    rw [GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a,rfl⟩ := hg
    exact scalar_action F a

/-- The compatible equivalence on the entire PGL₃ group, not only its component. -/
noncomputable def pglEquivInnerDiagonal : ProjGenLinGroup (Fin 3) F ≃* innerDiagonal F :=
  (QuotientGroup.quotientMulEquivOfEq (linearConj_ker F).symm).trans
    (QuotientGroup.quotientKerEquivRange (linearConj F))

theorem pglEquiv_mk (g : GL (Fin 3) F) :
    (pglEquivInnerDiagonal F (ProjGenLinGroup.mk g)).val = linearConj F g := rfl

theorem pglEquiv_component (x : PSL(3,F)) :
    (pglEquivInnerDiagonal F (ProjectiveSpecialLinearGroup.toPGL x)).val = MulAut.conj x := by
  obtain ⟨y,rfl⟩ := projection_surjective F x
  exact linearConj_toGL F y

/-- The actual PSL₃ component embeds faithfully by inner automorphisms. -/
theorem inner_injective : Function.Injective (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro g hg
  have hz : g ∈ center PSL(3,F) := by
    apply mem_center_iff.mpr
    intro x
    have hx := DFunLike.congr_fun hg x
    change g * x * g⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  rwa [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)] at hz

/-- The image of triangular matrices in the actual automorphism group. -/
def linearBorel : Subgroup (MulAut PSL(3,F)) := (glBorel F).map (linearConj F)

/-- The root stabilizer among inner-diagonal actors is the triangular image. -/
theorem linear_preserves_iff [CharP F 2] (a : MulAut PSL(3,F)) (ha : a ∈ innerDiagonal F) :
    (unipotent F).map a.toMonoidHom = unipotent F ↔ a ∈ linearBorel F := by
  obtain ⟨g,rfl⟩ := ha
  constructor
  · intro h
    exact Subgroup.mem_map_of_mem _ ((linearConj_preserves_iff F g).mp h)
  · rintro ⟨h,hh,he⟩
    rw [← he]
    exact linearConj_preserves F h hh

/-- The concrete PGL₃ Borel, the projective image of upper triangular matrices. -/
def pglBorel : Subgroup (ProjGenLinGroup (Fin 3) F) := (glBorel F).map ProjGenLinGroup.mk

/-- The PGL action and projective linear conjugation agree on the original component. -/
theorem pgl_component_conj (g : GL (Fin 3) F) :
    (MulAut.conj (ProjGenLinGroup.mk g) : ProjGenLinGroup (Fin 3) F →* _).comp
      ProjectiveSpecialLinearGroup.toPGL =
      ProjectiveSpecialLinearGroup.toPGL.comp (linearConj F g).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  obtain ⟨u,rfl⟩ := projection_surjective F x
  change ProjGenLinGroup.mk g * ProjGenLinGroup.mk (SpecialLinearGroup.toGL u) *
    (ProjGenLinGroup.mk g)⁻¹ = ProjGenLinGroup.mk (SpecialLinearGroup.toGL (linearConjSL F g u))
  rw [linearConjSL_toGL, map_mul, map_mul, map_inv]

/-- The root normalizer in actual PGL₃ equals the concrete triangular Borel. -/
theorem normalizer_pgl_root [CharP F 2] :
    normalizer ((unipotent F).map ProjectiveSpecialLinearGroup.toPGL :
      Set (ProjGenLinGroup (Fin 3) F)) = pglBorel F := by
  ext x
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_map, pgl_component_conj,
    ← Subgroup.map_map, (Subgroup.map_injective ProjectiveSpecialLinearGroup.toPGL_injective).eq_iff]
  constructor
  · intro h
    exact Subgroup.mem_map_of_mem _ ((linearConj_preserves_iff F g).mp h)
  · rintro ⟨h,hh,he⟩
    have ha := congrArg (fun z => (pglEquivInnerDiagonal F z).val) he
    rw [pglEquiv_mk, pglEquiv_mk] at ha
    rw [← ha]
    exact linearConj_preserves F h hh

open Theory.GroupTheory.AutomorphismExtensionBorel

/-- The whole-group equivalence respects the literal component embeddings. -/
theorem pglEquiv_innerEmbedding (x : PSL(3,F)) :
    pglEquivInnerDiagonal F (ProjectiveSpecialLinearGroup.toPGL x) =
      innerEmbedding (innerDiagonal F) (inner_le_innerDiagonal F) x :=
  Subtype.ext (pglEquiv_component F x)

/-- The same whole-group equivalence identifies the concrete Borels. -/
theorem pglEquiv_borel : (pglBorel F).map (pglEquivInnerDiagonal F).toMonoidHom =
    (linearBorel F).subgroupOf (innerDiagonal F) := by
  apply Subgroup.map_injective (innerDiagonal F).subtype_injective
  have hb : linearBorel F ≤ innerDiagonal F := Subgroup.map_le_range _ _
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hb]
  rw [pglBorel, Subgroup.map_map, Subgroup.map_map]
  have he : ((innerDiagonal F).subtype.comp
      (pglEquivInnerDiagonal F).toMonoidHom).comp ProjGenLinGroup.mk = linearConj F := by
    apply MonoidHom.ext
    intro g
    exact pglEquiv_mk F g
  rw [he]
  rfl

/-- Each actual diagonal actor lies in the concrete linear Borel. -/
theorem diagonal_mem_linearBorel (d : Fin 3 → Fˣ) :
    linearConj F (OuterSolvable.OddPrimeCoverage.diagonalGL d) ∈ linearBorel F := by
  apply Subgroup.mem_map_of_mem
  change (OuterSolvable.OddPrimeCoverage.diagonalGL d).val 1 0 = 0 ∧
    (OuterSolvable.OddPrimeCoverage.diagonalGL d).val 2 0 = 0 ∧
    (OuterSolvable.OddPrimeCoverage.diagonalGL d).val 2 1 = 0
  simp [OuterSolvable.OddPrimeCoverage.diagonalGL]

/-- The diagonal source case in actual PGL, using the existing component Sylow. -/
theorem normalizer_source_pgl [Finite F] {m : ℕ} (hm : 1 < m)
    (hF : Nat.card F = 2 ^ m) :
    normalizer (((unipotentSylow F (by omega) hF : Subgroup PSL(3,F)).map
      ProjectiveSpecialLinearGroup.toPGL) : Set (ProjGenLinGroup (Fin 3) F)) = pglBorel F := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt (show 0 < m by omega)])
  let : CharP F 2 := ringChar.of_eq hc
  exact normalizer_pgl_root F

end Matrix.PSL3.ExtensionBorel
