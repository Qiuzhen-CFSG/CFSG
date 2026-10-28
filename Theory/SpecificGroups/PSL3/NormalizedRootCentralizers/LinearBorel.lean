module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootCoordinates
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear

/-!
# Uniform highest-root centralizers in PSL₃ and PGL₃

The full center of the upper unitriangular Sylow subgroup is the highest-root
subgroup, through its literal projective matrix embedding. In characteristic
two a transvection has trace one, so projective fixation by GL₃ lifts to exact
matrix commutation. Scaling its nonzero parameter proves fixation of the whole
root. Thus the calculation holds for every inner-diagonal actor, not merely
for actors in the Borel. The PGL₃ application uses the genuine central quotient
and its compatible PSL₃ embedding.

For source A.3.18(iii), this covers the diagonal alternative directly. In the
mixed field–diagonal alternative the ambient Borel need not have this property;
the Chapter 13 consumer first uses D = [D,T] to put D in the inner-diagonal
action. No field extension is replaced by a split extension.

Source: Aschbacher–Smith, A.3.16–18 and the proof of 13.6.6, printed p.927.
The trace lifting argument follows the local calculation in
`PSL3.LinearThreeSylow.PointwiseFixer.Coordinates`.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.NormalizedRootCentralizers
variable {F : Type*} [Field F]

private theorem scalar_of_projective_eq (x y : SL(3,F))
    (h : (QuotientGroup.mk x : PSL(3,F)) = QuotientGroup.mk y) :
    ∃ r : F, x.val = r • y.val := by
  have hc : y⁻¹ * x ∈ Subgroup.center SL(3,F) := QuotientGroup.eq.mp h.symm
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem trace_transvection [CharP F 2] {i j : Fin 3} (hij : i ≠ j) (c : F) :
    Matrix.trace (SpecialLinearGroup.transvection hij c).val = 1 := by
  simp [SpecialLinearGroup.transvection_coe, Matrix.trace_add, hij, Matrix.trace_one]
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination htwo

private theorem conjugate_transvection_eq [CharP F 2]
    (m : GL (Fin 3) F) {i j : Fin 3} (hij : i ≠ j)
    (a : F) (h : linearConj F m (rootElement hij a) = rootElement hij a) :
    m.val * (1 + Matrix.single i j a) = (1 + Matrix.single i j a) * m.val := by
  obtain ⟨r, hr⟩ := scalar_of_projective_eq
    (linearConjSL F m (SpecialLinearGroup.transvection hij a))
    (SpecialLinearGroup.transvection hij a) h
  have hv (x : SL(3,F)) : (linearConjSL F m x).val = m.val * x.val * m.inv :=
    congrArg Units.val (linearConjSL_toGL F m x)
  have ht : Matrix.trace (linearConjSL F m (SpecialLinearGroup.transvection hij a)).val = 1 := by
    rw [hv, Matrix.trace_mul_cycle, m.inv_val, one_mul, trace_transvection]
  rw [hr, Matrix.trace_smul, trace_transvection, smul_eq_mul, mul_one] at ht
  have he : (linearConjSL F m (SpecialLinearGroup.transvection hij a)).val =
      (SpecialLinearGroup.transvection hij a).val := by simpa [ht] using hr
  have he' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M * m.val) he
  simpa only [hv, Matrix.mul_assoc, m.inv_val, mul_one,
    SpecialLinearGroup.transvection_coe] using he'

/-- Fixing one nonzero root parameter fixes the entire root under any genuine
GL₃ conjugation, with the projective scalar ambiguity removed by trace. -/
theorem linearConj_fixes_root [CharP F 2]
    (m : GL (Fin 3) F) {i j : Fin 3} (hij : i ≠ j)
    {a : F} (ha : a ≠ 0)
    (h : linearConj F m (rootElement hij a) = rootElement hij a) (b : F) :
    linearConj F m (rootElement hij b) = rootElement hij b := by
  have he := conjugate_transvection_eq m hij a h
  simp only [mul_add, add_mul, mul_one, one_mul, add_right_inj] at he
  have hs : Matrix.single i j b = (b / a) • Matrix.single i j a := by
    ext k l
    simp [Matrix.single_apply, ha]
  have hb : m.val * Matrix.single i j b = Matrix.single i j b * m.val := by
    rw [hs, Matrix.mul_smul, Matrix.smul_mul, he]
  change QuotientGroup.mk (linearConjSL F m (SpecialLinearGroup.transvection hij b)) = _
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  apply Units.ext
  change m.val * (1 + Matrix.single i j b) * m.inv = 1 + Matrix.single i j b
  rw [mul_add, mul_one, hb, add_mul, Matrix.mul_assoc, m.val_inv, mul_one]

/-- The full embedded center is the actual highest-root group. -/
theorem center_unipotent_eq_rootGroup :
    (center (unipotent F)).map (unipotent F).subtype =
      rootGroup (F := F) (by decide : (0 : Fin 3) ≠ 2) := by
  rw [marked_center F (unipotent F) (unipotentEquiv F)]
  change (Z F).map (projective F) = _
  ext x
  change x ∈ projectiveCenter F ↔ _
  rw [mem_projectiveCenter]
  have he (a : F) : projective F ⟨0,0,a⟩ = rootElement (by decide : (0 : Fin 3) ≠ 2) a := by
    apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
    apply Subtype.ext
    change matrix F ⟨0,0,a⟩ = 1 + Matrix.single 0 2 a
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix]
  simp only [he]
  constructor
  · rintro ⟨a,rfl⟩
    exact rootElement_mem _ a
  · rintro ⟨a,rfl⟩
    exact ⟨a.toAdd,rfl⟩

/-- Inner-diagonal fixation is uniform on the full Sylow center. -/
theorem innerDiagonal_fixes_center [CharP F 2]
    (α : MulAut PSL(3,F)) (hα : α ∈ innerDiagonal F)
    (r : PSL(3,F)) (hr : r ∈ (center (unipotent F)).map (unipotent F).subtype)
    (hne : r ≠ 1) (hfix : α r = r) :
    ∀ x ∈ (center (unipotent F)).map (unipotent F).subtype, α x = x := by
  rw [center_unipotent_eq_rootGroup] at hr ⊢
  obtain ⟨a,rfl⟩ := hr
  obtain ⟨m,rfl⟩ := hα
  have ha : a.toAdd ≠ 0 := fun he => hne ((rootElement_eq_one_iff _ _).mpr he)
  rintro x ⟨b,rfl⟩
  exact linearConj_fixes_root m _ ha hfix b.toAdd

/-- Any compatible inner-diagonal action has uniform centralizers on the
embedded full Sylow center. No assertion about field actors is made. -/
theorem uniform_mapped_center [CharP F 2] {H : Type*} [Group H]
    (f : PSL(3,F) →* H) (hf : Function.Injective f)
    (ρ : H →* MulAut PSL(3,F))
    (hcompat : ∀ b x, f (ρ b x) = b * f x * b⁻¹)
    (B : Subgroup H) (hB : B.map ρ ≤ innerDiagonal F)
    (r : H)
    (hr : r ∈ ((center (unipotent F)).map (unipotent F).subtype).map f)
    (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set H) =
      B ⊓ centralizer ((((center (unipotent F)).map (unipotent F).subtype).map f :
        Subgroup H) : Set H) := by
  obtain ⟨r,hr,rfl⟩ := hr
  have hn : r ≠ 1 := fun he => hne (he ▸ f.map_one)
  apply le_antisymm
  · intro b hb
    have hfix : ρ b r = r := by
      apply hf
      rw [hcompat, mem_centralizer_singleton_iff.mp hb.2, mul_inv_cancel_right]
    have hall := innerDiagonal_fixes_center (ρ b) (hB (mem_map_of_mem ρ hb.1)) r hr hn hfix
    refine ⟨hb.1, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    have he : b * f x * b⁻¹ = f x := by rw [← hcompat, hall x hx]
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · exact inf_le_inf_left B (centralizer_le (Set.singleton_subset_iff.mpr
      (mem_map_of_mem f hr)))

/-- In particular the uniform calculation holds in every subgroup of PSL₃,
including its Borel. -/
theorem uniform [CharP F 2] (B : Subgroup PSL(3,F))
    (r : PSL(3,F)) (hr : r ∈ (center (unipotent F)).map (unipotent F).subtype)
    (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set PSL(3,F)) =
      B ⊓ centralizer (((center (unipotent F)).map (unipotent F).subtype :
        Subgroup PSL(3,F)) : Set PSL(3,F)) := by
  simpa only [Subgroup.map_id] using uniform_mapped_center (MonoidHom.id PSL(3,F))
    Function.injective_id (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F))
    (fun _ _ => rfl) B
    (by rintro _ ⟨b,hb,rfl⟩; exact inner_le_innerDiagonal F ⟨b,rfl⟩)
    r (by simpa only [Subgroup.map_id] using hr) hne

/-- Uniform centralizers in the actual projective general linear group,
using its literal PSL₃ embedding. In particular this applies to pglBorel. -/
theorem pgl_uniform [CharP F 2] (B : Subgroup (ProjGenLinGroup (Fin 3) F))
    (r : ProjGenLinGroup (Fin 3) F)
    (hr : r ∈ ((center (unipotent F)).map (unipotent F).subtype).map
      ProjectiveSpecialLinearGroup.toPGL) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (ProjGenLinGroup (Fin 3) F)) =
      B ⊓ centralizer ((((center (unipotent F)).map (unipotent F).subtype).map
        ProjectiveSpecialLinearGroup.toPGL : Subgroup (ProjGenLinGroup (Fin 3) F)) :
          Set (ProjGenLinGroup (Fin 3) F)) := by
  let ρ := (innerDiagonal F).subtype.comp (ExtensionBorel.pglEquivInnerDiagonal F).toMonoidHom
  apply uniform_mapped_center ProjectiveSpecialLinearGroup.toPGL
    ProjectiveSpecialLinearGroup.toPGL_injective ρ ?_ B ?_ r hr hne
  · intro b x
    obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective b
    exact (DFunLike.congr_fun (ExtensionBorel.pgl_component_conj F g) x).symm
  · rintro _ ⟨b,hb,rfl⟩
    exact (ExtensionBorel.pglEquivInnerDiagonal F b).property

end Matrix.PSL3.NormalizedRootCentralizers
