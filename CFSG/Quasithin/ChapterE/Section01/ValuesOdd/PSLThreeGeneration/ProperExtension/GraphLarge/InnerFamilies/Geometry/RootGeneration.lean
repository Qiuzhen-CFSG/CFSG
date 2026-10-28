module

public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure.Action
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Matrix witnesses for inner-centralizer generation

The centralizer of diag(-1,-1,1) supplies all x₀₁(a). A determinant-one
matrix fixing the first coordinate and mixing coordinates 1 and 2 then
supplies all x₀₂(a), by a direct row calculation. Inverse transpose lies in
the full graph-extension centralizer, so the opposite roots are also present.
Root commutators and elementary generation give the entire inner group;
the graph element then gives the entire extension.

The witness retains both its actual SL₃ matrix and the inner conjugator
aligning the original involution. No maximality of the inner centralizer is
asserted. These calculations consume the concrete local witnesses needed
for Aschbacher--Smith E.1.14(7), printed p.214, via the subgroup controls
from E.1.2 and E.1.5, printed pp.209--210. Witness existence is separate.

Elementary generation is reused from the attributed ATLAS port
`Theory/AtlasPort/ExceptionalIsomorphisms/Elementary.lean`; its attribution
and license remain in that module and `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
open Matrix.PSL3 Matrix.PSL3.OuterSolvable

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
variable (F : Type*) [Field F]

private theorem graphSL_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) :
    graphSL F (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm (-a) := by
  change (SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a))⁻¹ = _
  have h : SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm a := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transpose, SpecialLinearGroup.transvection_coe,
      Matrix.transpose_add, Matrix.transpose_single]
  rw [h, SpecialLinearGroup.transvection_inv]

private theorem root_commute_standard (i j : Fin 3) (hij : i ≠ j)
    (hi : i ≠ 2) (hj : j ≠ 2) (a : F) :
    SpecialLinearGroup.transvection hij a ∈
      centralizer ({SL3.standardInvolution F} : Set SL(3,F)) := by
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  change (1 + single i j a) * (SL3.standardInvolution F).val =
    (SL3.standardInvolution F).val * (1 + single i j a)
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]

private theorem root_plane_identity (x : SL(3,F))
    (h00 : x.val 0 0 = 1) (h01 : x.val 0 1 = 0) (h02 : x.val 0 2 = 0)
    (h10 : x.val 1 0 = 0) (h20 : x.val 2 0 = 0) (s : F) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) s * x =
      x * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (s * x.val 1 1) *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (s * x.val 1 2) := by
  apply Subtype.ext
  change (1 + single 0 1 s) * x.val =
    x.val * (1 + single 0 1 (s * x.val 1 1)) * (1 + single 0 2 (s * x.val 1 2))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h01, h02, h10, h20]

private theorem sl_eq_top_of_block_plane (H : Subgroup SL(3,F))
    (hC : centralizer ({SL3.standardInvolution F} : Set SL(3,F)) ≤ H)
    (hgraph : ∀ y ∈ H, graphSL F y ∈ H)
    (x : SL(3,F)) (hx : x ∈ H)
    (h00 : x.val 0 0 = 1) (h01 : x.val 0 1 = 0) (h02 : x.val 0 2 = 0)
    (h10 : x.val 1 0 = 0) (h20 : x.val 2 0 = 0) (h12 : x.val 1 2 ≠ 0) :
    H = ⊤ := by
  have h01' (a : F) : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a ∈ H :=
    hC (root_commute_standard F 0 1 (by decide) (by decide) (by decide) a)
  have h02' (a : F) : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a ∈ H := by
    have hid := root_plane_identity F x h00 h01 h02 h10 h20 (a / x.val 1 2)
    have hh : x * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide)
        (a / x.val 1 2 * x.val 1 1) *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide)
        (a / x.val 1 2 * x.val 1 2) ∈ H :=
      hid ▸ H.mul_mem (h01' _) hx
    have hroot := (H.mul_mem_cancel_left (H.mul_mem hx (h01' _))).mp hh
    simpa only [div_mul_cancel₀ _ h12] using hroot
  have h10' (a : F) : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) a ∈ H := by
    simpa only [graphSL_transvection, neg_neg] using hgraph _ (h01' (-a))
  have h20' (a : F) : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a ∈ H := by
    simpa only [graphSL_transvection, neg_neg] using hgraph _ (h02' (-a))
  have h12' (a : F) : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a ∈ H := by
    rw [← mul_one a, ← Atlas.elementary_commutator (show (1 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) (show (0 : Fin 3) ≠ 2 by decide) a 1]
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h10' a) (h02' 1)) (H.inv_mem (h10' a)))
      (H.inv_mem (h02' 1))
  have h21' (a : F) : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a ∈ H := by
    simpa only [graphSL_transvection, neg_neg] using hgraph _ (h12' (-a))
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun y => y ∈ H) _ (fun _ _ => H.mul_mem) g
  intro i j hij a
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01' a
  · exact h02' a
  · exact h10' a
  · exact (hij rfl).elim
  · exact h12' a
  · exact h20' a
  · exact h21' a
  · exact (hij rfl).elim

open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3.OddInvolutionFixed

/-- The literal conjugation image of a determinant-one matrix. -/
@[expose] def innerSL : SL(3,F) →* graphExtension F :=
  (MulAut.conj.comp (projection F)).codRestrict (graphExtension F) (by
    intro x
    exact mem_sup_left ⟨projection F x, rfl⟩)

@[expose] def graphElement : graphExtension F :=
  ⟨graph F, mem_sup_right (mem_zpowers _)⟩

@[expose] def standardInner : graphExtension F := innerSL F (SL3.standardInvolution F)

private theorem innerSL_graph (x : SL(3,F)) :
    innerSL F (graphSL F x) = graphElement F * innerSL F x * (graphElement F)⁻¹ := by
  apply Subtype.ext
  change MulAut.conj (projection F (graphSL F x)) =
    graph F * MulAut.conj (projection F x) * (graph F)⁻¹
  have he : projection F (graphSL F x) = graph F (projection F x) := rfl
  rw [he]
  ext y
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem graphSL_standard : graphSL F (SL3.standardInvolution F) = SL3.standardInvolution F := by
  change (SpecialLinearGroup.transpose (SL3.standardInvolution F))⁻¹ = _
  have ht : SpecialLinearGroup.transpose (SL3.standardInvolution F) = SL3.standardInvolution F := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [ht]
  symm
  apply eq_inv_of_mul_eq_one_left
  exact (pow_two _).symm.trans (SL3.standardInvolution_sq F)

private theorem graphElement_centralizes_standard :
    graphElement F ∈ centralizer ({standardInner F} : Set (graphExtension F)) := by
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  change graphElement F * innerSL F (SL3.standardInvolution F) * (graphElement F)⁻¹ = _
  rw [← innerSL_graph, graphSL_standard]
  rfl

private theorem innerSL_range : (innerSL F).range = innerPart F := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨projection F g, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨g, rfl⟩ := projection_surjective F y
    exact ⟨g, Subtype.ext hy⟩

/-- A concrete off-block matrix and the full standard centralizer generate the graph extension. -/
theorem eq_top_of_standard_block_plane (M : Subgroup (graphExtension F))
    (hC : centralizer ({standardInner F} : Set (graphExtension F)) ≤ M)
    (x : SL(3,F)) (hx : innerSL F x ∈ M)
    (h00 : x.val 0 0 = 1) (h01 : x.val 0 1 = 0) (h02 : x.val 0 2 = 0)
    (h10 : x.val 1 0 = 0) (h20 : x.val 2 0 = 0) (h12 : x.val 1 2 ≠ 0) :
    M = ⊤ := by
  have hgamma : graphElement F ∈ M := hC (graphElement_centralizes_standard F)
  have hpre : M.comap (innerSL F) = ⊤ := by
    apply sl_eq_top_of_block_plane F _ _ _ x hx h00 h01 h02 h10 h20 h12
    · intro y hy
      apply hC
      apply mem_centralizer_singleton_iff.mpr
      exact (map_mul (innerSL F) y _).symm.trans
        ((congrArg (innerSL F) (mem_centralizer_singleton_iff.mp hy)).trans
          (map_mul (innerSL F) _ y))
    · intro y hy
      change innerSL F (graphSL F y) ∈ M
      rw [innerSL_graph]
      exact M.mul_mem (M.mul_mem hgamma hy) (M.inv_mem hgamma)
  have hI : innerPart F ≤ M := by
    rw [← innerSL_range]
    rintro y ⟨x, rfl⟩
    exact show x ∈ M.comap (innerSL F) from hpre ▸ mem_top x
  have hgen : innerPart F ⊔ zpowers (graphElement F) = ⊤ := by
    apply (Subgroup.map_injective (graphExtension F).subtype_injective)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map]
    change ((MulAut.innerSubgroup PSL(3,F)).subgroupOf (graphExtension F)).map _ ⊔
      zpowers (graph F) = _
    rw [map_subgroupOf_eq_of_le (show MulAut.innerSubgroup PSL(3,F) ≤ graphExtension F from le_sup_left)]
    rw [range_subtype]
    rfl
  apply top_unique
  rw [← hgen]
  exact sup_le hI (zpowers_le.mpr hgamma)

/-- A determinant-one matrix fixing the first coordinate and mixing the last two. -/
@[expose] def MixesSecondPlane (x : SL(3,F)) : Prop :=
  x.val 0 0 = 1 ∧ x.val 0 1 = 0 ∧ x.val 0 2 = 0 ∧
    x.val 1 0 = 0 ∧ x.val 2 0 = 0 ∧ x.val 1 2 ≠ 0

/-- An actual matrix witness, with the inner conjugator aligning the original involution. -/
@[expose] def HasMixingElement (z : graphExtension F) (H : Subgroup (graphExtension F)) : Prop :=
  ∃ s : SL(3,F), innerSL F s * standardInner F * (innerSL F s)⁻¹ = z ∧
    ∃ x : SL(3,F), MixesSecondPlane F x ∧
      innerSL F s * innerSL F x * (innerSL F s)⁻¹ ∈ H

/-- Transport the explicit root calculation along its original matrix conjugator. -/
theorem eq_top_of_mixing (z : graphExtension F) (M : Subgroup (graphExtension F))
    (hC : centralizer ({z} : Set (graphExtension F)) ≤ M)
    (hmix : HasMixingElement F z M) : M = ⊤ := by
  obtain ⟨s, hs, x, ⟨h00, h01, h02, h10, h20, h12⟩, hx⟩ := hmix
  let e := MulAut.conj (innerSL F s)
  have hez : e (standardInner F) = z := hs
  have hpre : M.comap e.toMonoidHom = ⊤ := by
    apply eq_top_of_standard_block_plane F _ _ x hx h00 h01 h02 h10 h20 h12
    intro y hy
    apply hC
    apply mem_centralizer_singleton_iff.mpr
    change e y * z = z * e y
    rw [← hez, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hy]
  apply top_unique
  intro y _
  obtain ⟨w, rfl⟩ := e.surjective y
  exact show w ∈ M.comap e.toMonoidHom from hpre ▸ mem_top w

theorem HasMixingElement.mono {z : graphExtension F} {H K : Subgroup (graphExtension F)}
    (h : HasMixingElement F z H) (hHK : H ≤ K) : HasMixingElement F z K := by
  obtain ⟨s, hs, x, hx, hmem⟩ := h
  exact ⟨s, hs, x, hx, hHK hmem⟩

/-- Standard coordinates for any inner involution in the literal graph extension. -/
theorem exists_standard_coordinates [Finite F] [IsSimpleGroup PSL(3,F)]
    (h2 : (2 : F) ≠ 0) (z : graphExtension F) (hz : orderOf z = 2) (hzI : z ∈ innerPart F) :
    ∃ s : SL(3,F), innerSL F s * standardInner F * (innerSL F s)⁻¹ = z := by
  let w : innerPart F := ⟨z, hzI⟩
  let y := (innerPartEquiv F).symm w
  have hy : orderOf y = 2 := by
    rw [MulEquiv.orderOf_eq, ← orderOf_submonoid]
    exact hz
  obtain ⟨u, hu, hproj⟩ := involution_lift y hy
  obtain ⟨s, hs⟩ := SL3.exists_standardInvolution_conjugator F u hu h2
  refine ⟨s, ?_⟩
  have he : innerSL F u = z := by
    apply Subtype.ext
    change MulAut.conj (projection F u) = z.val
    rw [hproj]
    exact innerPartEquiv_symm_conj F w
  rw [← he]
  change innerSL F s * innerSL F (SL3.standardInvolution F) * (innerSL F s)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hs]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
