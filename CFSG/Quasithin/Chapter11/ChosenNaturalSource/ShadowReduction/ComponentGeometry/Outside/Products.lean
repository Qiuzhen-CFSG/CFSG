module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Decomposition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Reduction

/-!
# The literal products in source 11.4.3

The point and line normalizers use the same K/O₂(K) action. The equality
Kz=K supplies relative normality in the point centralizer. For the line
normalizer we first apply Frattini inside C_G(V₁)T, then use 11.2.3.
Both joins are converted to actual three-factor products.

The outer-group two-closedness remains an explicit model input; it is
not inferred from a family label. EarlierGeometry and Kz=K belong to
the preceding source producers. Source: Aschbacher--Smith, 11.4.3, p.778.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The component comparison supplies normality in the point centralizer. -/
theorem point_normalizes_component (he : E.Kz = E.K) :
    Gz E ≤ normalizer (E.K : Set G) := by
  rw [← he]
  exact le_normalizer_conjugateSpanBy _ _

/-- The actual quotient centralizer is normal relative to Gz. -/
theorem point_normalizes_kernel (he : E.Kz = E.K) :
    Gz E ≤ normalizer (Yz E : Set G) :=
  (le_inf (Gz E).le_normalizer ((point_normalizes_component E he).trans
    (Closure.normalizer_normalizes_coreQuotientCentralizer E.K))).trans
      inf_normalizer_le_normalizer_inf

/-- Source 11.4.3(1), with the outer model fact still displayed. -/
theorem point_decomposition (h : Comparison.EarlierGeometry E) (he : E.Kz = E.K)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (ho : ChapterE.IsTwoClosed (MulAut.Outer (E.K ⧸ pCore 2 E.K))) :
    Gz E = E.K ⊔ Yz E ⊔ Mz E := by
  have hn := point_normalizes_component E he
  exact decomposition_of_outer_image E.K (Gz E) E.M (he ▸ h.point_component.1) hn
    h.sylow_le_pointCentralizer hNT (outerAction_range_twoClosed _ _ hn ho)

/-- Source 11.4.3(2). The preceding 11.2.3 supplement is used only at
this last step, after the actual centralizer product has been established. -/
theorem line_decomposition (h : Comparison.EarlierGeometry E)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (ho : ChapterE.IsTwoClosed (MulAut.Outer (E.K ⧸ pCore 2 E.K))) :
    E.G₁ = E.K ⊔ E.Y ⊔ E.M₁ := by
  let C := centralizer (E.V₁ : Set G)
  let J := C ⊔ (T : Subgroup G)
  have hJG : J ≤ E.G₁ := sup_le (Subgroup.centralizer_le_normalizer _) hT
  have hn : J ≤ normalizer (E.K : Set G) := hJG.trans E.G₁_normalizes_K
  have hc : J ≤ normalizer (C : Set G) :=
    hJG.trans (normalizer_le_normalizer_centralizer E.V₁)
  have hj := decomposition_on_normal_subgroup E.K C J E.M h.line_component_centralizes
    le_sup_left hn hc le_sup_right rfl hNT (outerAction_range_twoClosed _ _ hn ho)
  have hJbound : J ≤ E.K ⊔ E.Y ⊔ E.M₁ := by
    calc
      J = E.K ⊔ E.Y ⊔ (E.M ⊓ J) := hj
      _ ≤ E.K ⊔ E.Y ⊔ E.M₁ := sup_le_sup_left (inf_le_inf_left E.M hJG) _
  apply le_antisymm
  · calc
      E.G₁ = C ⊔ E.M₁ := h.normalizer_split hf
      _ ≤ E.K ⊔ E.Y ⊔ E.M₁ := sup_le (le_sup_left.trans hJbound) le_sup_right
  · exact sup_le (sup_le E.K_le_G₁ E.Y_le_G₁) inf_le_right

omit [Finite G] in
private theorem triple_product {J K Y M : Subgroup G}
    (he : J = K ⊔ Y ⊔ M) (hMJ : M ≤ J) (hYJ : Y ≤ J)
    (hK : J ≤ normalizer (K : Set G)) (hY : J ≤ normalizer (Y : Set G)) :
    ∀ g ∈ J, ∃ k ∈ K, ∃ y ∈ Y, ∃ m ∈ M, g = k * y * m := by
  intro g hg
  have hM : M ≤ normalizer ((K ⊔ Y : Subgroup G) : Set G) :=
    (le_inf (hMJ.trans hK) (hMJ.trans hY)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [he] at hg
  change g ∈ ((K ⊔ Y ⊔ M : Subgroup G) : Set G) at hg
  rw [coe_mul_of_right_le_normalizer_left _ _ hM] at hg
  obtain ⟨a, ha, m, hm, rfl⟩ := hg
  change a ∈ ((K ⊔ Y : Subgroup G) : Set G) at ha
  rw [coe_mul_of_right_le_normalizer_left _ _ (hYJ.trans hK)] at ha
  obtain ⟨k, hk, y, hy, rfl⟩ := ha
  exact ⟨k, hk, y, hy, m, hm, rfl⟩

/-- The point-centralizer equality is the literal product in the source. -/
theorem point_product (h : Comparison.EarlierGeometry E) (he : E.Kz = E.K)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (ho : ChapterE.IsTwoClosed (MulAut.Outer (E.K ⧸ pCore 2 E.K))) :
    ∀ g ∈ Gz E, ∃ k ∈ E.K, ∃ y ∈ Yz E, ∃ m ∈ Mz E, g = k * y * m :=
  triple_product (point_decomposition E h he hNT ho) inf_le_right inf_le_left
    (point_normalizes_component E he) (point_normalizes_kernel E he)

/-- The line-normalizer equality is also an actual product. -/
theorem line_product (h : Comparison.EarlierGeometry E)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (ho : ChapterE.IsTwoClosed (MulAut.Outer (E.K ⧸ pCore 2 E.K))) :
    ∀ g ∈ E.G₁, ∃ k ∈ E.K, ∃ y ∈ E.Y, ∃ m ∈ E.M₁, g = k * y * m := by
  have hY : E.G₁ ≤ normalizer (E.Y : Set G) :=
    (le_inf (normalizer_le_normalizer_centralizer E.V₁)
      (E.G₁_normalizes_K.trans
        (Closure.normalizer_normalizes_coreQuotientCentralizer E.K))).trans
          inf_normalizer_le_normalizer_inf
  exact triple_product (line_decomposition E h hT hf hNT ho) inf_le_right E.Y_le_G₁
    E.G₁_normalizes_K hY

/-- The equal-component consequence of 11.4.3(1), using the already proved
outside selection to obtain the required point-centralizer escape. -/
theorem kernel_outside_of_equal (h : Comparison.EarlierGeometry E) (he : E.Kz = E.K)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (ho : ChapterE.IsTwoClosed (MulAut.Outer (E.K ⧸ pCore 2 E.K)))
    (h1132 : ∀ H, Hypothesis1131At D E.input E.point H →
      Proposition1132At D E.input E.point H)
    (hKL : E.K = E.L₁) : ¬ Yz E ≤ E.M := by
  obtain ⟨H, hH, hHz⟩ := exists_outside_in_pointCentralizer E
    h.point_mem h.point_fixed h.point_ne_one h1132
  intro hY
  apply hH.1.2
  apply hHz.trans
  calc
    Gz E = E.K ⊔ Yz E ⊔ Mz E := point_decomposition E h he hNT ho
    _ ≤ E.M := sup_le (sup_le (hKL ▸ E.L₁_le.trans L.le_normalizer) hY) inf_le_left

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
