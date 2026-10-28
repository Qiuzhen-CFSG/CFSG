module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.ProductSylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Coordinates for the Rudvalis component normalizer

The two factors below are literal images of the centralizer coordinates.
The product calculation proves centralizer containment in the component
normalizer. The layer calculation also transports a fused central involution
into that same normalizer. Neither calculation assumes an ambient normalizer
or centralizer table.

Source: GLS3, Table 5.3r; Aschbacher–Smith I.2.2(7), printed pp.412–413.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.CubicExtension
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped IsMulCommutative

variable {E : Type} [Group E]

/-- The actual second factor in the given centralizer coordinates. -/
@[expose] public noncomputable def componentFactor (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) : Subgroup Model :=
  ((centralizerEmbedding C eC).comp (MonoidHom.inr E (SuzukiMatrixGroup 1))).range

/-- The actual first factor in the same coordinates. -/
@[expose] public noncomputable def fourFactor (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) : Subgroup Model :=
  ((centralizerEmbedding C eC).comp (MonoidHom.inl E (SuzukiMatrixGroup 1))).range

public theorem componentFactor_le (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) : componentFactor C eC ≤ C := by
  rintro _ ⟨x, rfl⟩
  exact (eC.symm (1, x)).property

public theorem fourFactor_le (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) : fourFactor C eC ≤ C := by
  rintro _ ⟨x, rfl⟩
  exact (eC.symm (x, 1)).property

/-- A genuine equivalence to the precise matrix Suzuki carrier. -/
public noncomputable def componentEquiv (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) : componentFactor C eC ≃* SuzukiMatrixGroup 1 :=
  (MonoidHom.ofInjective
    (f := (centralizerEmbedding C eC).comp (MonoidHom.inr E (SuzukiMatrixGroup 1)))
    ((centralizerEmbedding_injective C eC).comp
      (fun _ _ h => congrArg Prod.snd h))).symm

public theorem factor_sup (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) :
    componentFactor C eC ⊔ fourFactor C eC = C := by
  apply le_antisymm (sup_le (componentFactor_le C eC) (fourFactor_le C eC))
  intro c hc
  let x := eC ⟨c, hc⟩
  have he : centralizerEmbedding C eC ((1, x.2) * (x.1, 1)) = c := by
    change (eC.symm ((1, x.2) * (x.1, 1)) : Model) = c
    simpa only [Prod.mk_mul_mk, one_mul, mul_one] using
      congrArg Subtype.val (eC.symm_apply_apply ⟨c, hc⟩)
  rw [← he, map_mul]
  exact (componentFactor C eC ⊔ fourFactor C eC).mul_mem
    ((show componentFactor C eC ≤ componentFactor C eC ⊔ fourFactor C eC from le_sup_left) (show centralizerEmbedding C eC (1, x.2) ∈ componentFactor C eC from ⟨x.2, rfl⟩))
    ((show fourFactor C eC ≤ componentFactor C eC ⊔ fourFactor C eC from le_sup_right) (show centralizerEmbedding C eC (x.1, 1) ∈ fourFactor C eC from ⟨x.1, rfl⟩))

public theorem fourFactor_centralizes [IsElementaryAbelian 2 E] (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) :
    fourFactor C eC ≤ centralizer (C : Set Model) := by
  rintro _ ⟨x, rfl⟩
  apply mem_centralizer_iff.mpr
  intro c hc
  have he : c = centralizerEmbedding C eC (eC ⟨c, hc⟩) :=
    (congrArg Subtype.val (eC.symm_apply_apply ⟨c, hc⟩)).symm
  rw [he]
  change centralizerEmbedding C eC (eC ⟨c, hc⟩) * centralizerEmbedding C eC (x, 1) =
    centralizerEmbedding C eC (x, 1) * centralizerEmbedding C eC (eC ⟨c, hc⟩)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (mul_comm _ _) (by simp)

public theorem fourFactor_square [IsElementaryAbelian 2 E] (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) {x : Model} (hx : x ∈ fourFactor C eC) :
    x ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := hx
  rw [← map_pow]
  have ha := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) a
  rw [ha, map_one]

/-- The centralizer normalizes its second direct factor. -/
public theorem centralizer_le_normalizer (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) :
    C ≤ normalizer (componentFactor C eC : Set Model) := by
  apply le_normalizer_iff.mpr
  intro c hc x hx
  obtain ⟨s, rfl⟩ := hx
  let a := eC ⟨c, hc⟩
  have he : c = centralizerEmbedding C eC a :=
    (congrArg Subtype.val (eC.symm_apply_apply ⟨c, hc⟩)).symm
  refine ⟨a.2 * s * a.2⁻¹, ?_⟩
  rw [he]
  change centralizerEmbedding C eC (1, a.2 * s * a.2⁻¹) =
    centralizerEmbedding C eC a * centralizerEmbedding C eC (1, s) *
      (centralizerEmbedding C eC a)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (by simp) rfl

private theorem layer_characteristic (C : Subgroup Model) :
    (componentLayer C).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro e
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro K hK
  exact map_le_iff_le_comap.mp (le_sSup (hK.map_equiv e))

/-- The identification with the actual layer is retained when its centralizer
is normalized. -/
public theorem normalizer_le_component_normalizer (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1)
    (hLayer : (componentLayer C).map C.subtype = componentFactor C eC) :
    normalizer (C : Set Model) ≤ normalizer (componentFactor C eC : Set Model) := by
  let := layer_characteristic C
  rw [← hLayer]
  exact normalizer_le_normalizer_characteristic_image C (componentLayer C)

/-- Fusion into the center of an element centralizer already normalizes that
centralizer. Finiteness turns containment into equality. -/
public theorem normalizes_centralizer_of_central_fusion (i g : Model)
    (hj : g * i * g⁻¹ ∈ centralizer (centralizer ({i} : Set Model) : Set Model)) :
    g ∈ normalizer (centralizer ({i} : Set Model) : Set Model) := by
  let C := centralizer ({i} : Set Model)
  let a := MulAut.conj g
  have hle : C ≤ C.map a.toMonoidHom := by
    intro x hx
    refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply a.injective
    simpa only [map_mul, a.apply_symm_apply, a, MulAut.conj_apply] using
      (mem_centralizer_iff.mp hj x hx)
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (eq_of_le_of_card_ge hle (by rw [card_map_of_injective a.injective])).symm

/-- A distinct fused central involution gives an actual component-normalizer
element outside the original centralizer. -/
public theorem exists_component_normalizer_outside [IsElementaryAbelian 2 E]
    (i : Model) (eC : centralizer ({i} : Set Model) ≃* E × SuzukiMatrixGroup 1)
    (hLayer : (componentLayer (centralizer ({i} : Set Model))).map
      (centralizer ({i} : Set Model)).subtype = componentFactor _ eC)
    (hfusion : ∃ g : Model, g * i * g⁻¹ ∈ fourFactor _ eC ∧ g * i * g⁻¹ ≠ i) :
    ∃ g ∈ normalizer (componentFactor _ eC : Set Model),
      g ∉ centralizer ({i} : Set Model) := by
  obtain ⟨g, hg, hne⟩ := hfusion
  refine ⟨g, normalizer_le_component_normalizer _ eC hLayer
    (normalizes_centralizer_of_central_fusion i g (fourFactor_centralizes _ eC hg)), ?_⟩
  intro hc
  exact hne (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc))

end Rudvalis.CoveringIncidence.NormalizerGeometry.CubicExtension
