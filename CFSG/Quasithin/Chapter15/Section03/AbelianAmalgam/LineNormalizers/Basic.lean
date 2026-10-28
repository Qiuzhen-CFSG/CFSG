module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Constructions
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Residual, product, and span steps for the line normalizers

The two-residual of the line centralizer is normal in the full line
normalizer, because the centralizer is normal there and residuals commute
with automorphisms. Similarly, `T_E` normalizes `Y_E` whenever `T` normalizes
`Y`, so their join is their setwise product.

A surjective action of a subgroup of `G_E` on `E` gives a product with
`C_G(E)`, by correcting each element by an element with the same action.
Taking inverses reverses this product and shows that the conjugate span
`V_E` is generated already by the centralizer. Its containment in the span
from 15.3.50 then proves abelianness.

The full action on the singular line, `Z ≤ E`, the Thompson calculation,
and the recognition in 15.3.67 remain separate obligations. In particular,
normality below is relative to `G_E`, and the action-surjectivity and
factorization premises must be supplied by the geometric calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 15.3.66–67, printed pp.1152–1153, PDF pp.1169–1170.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G]

/-- `Y_E` lies in the relative normalizer used to define it. -/
theorem lineY_le (Y E : Subgroup G) : lineY Y E ≤ Y ⊓ lineNormalizer E :=
  map_subtype_le _

/-- `X_E` lies in the centralizer used to define it. -/
theorem lineX_le_centralizer (E : Subgroup G) :
    lineX E ≤ centralizer (E : Set G) := map_subtype_le _

/-- The line Sylow intersection normalizes the line residual. -/
theorem lineT_le_normalizer_lineY [Finite G] (Y T E : Subgroup G)
    (hTY : T ≤ normalizer (Y : Set G)) :
    lineT T E ≤ normalizer (lineY Y E : Set G) := by
  have hN : lineT T E ≤ normalizer (Y ⊓ lineNormalizer E : Set G) :=
    (le_inf (inf_le_left.trans hTY)
      (inf_le_right.trans (lineNormalizer E).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact map_twoResidualAmbient_of_subgroup_image (Y ⊓ lineNormalizer E)
    (MulAut.conj g).toMonoidHom (Y ⊓ lineNormalizer E)
    (mem_normalizer_iff_map_conj_eq.mp (hN hg))

/-- The join of the line residual and the Sylow intersection is their product. -/
theorem lineY_sup_lineT_product [Finite G] (Y T E : Subgroup G)
    (hTY : T ≤ normalizer (Y : Set G)) :
    ((lineY Y E ⊔ lineT T E : Subgroup G) : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) :=
  coe_mul_of_right_le_normalizer_left _ _ (lineT_le_normalizer_lineY Y T E hTY)

/-- The full line normalizer normalizes the residual of the line centralizer. -/
theorem lineNormalizer_le_normalizer_lineX [Finite G] (E : Subgroup G) :
    lineNormalizer E ≤ normalizer (lineX E : Set G) := by
  have hNC : lineNormalizer E ≤ normalizer (centralizer (E : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (E : Set G))).mp
      inferInstance
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact map_twoResidualAmbient_of_subgroup_image (centralizer (E : Set G))
    (MulAut.conj g).toMonoidHom (centralizer (E : Set G))
    (mem_normalizer_iff_map_conj_eq.mp (hNC hg))

/-- The relative normality assertion for `X_E` in 15.3.67(3). -/
theorem lineX_normal_in_lineNormalizer [Finite G] (E : Subgroup G) :
    ((lineX E).subgroupOf (lineNormalizer E)).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))).mpr
      (lineNormalizer_le_normalizer_lineX E)

/-- Correct a normalizer element by an element inducing the same automorphism of `E`. -/
theorem lineNormalizer_factorization_of_full_action (E A : Subgroup G)
    (hA : A ≤ lineNormalizer E)
    (honto : Function.Surjective (E.normalizerMonoidHom.comp (inclusion hA))) :
    ∀ g ∈ lineNormalizer E, ∃ a ∈ A, ∃ c ∈ centralizer (E : Set G), g = a * c := by
  intro g hg
  let gN : lineNormalizer E := ⟨g, hg⟩
  obtain ⟨a, ha⟩ := honto (E.normalizerMonoidHom gN)
  let aN : lineNormalizer E := inclusion hA a
  have hc : aN⁻¹ * gN ∈ E.normalizerMonoidHom.ker := by
    change E.normalizerMonoidHom (aN⁻¹ * gN) = 1
    rw [map_mul, map_inv, show E.normalizerMonoidHom aN = E.normalizerMonoidHom gN from ha,
      inv_mul_cancel]
  rw [E.normalizerMonoidHom_ker] at hc
  refine ⟨a, a.property, (a : G)⁻¹ * g, hc, ?_⟩
  simp

/-- The setwise-product form of the correction, used in 15.3.66(6). -/
theorem lineNormalizer_product_of_full_action (E A : Subgroup G)
    (hA : A ≤ lineNormalizer E)
    (honto : Function.Surjective (E.normalizerMonoidHom.comp (inclusion hA))) :
    (lineNormalizer E : Set G) = (A : Set G) * (centralizer (E : Set G) : Set G) := by
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨a, ha, c, hc, rfl⟩ := lineNormalizer_factorization_of_full_action E A hA honto g hg
    exact Set.mul_mem_mul ha hc
  · rintro g ⟨a, ha, c, hc, rfl⟩
    exact mul_mem (hA ha) (centralizer_le_normalizer (E : Set G) hc)

/-- The centralizer containment 15.3.66(7), once `Z ≤ E` is established. -/
theorem centralizer_line_le_of_Z_le (E Z Mc : Subgroup G)
    (hZE : Z ≤ E) (hMc : Mc = centralizer (Z : Set G)) :
    centralizer (E : Set G) ≤ Mc := by
  rw [hMc]
  exact centralizer_le hZE

/-- The line span lies in the local span from 15.3.50. -/
theorem lineV_le_localSpan_of_factorization (V E M Mc A : Subgroup G)
    (hM : M ≤ normalizer (V : Set G)) (hAM : A ≤ M)
    (hC : centralizer (E : Set G) ≤ Mc)
    (hprod : ∀ g ∈ lineNormalizer E, ∃ a ∈ A, ∃ c ∈ centralizer (E : Set G), g = a * c) :
    lineV V E ≤ conjugateSpanBy V Mc := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g, hg, v, hv, rfl⟩
  obtain ⟨a, ha, c, hc, he⟩ := hprod g⁻¹ (inv_mem hg)
  have hg' : g = c⁻¹ * a⁻¹ := by simpa using congrArg Inv.inv he
  have hv' : a⁻¹ * v * a ∈ V := by
    simpa only [inv_inv, SetLike.mem_coe] using
      (hM (hAM (A.inv_mem ha)) v).mp hv
  apply Subgroup.subset_closure
  refine ⟨c⁻¹, Mc.inv_mem (hC hc), a⁻¹ * v * a, hv', ?_⟩
  rw [hg']
  group

/-- The centralizer alone generates the full line-normalizer span of `V`. -/
theorem lineV_eq_centralizerSpan_of_factorization (V E A : Subgroup G)
    (hA : A ≤ normalizer (V : Set G))
    (hprod : ∀ g ∈ lineNormalizer E, ∃ a ∈ A, ∃ c ∈ centralizer (E : Set G), g = a * c) :
    lineV V E = conjugateSpanBy V (centralizer (E : Set G)) := by
  apply le_antisymm
  · exact lineV_le_localSpan_of_factorization V E (normalizer (V : Set G))
      (centralizer (E : Set G)) A le_rfl hA le_rfl hprod
  · exact conjugateSpanBy_mono le_rfl (centralizer_le_normalizer (E : Set G))

/-- Transfer abelianness from the local span to `V_E`. -/
theorem lineV_abelian_of_factorization (V E M Mc A : Subgroup G)
    (hM : M ≤ normalizer (V : Set G)) (hAM : A ≤ M)
    (hC : centralizer (E : Set G) ≤ Mc)
    (hprod : ∀ g ∈ lineNormalizer E, ∃ a ∈ A, ∃ c ∈ centralizer (E : Set G), g = a * c)
    [IsMulCommutative (conjugateSpanBy V Mc)] : IsMulCommutative (lineV V E) := by
  have hle := lineV_le_localSpan_of_factorization V E M Mc A hM hAM hC hprod
  exact le_centralizer_iff_isMulCommutative.mp
    (hle.trans ((conjugateSpanBy V Mc).le_centralizer.trans (centralizer_le hle)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
