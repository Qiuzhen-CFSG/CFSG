module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Theory.GroupTheory.PResidual.CubicCoreIndex

/-!
# Intrinsic kernels in the ordinary Borel product

The literal source residuals make B and J = BL₁ two-perfect. The theta
identity makes L₁ normal in J, so its two-core lies in O₂(J). The
nontrivial natural A₄ image proves B_C ≠ J. These facts and the proved
cubic quotient give the repaired index once the product factorization
has been established by the action-image calculation.

Separately, an abelian Borel quotient is odd by two-perfectness of B.
It follows that O³(B) = O²(O³(B)) O₂(B). This does not assume the
unresolved placement of O²(O³(B)) in B_C.

Source: Aschbacher–Smith 13.7.3(9), p.936, and the sufficient two-kernel
calculation for 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.TwoKernels
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)

/-- B is the embedded two-residual of the actual Borel preimage. -/
theorem borel_isPPerfect : IsPPerfect 2 d.B := isPPerfect_embedded_pResidual 2 _

/-- The theta identity of 13.7.3(9) supplies relative normality of L₁. -/
theorem product_normalizes_one : d.B ⊔ one L (T : Subgroup G) V₁ ≤
    normalizer (one L (T : Subgroup G) V₁ : Set G) := by
  let J := d.B ⊔ one L (T : Subgroup G) V₁
  apply le_normalizer_iff.mpr
  intro g hg x hx
  rw [d.theta_product] at hx ⊢
  have hm : closure {y : G | y ∈ J ∧ orderOf y = 3} ≤
      (closure {y : G | y ∈ J ∧ orderOf y = 3}).comap (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    intro y hy
    apply Subgroup.subset_closure
    refine ⟨J.mul_mem (J.mul_mem hg hy.1) (J.inv_mem hg), ?_⟩
    exact ((MulAut.conj g).orderOf_eq y).trans hy.2
  exact hm hx

/-- Joining the two literal residuals supplies two-perfectness of BL₁. -/
theorem product_isPPerfect : IsPPerfect 2 (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) := by
  let J := d.B ⊔ one L (T : Subgroup G) V₁
  have hB : IsPPerfect 2 d.B := borel_isPPerfect d
  have hD : IsPPerfect 2 (one L (T : Subgroup G) V₁) := residual_isPPerfect _
  have hBR : residualIn 2 d.B = d.B := by
    unfold residualIn
    rw [(pResidual_eq_top_iff 2 _).mpr hB, ← MonoidHom.range_eq_map, range_subtype]
  have hDR : residualIn 2 (one L (T : Subgroup G) V₁) = one L (T : Subgroup G) V₁ := by
    unfold residualIn
    rw [(pResidual_eq_top_iff 2 _).mpr hD, ← MonoidHom.range_eq_map, range_subtype]
  have hj : residualIn 2 J = J := by
    apply le_antisymm (map_subtype_le _)
    apply sup_le
    · rw [← hBR]
      exact embedded_pResidual_mono 2 le_sup_left
    · rw [← hDR]
      exact embedded_pResidual_mono 2 le_sup_right
  apply (pResidual_eq_top_iff 2 J).mp
  apply map_injective J.subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact hj

/-- Normality of L₁ places its intrinsic core in the product's intrinsic core. -/
theorem one_core_le_product_core :
    (one L (T : Subgroup G) V₁).pCoreIn 2 ≤
      (d.B ⊔ one L (T : Subgroup G) V₁).pCoreIn 2 :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
    ((pCoreIn_le 2 _).trans le_sup_right)
    ((product_normalizes_one d).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- The literal centralizing residual is normal relative to BL₁. -/
theorem product_normalizes_centralizingResidual :
    d.B ⊔ one L (T : Subgroup G) V₁ ≤
      normalizer (centralizingResidual d.B (one L (T : Subgroup G) V₁) L : Set G) :=
  centralizingResidual_normalized _ _ _ _ d.product_normalizes_L
    (d.B ⊔ one L (T : Subgroup G) V₁).le_normalizer d.product_normalizes_L

/-- A₄ in the genuine natural action prevents the kernel residual from filling BL₁. -/
theorem centralizingResidual_ne_product (a : NaturalSetup L (T : Subgroup G) V V₁) :
    centralizingResidual d.B (one L (T : Subgroup G) V₁) L ≠
      d.B ⊔ one L (T : Subgroup G) V₁ := by
  intro he
  have h := twelve_le_centralizingResidual_index a d.B d.product_normalizes_L
  rw [he, relIndex_self] at h
  omega

/-- The correct denominator gives index three once the model image proves J = CL₁.
All other index hypotheses are discharged here from the genuine source setup. -/
theorem cubic_index_of_factorization (a : NaturalSetup L (T : Subgroup G) V V₁)
    (hfactor : d.B ⊔ one L (T : Subgroup G) V₁ =
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ one L (T : Subgroup G) V₁) :
    (centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔
      (d.B ⊔ one L (T : Subgroup G) V₁).pCoreIn 2).relIndex
        (d.B ⊔ one L (T : Subgroup G) V₁) = 3 :=
  cubic_relIndex_sup_pCoreIn _ _ _ hfactor.symm
    (product_normalizes_centralizingResidual d) (product_isPPerfect d)
    (source_residual_quotient_card a _ rfl) (one_core_le_product_core d)
    (centralizingResidual_ne_product d a)

/-- The actual two-residual definition of B supplies the needed odd quotient order. -/
theorem borel_quotient_odd (hab : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2) :
    Odd (Nat.card (d.B ⧸ pCore 2 d.B)) :=
  odd_card_quotient_twoCore_of_isPPerfect d.B (borel_isPPerfect d) hab

/-- The repaired residual supplement, with oddness proved before using it. -/
theorem borel_threeResidual (hab : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2) :
    residualIn 3 d.B = residualIn 2 (residualIn 3 d.B) ⊔ d.B.pCoreIn 2 :=
  threeResidual_twoResidual_sup_twoCore d.B (borel_quotient_odd d hab)

/-- Every chosen member of T normalizes both B and the actual product J. -/
theorem marked_normalizes (t : G) (ht : t ∈ (T : Subgroup G)) :
    t ∈ normalizer (d.B : Set G) ∧
      t ∈ normalizer ((d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) : Set G) :=
  ⟨d.borel_normalized (mem_sup_right ht), d.T_normalizes_product ht⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.TwoKernels
