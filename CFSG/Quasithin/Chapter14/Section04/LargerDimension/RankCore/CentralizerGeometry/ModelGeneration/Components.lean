module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.ComponentAction
/-!
# The marked orthogonal component square

The checked orthogonal equivalence identifies Ω⁺₄(4) with A₅ × A₅. We
embed the two coordinate factors in the actual normal residual, prove they
are distinct and generate it, and prove that the first is a subnormal
quasisimple component of the ambient quotient. The source element swapping
these factors then generates the residual by the component dichotomy.
No component is assumed normal in the ambient quotient.

Source: Aschbacher–Smith, 14.4.2(3) and 14.4.7, printed pp.1006,1009.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
variable {Q : Type*} [Group Q]
local notation "A5" => alternatingGroup (Fin 5)
private def leftAxis : Subgroup (A5 × A5) := (⊤ : Subgroup A5).prod ⊥
private def rightAxis : Subgroup (A5 × A5) := (⊥ : Subgroup A5).prod ⊤
private def leftEquiv : leftAxis ≃* A5 where
  toFun x := x.val.1
  invFun x := ⟨(x,1), mem_top _, one_mem _⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (mem_bot.mp x.property.2).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl
private theorem axis_sup : leftAxis ⊔ rightAxis = ⊤ := by
  apply top_unique
  rintro ⟨a,b⟩ _
  simpa using (mul_mem_sup (show (a,1) ∈ leftAxis from ⟨mem_top _,one_mem _⟩)
    (show (1,b) ∈ rightAxis from ⟨one_mem _,mem_top _⟩))
private theorem axes_ne : leftAxis ≠ rightAxis := by
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨a,ha⟩ := exists_ne (1 : A5)
  intro hh
  have h : (a,1) ∈ rightAxis := hh ▸ (show (a,1) ∈ leftAxis from ⟨mem_top _,one_mem _⟩)
  exact ha (mem_bot.mp h.1)
private theorem a5_quasisimple : IsQuasisimple A5 where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

private def leftFactor (K : Subgroup Q) (e : K ≃* A5 × A5) : Subgroup Q :=
  (leftAxis.map e.symm.toMonoidHom).map K.subtype
private def rightFactor (K : Subgroup Q) (e : K ≃* A5 × A5) : Subgroup Q :=
  (rightAxis.map e.symm.toMonoidHom).map K.subtype

private theorem left_component (K : Subgroup Q) [K.Normal] (e : K ≃* A5 × A5) :
    IsComponent Q (leftFactor K e) := by
  let : leftAxis.Normal := inferInstanceAs (((⊤ : Subgroup A5).prod (⊥ : Subgroup A5)).Normal)
  let : (leftAxis.map e.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.symm.surjective
  let := a5_quasisimple
  refine ⟨(inferInstance : (leftAxis.map e.symm.toMonoidHom).Normal).isSubnormal.trans'
    (inferInstance : K.Normal).isSubnormal, ?_⟩
  exact IsQuasisimple.of_mulEquiv (leftEquiv.symm.trans
    ((leftAxis.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      ((leftAxis.map e.symm.toMonoidHom).equivMapOfInjective K.subtype K.subtype_injective)))
private theorem factor_sup (K : Subgroup Q) (e : K ≃* A5 × A5) :
    leftFactor K e ⊔ rightFactor K e = K := by
  unfold leftFactor rightFactor
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, axis_sup,
    map_top_of_surjective _ e.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
private theorem factor_ne (K : Subgroup Q) (e : K ≃* A5 × A5) :
    leftFactor K e ≠ rightFactor K e := by
  intro hh
  exact axes_ne (Subgroup.map_injective e.symm.injective
    (Subgroup.map_injective K.subtype_injective hh))

private theorem swapped_component_generation (K L₁ L₂ X : Subgroup Q) [K.Normal]
    (hcomponent : IsComponent Q L₁)
    (hK : K = L₁ ⊔ L₂) (hL₁K : L₁ ≤ K)
    (hXK : X ≤ normalizer (K : Set Q)) (hne : L₁ ≠ L₂)
    (hinter : ∃ x : X,
      L₁.map (MulAut.conj (x : Q)).toMonoidHom = L₂) :
    ⁅K, X⁆ = K := by
  obtain ⟨x, hx⟩ := hinter
  have horbit_le : (⨆ a : X, L₁.map (MulAut.conj (a : Q)).toMonoidHom) ≤ K := by
    apply iSup_le
    intro a
    have hmapK := mem_normalizer_iff_map_conj_eq.mp (hXK a.property)
    rw [← hmapK]
    exact map_mono hL₁K
  have horbit_ge : K ≤ (⨆ a : X, L₁.map (MulAut.conj (a : Q)).toMonoidHom) := by
    rw [hK]
    apply sup_le
    · exact le_iSup_of_le (1 : X) (by
        convert (le_rfl : L₁ ≤ L₁) using 1; ext y; simp)
    · rw [← hx]
      exact le_iSup (fun a : X => L₁.map (MulAut.conj (a : Q)).toMonoidHom) x
  have horbit : (⨆ a : X, L₁.map (MulAut.conj (a : Q)).toMonoidHom) = K :=
    le_antisymm horbit_le horbit_ge
  have hnotcentral : ¬ X ≤ centralizer (L₁ : Set Q) := by
    intro hc
    have hxl := (centralizer_le_normalizer (L₁ : Set Q)) (hc x.property)
    have heq := mem_normalizer_iff_map_conj_eq.mp hxl
    exact hne (heq.symm.trans hx)
  rcases hcomponent.commutator_dichotomy X with hb | he
  · rw [commutator_comm] at hb
    exact (hnotcentral (commutator_eq_bot_iff_le_centralizer.mp hb)).elim
  · rw [horbit] at he
    apply le_antisymm (commutator_le_left K X)
    calc
      K = ⁅L₁, X⁆ := he.symm
      _ ≤ ⁅K, X⁆ := commutator_mono hL₁K le_rfl


private theorem square_generation (K X : Subgroup Q) [K.Normal] (e : K ≃* A5 × A5)
    (hswap : ∃ x : X, (leftFactor K e).map (MulAut.conj (x : Q)).toMonoidHom = rightFactor K e) :
    ⁅K,X⁆ = K := by
  apply swapped_component_generation K (leftFactor K e) (rightFactor K e) X
    (left_component K e) (factor_sup K e).symm
    ((le_sup_left : leftFactor K e ≤ leftFactor K e ⊔ rightFactor K e).trans (factor_sup K e).le)
    le_normalizer_of_normal (factor_ne K e) hswap


/-- The literal elementary Ω⁺₄(4) carrier in determinant-model factor coordinates. -/
def orthogonalFactorCoordinates :
    ClassicalOrthogonal.OmegaPlus 2 ClassicalOrthogonal.FourPlusMatrix.Binary.F ≃* A5 × A5 :=
  ClassicalOrthogonal.FourPlusMatrix.elementaryEquiv.symm.trans
    (ClassicalOrthogonal.FourPlusMatrix.QuotientLocal.factorAlternatingEquiv.prodCongr
      ClassicalOrthogonal.FourPlusMatrix.QuotientLocal.factorAlternatingEquiv)

/-- First actual component, marked through the determinant-model equivalence. -/
def orthogonalLeftFactor (K : Subgroup Q)
    (e : K ≃* ClassicalOrthogonal.OmegaPlus 2 ClassicalOrthogonal.FourPlusMatrix.Binary.F) :
    Subgroup Q :=
  (((⊤ : Subgroup A5).prod ⊥).map (e.trans orthogonalFactorCoordinates).symm.toMonoidHom).map
    K.subtype

/-- Second actual component in the same orthogonal coordinates. -/
def orthogonalRightFactor (K : Subgroup Q)
    (e : K ≃* ClassicalOrthogonal.OmegaPlus 2 ClassicalOrthogonal.FourPlusMatrix.Binary.F) :
    Subgroup Q :=
  (((⊥ : Subgroup A5).prod ⊤).map (e.trans orthogonalFactorCoordinates).symm.toMonoidHom).map
    K.subtype

/-- The source component interchange, with right conjugation, generates the
actual orthogonal residual. The inverse actor converts to Mathlib conjugation. -/
theorem orthogonal_residual_generation (X : Subgroup Q)
    (e : pResidual 2 Q ≃*
      ClassicalOrthogonal.OmegaPlus 2 ClassicalOrthogonal.FourPlusMatrix.Binary.F)
    (hswap : ∃ x : X,
      conjugate (orthogonalLeftFactor (pResidual 2 Q) e) (x : Q) =
        orthogonalRightFactor (pResidual 2 Q) e) :
    ⁅pResidual 2 Q, X⁆ = pResidual 2 Q := by
  apply square_generation _ X (e.trans orthogonalFactorCoordinates)
  obtain ⟨x, hx⟩ := hswap
  exact ⟨x⁻¹, hx⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
