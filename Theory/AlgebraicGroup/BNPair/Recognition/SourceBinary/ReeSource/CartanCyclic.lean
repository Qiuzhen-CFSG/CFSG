module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanFactors

/-!
# Cyclicity of the literal source linear Cartan image

The involutory root-group lift gives the actual faithful two-point subgroup.
The natural linear panel marking identifies it with a cyclic field-unit
torus. The entire source Cartan image lies in that subgroup, proving
cyclicity for the source action, including the field of order two.

Source: Fong--Seitz I (1973), proof of (6H)(a), p.51. The following
LinearActions consumer uses this with the proved image order to obtain
the regular action on the perpendicular source root.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

private theorem model_reflection_involution {M : Type*} [Group M]
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M)
    (B : Subgroup M) (hB : (quotientBorel Q i).map μ.toMonoidHom = B)
    (s : RootReflection Q split i) :
    let t := μ (QuotientGroup.mk' (panelKernel Q i)
      (rootReflectionEndpoint Q split i (involutoryRootReflection Q split i s)))
    IsInvolution t ∧ t ∉ B := by
  let r := involutoryRootReflection Q split i s
  let q := QuotientGroup.mk' (panelKernel Q i)
  let t := μ (q (rootReflectionEndpoint Q split i r))
  have htB : t ∉ B := by
    intro ht
    rw [← hB, mem_map_equiv] at ht
    have hc : q (rootReflectionEndpoint Q split i r) ∈ quotientBorel Q i := by
      simpa only [t, MulEquiv.symm_apply_apply] using ht
    exact rootReflectionProjection_not_mem_borel Q split i r hc
  have ht2 : t^2 = 1 := by
    have hr2 : (rootReflectionEndpoint Q split i r)^2 = 1 :=
      Subtype.ext (involutoryRootReflection_sq Q split i s)
    change (μ (q (rootReflectionEndpoint Q split i r)))^2 = 1
    rw [← map_pow, ← map_pow, hr2, map_one, map_one]
  change IsInvolution t ∧ t ∉ B
  exact ⟨⟨fun he => htB (he ▸ B.one_mem),ht2⟩,htB⟩

private theorem rightConjugate_eq_native {M : Type*} [Group M] (B : Subgroup M) (t : M) :
    rightConjugate B t = BenderSuzuki.PFchapter1section1.rightConjugate B t := by
  ext x
  exact (BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.mem_rightConjugate B t x).symm

theorem linear_cartanImage_cyclic (n : ℕ) (hn : 0 < n)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) : IsCyclic (cartanPanelMap Q i).range := by
  let r := involutoryRootReflection Q split i s
  obtain ⟨ht,htB⟩ := model_reflection_involution Q split i μ _ hB s
  have hcyc : IsCyclic (panelCartanPair Q split i r) := by
    apply (panelCartanPairEquiv Q split i μ _ hB r).isCyclic.mpr
    rw [rightConjugate_eq_native]
    exact (BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.twoPoint_cyclic_card hn
      (MulEquiv.refl (PSL2BinaryMatrixGroup n)) T ht htB).1
  let := hcyc
  exact isCyclic_of_injective (inclusion (cartanPanelMap_range_le_pair Q split i r))
    (inclusion_injective _)

/-- The actual Suzuki Cartan image is cyclic also when its parameter is zero. -/
theorem suzuki_cartanImage_cyclic (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) : IsCyclic (cartanPanelMap Q i).range := by
  by_cases hm : m = 0
  · subst m
    have hc : Nat.card (cartanPanelMap Q i).range = 1 := by
      simpa using suzuki_cartanImage_card Q split i 0 μ hB s
    let := (Nat.card_eq_one_iff_unique.mp hc).1
    infer_instance
  · have hmpos := Nat.pos_of_ne_zero hm
    rw [suzukiRootSubgroup_normalizer m hmpos] at hB
    let r := involutoryRootReflection Q split i s
    obtain ⟨ht,htB⟩ := model_reflection_involution Q split i μ _ hB s
    have hcyc : IsCyclic (panelCartanPair Q split i r) := by
      apply (panelCartanPairEquiv Q split i μ _ hB r).isCyclic.mpr
      rw [rightConjugate_eq_native]
      exact suzukiBorel_pair_isCyclic m hmpos _ ht htB
    let := hcyc
    exact isCyclic_of_injective (inclusion (cartanPanelMap_range_le_pair Q split i r))
      (inclusion_injective _)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
