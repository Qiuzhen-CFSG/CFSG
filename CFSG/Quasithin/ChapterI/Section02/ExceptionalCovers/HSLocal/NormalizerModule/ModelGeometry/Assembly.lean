module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.ModelGeometry.Action
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.ModelGeometry.Incidence
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelResidual
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbit.Structure
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.ModelInput
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The source subgroups in the concrete HS normalizer geometry

The actual residual and core calculations identify the alternating preimage
T and pair kernel P with X₀ and R₀. Transporting the intrinsic center through
the literal inclusion identifies the cyclic factor W with V₀. The proved
concrete incidences therefore give A ≤ X₀, normal generation by V₀, and the
marked two-central involution in R₀ outside A.

The involution calculation also identifies the embedded first omega subgroup
with the elementary eight. An order-seven element extends to a Sylow subgroup;
its fixed-free action implies the required centralizer intersection is trivial.
Together these discharge every field of the abelian-section model input.
The cover centralizer hypotheses and the covering-group conclusions belong
to the normalizer assembly, not to these unconditional model calculations.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423;
GLS3 Table 5.3m.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore

/-- The concrete alternating preimage is the source's embedded two-residual. -/
theorem X₀_eq_T : X₀ = T := CentralizerRestriction.marked_centralizer_residual_eq

/-- The concrete pair kernel is the source's embedded residual two-core. -/
theorem R₀_eq_P : R₀ = P := CentralizerRestriction.marked_centralizer_core_eq

/-- The cyclic factor is the actual embedded center, with the original inclusions. -/
theorem V₀_eq_W : V₀ = W := by
  unfold V₀ HSLocal.coreCenter
  rw [CentralizerRestriction.marked_centralizer_core_eq,
    map_center_image_of_injective core (localGroup 0).subtype (localGroup 0).subtype_injective,
    ← map_map, CentralizerRestriction.model_core_center]
  rfl

theorem A_le_X₀ : A ≤ X₀ := by
  rw [X₀_eq_T]
  exact A_le_T

theorem V₀_le_A : V₀ ≤ A := by
  rw [V₀_eq_W]
  exact W_le_A

theorem V₀_le_normalizer : V₀ ≤ baseNormalizer := V₀_le_A.trans A_le_normalizer

/-- The source center normally generates precisely the literal normalizer core. -/
theorem V₀_normalClosure :
    normalClosure (V₀.subgroupOf baseNormalizer : Set baseNormalizer) =
      pCore 2 baseNormalizer := by
  rw [V₀_eq_W]
  exact W_normalClosure

theorem elementary_le_R₀ : baseElementary ≤ R₀ := by
  rw [R₀_eq_P]
  exact elementary_le_P

theorem j₀_mem_R₀ : j₀ ∈ R₀ := by
  rw [R₀_eq_P]
  exact j₀_mem_P

theorem j₀_mem_normalizer_inf_R₀ : j₀ ∈ baseNormalizer ⊓ R₀ :=
  ⟨j₀_mem_normalizer, j₀_mem_R₀⟩

/-- The marked normalizer witness has order two before taking a quotient. -/
theorem j₀Normalizer_order : orderOf j₀Normalizer = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact j₀_order

theorem j₀Normalizer_not_mem_core : j₀Normalizer ∉ pCore 2 baseNormalizer := by
  intro h
  exact j₀_not_mem_A (mem_map_of_mem baseNormalizer.subtype h)

/-- The exact omega-image premise used by the cover's Frattini calculation. -/
theorem core_omega_image :
    ((omega (pCore 2 baseNormalizer) (p := 2) 1).map
      (pCore 2 baseNormalizer).subtype).map baseNormalizer.subtype = baseElementary := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro q hq
    exact (CoreGeometry.core_involution_iff q).mp (by simpa only [Set.mem_ofPred_eq, pow_one] using hq)
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := elementary_le_A hx
    refine ⟨q, ⟨⟨q, hq⟩, subset_closure ?_, rfl⟩, rfl⟩
    simpa only [Set.mem_ofPred_eq, pow_one] using (CoreGeometry.core_involution_iff ⟨q, hq⟩).mpr hx

/-- A literal Sylow-seven subgroup has trivial centralizer in the two-core. -/
theorem exists_sylow_seven_centralizer_trivial : ∃ Y : Sylow 7 baseNormalizer,
    pCore 2 baseNormalizer ⊓ centralizer (Y : Set baseNormalizer) = ⊥ := by
  obtain ⟨y, hy, hfree⟩ := CoreGeometry.exists_seven_fixedPointFree
  have hp : IsPGroup 7 (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨Y, hY⟩ := hp.exists_le_sylow
  refine ⟨Y, eq_bot_iff.mpr ?_⟩
  intro x hx
  have hc : y * x = x * y := hx.2 y (hY (mem_zpowers y))
  have hf := hfree (⟨x, hx.1⟩ : pCore 2 baseNormalizer) (by
    apply Subtype.ext
    change y * x * y⁻¹ = x
    rw [hc, mul_inv_cancel_right])
  exact congrArg Subtype.val hf

/-- All model premises of the independent abelian-section argument are discharged. -/
noncomputable def abelianSectionModelInput : AbelianSection.ModelInput where
  coordinates := coreEquiv
  omega_image := core_omega_image
  seven := Classical.choose exists_sylow_seven_centralizer_trivial
  seven_fixed := Classical.choose_spec exists_sylow_seven_centralizer_trivial
  core_le_residual := A_le_X₀
  center_le_normalizer := V₀_le_normalizer
  center_generates := V₀_normalClosure
  elementary_le_core := elementary_le_R₀

/-- The precise odd-index premise used by the nonsplitting consumer. -/
theorem normalizer_index_not_even : ¬ 2 ∣ baseNormalizer.index :=
  normalizer_odd_index.not_two_dvd_nat

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
