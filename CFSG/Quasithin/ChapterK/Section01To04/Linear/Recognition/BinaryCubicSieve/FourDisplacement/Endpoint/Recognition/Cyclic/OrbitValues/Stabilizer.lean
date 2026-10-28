module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.Flags
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.ResidualUpper.Generation

/-!
# Highest-vector fixedness under the endpoint flag stabilizer

The stabilizer of (e₀,e₃*) preserves the first and third coordinate cuts.
Gaussian elimination expresses this partial-flag stabilizer using positive
roots and the lower middle root. The latter is a conjugate of the upper
middle root by the inactive coordinate exchange, so every generator fixes
an endpoint highest vector. The SL-to-linear-group comparison preserves the
literal matrix action throughout.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A. This supplies stabilizer
fixedness in the local-relation construction of the adjoint cyclic map.
-/

public section
open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.OrderedResidualConjugators BinaryLinear.OrderedResidualConjugators.ResidualUpper
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
set_option backward.isDefEq.respectTransparency false
private noncomputable abbrev stdBasis : BinaryLinear.InvariantNodeActions.Basis 3 := Pi.basisFun (ZMod 2) (Fin 4)

private theorem root_comparison (r s : Fin 4) (hrs : r ≠ s) :
    root stdBasis r s hrs = slEquivLinear 4 (Matrix.SpecialLinearGroup.transvection hrs 1) := by
  apply stdBasis.ext'
  intro k
  rw [root_basis]
  simp only [stdBasis, Pi.basisFun_apply, slEquivLinear_apply]
  by_cases hk : k = s <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.single_mulVec_eq, hk, -Matrix.mulVec_single]

private theorem cut_mem (i : Fin 3) (x : Natural) :
    x ∈ cutSpace stdBasis i ↔ ∀ r : Fin 4, i.val < r.val → x r = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  constructor
  · intro h r hr
    by_contra hn
    exact (Nat.not_le_of_gt hr) (h r (by simpa [stdBasis] using hn))
  · intro h r hr
    by_contra hn
    apply hr
    simpa [stdBasis] using h r (Nat.lt_of_not_ge hn)

private theorem stabilizer_mem_parabolic (g : Group) (hg : translate g seed = seed) :
    slEquivLinear 4 g ∈ minimalParabolic stdBasis 1 := by
  have hp : natural g (Pi.single 0 1) = Pi.single 0 1 := congrArg point hg
  have hc : form (Pi.single 3 1) ∘ₗ natural g⁻¹ = form (Pi.single 3 1) := by
    have hh := congrArg (fun a => form (covector a)) hg
    change form (dualTranslate g (covector seed)) = form (covector seed) at hh
    rw [form_dualTranslate] at hh
    exact hh
  have hf (x : Natural) : (natural g x) 3 = x 3 := by
    have hh := LinearMap.congr_fun hc (natural g x)
    have hi : natural g⁻¹ (natural g x) = x := by
      change (natural g⁻¹ * natural g) x = x
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    simpa only [LinearMap.comp_apply, hi, form_apply, single_one_dotProduct] using hh.symm
  apply (mem_cutStabilizer_maps stdBasis {1}ᶜ _).mpr
  intro i hi x hx
  have hii : i = 0 ∨ i = 2 := by
    have hi1 : i ≠ 1 := hi
    fin_cases i <;> tauto
  rcases hii with rfl | rfl
  · have he : x = x 0 • Pi.single 0 1 := by
      ext r
      have hz := (cut_mem 0 x).mp hx
      by_cases hr : r = 0
      · subst r; simp
      · rw [hz r (Fin.pos_iff_ne_zero.mpr hr)]
        simp [Pi.single_eq_of_ne hr]
    rw [he, map_smul]
    change x 0 • natural g (Pi.single 0 1) ∈ _
    rw [hp]
    apply (cutSpace stdBasis 0).smul_mem
    simpa only [stdBasis, Pi.basisFun_apply] using (basis_mem_cutSpace stdBasis 0 0).mpr le_rfl
  · apply (cut_mem 2 _).mpr
    intro r hr
    have hr3 : r = 3 := by omega
    subst r
    change (natural g x) 3 = 0
    rw [hf, (cut_mem 2 x).mp hx 3 (by decide)]

/-- Positive-root fixedness and the inactive middle exchange force the full
stabilizer of the highest-root flag to fix the highest vector. -/
theorem localHighest_stabilizer_fixed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ {0,2} v) (g : Group) (hg : translate g seed = seed) : σ g v = v := by
  have hl : σ (simpleLower 1) v = v := by
    rw [simpleLower_eq_swap_upper_swap, map_mul, map_mul]
    change σ (simpleSwap 1) (σ (simpleUpper 1) (σ (simpleSwap 1) v)) = v
    have hu : σ (simpleUpper 1) v = v := h.upper_fixed 1 2 (by decide)
    rw [h.inactive_fixed 1 (by decide), hu, h.inactive_fixed 1 (by decide)]
  let τ : Representation (ZMod 2) (LinearGroup 4) V := σ.comp (slEquivLinear 4).symm.toMonoidHom
  have hm : slEquivLinear 4 g ∈ elementaryParabolic stdBasis 1 :=
    minimalParabolic_le_elementaryParabolic stdBasis 1 (stabilizer_mem_parabolic g hg)
  have he : τ (slEquivLinear 4 g) = σ g := by simp [τ]
  rw [← he]
  suffices hall : ∀ k ∈ elementaryParabolic stdBasis 1, τ k v = v from hall _ hm
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem k hk =>
    obtain ⟨r, s, hrs, hallow, rfl⟩ := hk
    rw [root_comparison]
    change σ ((slEquivLinear 4).symm (slEquivLinear 4 _)) v = v
    rw [MulEquiv.symm_apply_apply]
    rcases hallow with hu | ⟨rfl, rfl⟩
    · exact h.upper_fixed r s hu
    · exact hl
  | one => simp
  | mul a b _ _ ha hb => simpa only [map_mul, Module.End.mul_apply, hb] using ha
  | inv a _ ha => exact τ.inv_apply_eq_iff.mpr ha.symm
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
