module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Conjugation
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.FixedComplement
public import Mathlib.LinearAlgebra.Projection

/-!
# Internal coordinates for any selected solvable factor subfamily

Restriction of the independent group factors and natural supports gives
actual product equivalences on any injectively indexed subfamily. The
selected supports have the fixed space of their product as complement;
all coordinate maps agree with the original subgroup and subspace inclusions.
This is the internal-coordinate step of solvable Thompson factorization
B.2.16(2), using B.1.8, printed pp.70 and79.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
open scoped BigOperators
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)
variable {n : ℕ} (f : Fin n → Fin d.count) (hf : Function.Injective f)

include hf in
theorem selectedCommute : Pairwise fun i j => ∀ x y : G, x ∈ d.factor (f i) →
    y ∈ d.factor (f j) → Commute x y := by
  intro i j hij x y hx hy
  exact d.factor_commute (fun he => hij (hf he)) ⟨x,hx⟩ ⟨y,hy⟩

noncomputable def selectedGroupProduct : ((i : Fin n) → d.factor (f i)) ≃*
    (⨆ i, d.factor (f i) : Subgroup G) := by
  classical
  let hc := d.selectedCommute f hf
  exact (MonoidHom.ofInjective (Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (hcomm := hc) (d.factors_independent.comp hf))).trans
      (MulEquiv.subgroupCongr (Subgroup.noncommPiCoprod_range (hcomm := hc)))

@[simp] theorem selectedGroupProduct_single (i : Fin n) (g : d.factor (f i)) :
    (d.selectedGroupProduct f hf (Pi.mulSingle i g) : G) = g := by
  classical
  exact Subgroup.noncommPiCoprod_mulSingle (hcomm := d.selectedCommute f hf) i g

noncomputable def selectedSupportSum :
    ((i : Fin n) → subspaceCommutator ρ ⊤ (d.factor (f i))) ≃ₗ[ZMod 2]
      (⨆ i, subspaceCommutator ρ ⊤ (d.factor (f i)) : Submodule (ZMod 2) V) := by
  classical
  let W := fun i => subspaceCommutator ρ ⊤ (d.factor (f i))
  let s : ((i : Fin n) → W i) →ₗ[ZMod 2] V :=
    LinearMap.lsum (ZMod 2) (fun i => W i) (ZMod 2) (fun i => (W i).subtype)
  have hs (v : (i : Fin n) → W i) : s v = ∑ i, (v i : V) := by
    simp only [s, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply]
  have hi : Function.Injective s := by
    intro v w hvw
    have he := (iSupIndep_iff_finsetSum_eq_imp_eq W).mp
      (d.supports_independent.comp hf) Finset.univ
      (fun i => (v i : V)) (fun i => (w i : V))
      (fun i _ => ⟨(v i).property,(w i).property⟩)
      (by simpa only [hs] using hvw)
    funext i
    exact Subtype.ext (he i (Finset.mem_univ i))
  have hr : s.range = ⨆ i, W i := by
    apply le_antisymm
    · rintro _ ⟨v,rfl⟩
      rw [hs]
      exact Submodule.sum_mem _ fun i _ => (le_iSup W i) (v i).property
    · apply iSup_le
      intro i v hv
      refine ⟨Pi.single i (⟨v,hv⟩ : W i), ?_⟩
      simpa [s] using (LinearMap.lsum_piSingle (ZMod 2) (fun i => W i) (ZMod 2) (fun i => (W i).subtype) i (⟨v,hv⟩ : W i))
  exact (LinearEquiv.ofInjective s hi).trans (LinearEquiv.ofEq _ _ hr)

@[simp] theorem selectedSupportSum_single (i : Fin n)
    (v : subspaceCommutator ρ ⊤ (d.factor (f i))) :
    (d.selectedSupportSum f hf (Pi.single i v) : V) = v := by
  classical
  exact LinearMap.lsum_piSingle (ZMod 2)
    (fun i => subspaceCommutator ρ ⊤ (d.factor (f i))) (ZMod 2)
    (fun i => (subspaceCommutator ρ ⊤ (d.factor (f i))).subtype) i v

theorem selected_isCompl :
    IsCompl (fixedSpace ρ (⨆ i, d.factor (f i)))
      (⨆ i, subspaceCommutator ρ ⊤ (d.factor (f i))) := by
  simpa only [iSup_range] using (d.selected_support_complement (Set.range f)).symm

noncomputable def selectedModuleSum :
    (fixedSpace ρ (⨆ i, d.factor (f i)) ×
      ((i : Fin n) → subspaceCommutator ρ ⊤ (d.factor (f i)))) ≃ₗ[ZMod 2] V :=
  ((LinearEquiv.refl (ZMod 2) _).prodCongr (d.selectedSupportSum f hf)).trans
    (Submodule.prodEquivOfIsCompl _ _ (d.selected_isCompl f))

@[simp] theorem selectedModuleSum_fixed (v : fixedSpace ρ (⨆ i, d.factor (f i))) :
    d.selectedModuleSum f hf (v,0) = v := by
  simp [selectedModuleSum]

@[simp] theorem selectedModuleSum_single (i : Fin n)
    (v : subspaceCommutator ρ ⊤ (d.factor (f i))) :
    d.selectedModuleSum f hf (0,Pi.single i v) = v := by
  simp [selectedModuleSum]
end CFSG.Quasithin.ChapterB.SolvableFFFactors
