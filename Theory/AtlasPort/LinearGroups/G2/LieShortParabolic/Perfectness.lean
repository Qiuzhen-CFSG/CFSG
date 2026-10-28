module
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Core
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.GroupTheory.SolvableResidual

/-!
# Perfectness of the short G₂ local group

The short rank-one torus lies in the local group. For a field with more than
two elements, its commutators give roots C and F, whose torus characters are
respectively a and a². Short Weyl conjugation gives D, while root commutators
give B and A, and reflection gives E. The short rank-one word then gives the
Weyl generator itself in the local derived subgroup. This argument includes
q = 4 without requiring a nontrivial cubic torus character.

The final statements identify both the intrinsic solvable residual and its
image in the ambient group. Every conjugation used is inside the local group.

Source: Aschbacher--Smith, F.1.12(II), printed pp. 263--264.
The torus-commutator method adapts the licensed ATLAS G₂ perfectness argument;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. The short-local
restriction and root commutator argument are added here.
-/

@[expose] public section
open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit
open scoped commutatorElement
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem short_root_mem_derived (X : F → Model F)
    (hadd : ∀ a b, X a * X b = X (a + b)) (hzero : X 0 = 1)
    (hmem : ∀ a, X a ∈ local₁) (g : Model F) (hg : g ∈ local₁)
    (c : F) (hc : c ≠ 1) (hconj : ∀ a, g * X a * g⁻¹ = X (c*a))
    (a : F) : X a ∈ ⁅local₁ (F := F), local₁ (F := F)⁆ := by
  have hinv (b : F) : X (-b) = (X b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hadd, neg_add_cancel, hzero]
  have he : ⁅g, X (a / (c-1))⁆ = X a := by
    rw [commutatorElement_def, hconj, ← hinv, hadd]
    congr 1
    field_simp
    ring
  rw [← he]
  exact Subgroup.commutator_mem_commutator hg (hmem _)

private theorem short_FC_commutator (a : F) : ⁅rootF (1 : F),rootC a⁆ = rootB a := by
  have hf : rootF (1 : F) = unipotentProduct ![0,0,0,0,0,1] := by simp [unipotentProduct]
  have hc : rootC a = unipotentProduct ![0,0,a,0,0,0] := by simp [unipotentProduct]
  have hb : rootB a = unipotentProduct ![0,a,0,0,0,0] := by simp [unipotentProduct]
  rw [hf,hc,hb,commutatorElement_def,unipotentProduct_inv,unipotentProduct_inv,
    unipotentProduct_mul,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,
    CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod,CharTwo.add_self_eq_zero]

/-- The short local group is perfect for every finite field of even order greater than two. -/
theorem local₁_isPerfect [Finite F] (hq : 2 < Nat.card F) :
    Group.IsPerfect (local₁ (F := F)) := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  let m : Fˣ := Units.mk0 t ht'.1
  let H : Subgroup (Model F) := ⁅local₁ (F := F), local₁ (F := F)⁆
  have hS : (weylS : Model F) ∈ local₁ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hconj {x : Model F} (hx : x ∈ H) : weylS * x * weylS⁻¹ ∈ H := by
    have hn := Subgroup.normalizer_commutator_ge_left
      (local₁ (F := F)) (local₁ (F := F)) hS
    exact (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have hC (a : F) : rootC a ∈ H := by
    apply short_root_mem_derived rootC rootC_add rootC_zero
      (fun a => unipotent_le_local₁ (Subgroup.subset_closure (by simp)))
      (torus m m⁻¹) (short_torus_mem_local₁ m) t ht'.2
    intro b
    simpa [m] using torus_rootC m m⁻¹ b
  have hD (a : F) : rootD a ∈ H := by
    have he : weylS * rootC a * weylS⁻¹ = rootD a := by
      simpa [unipotentProduct] using weylS_fiveRoot_conjugate (F := F) ![0,0,a,0,0,0] rfl
    rw [← he]
    exact hconj (hC a)
  have ht2 : t^2 ≠ 1 := by
    intro he
    rcases sq_eq_one_iff.mp he with he | he
    · exact ht'.2 he
    · exact ht'.2 (by simpa only [CharTwo.neg_eq] using he)
  have hF (a : F) : rootF a ∈ H := by
    apply short_root_mem_derived rootF rootF_add rootF_zero
      (fun a => unipotent_le_local₁ (Subgroup.subset_closure (by simp)))
      (torus m m⁻¹) (short_torus_mem_local₁ m) (t^2) ht2
    intro b
    simpa [m,div_eq_mul_inv,pow_two] using torus_rootF m m⁻¹ b
  have hB (a : F) : rootB a ∈ H := by
    rw [← short_FC_commutator]
    exact Subgroup.commutator_mem_commutator
      (unipotent_le_local₁ (Subgroup.subset_closure (by simp)))
      (unipotent_le_local₁ (Subgroup.subset_closure (by simp)))
  have hE (a : F) : rootE a ∈ H := by
    rw [← weylS_rootB]
    exact hconj (hB a)
  have hA (a : F) : rootA a ∈ H := by
    have he : ⁅rootB a,rootE 1⁆ = rootA a := by
      simpa [unipotentProduct] using
        fiveRoot_commutator (F := F) ![0,a,0,0,0,0] ![0,0,0,0,1,0] rfl rfl
    rw [← he]
    exact Subgroup.commutator_mem_commutator
      (unipotent_le_local₁ (Subgroup.subset_closure (by simp)))
      (unipotent_le_local₁ (Subgroup.subset_closure (by simp)))
  have hU : unipotent (K := F) ≤ H := by
    apply (Subgroup.closure_le H).mpr
    intro g hg
    rcases hg with (((((hg|hg)|hg)|hg)|hg)|hg)
    all_goals obtain ⟨a,rfl⟩ := hg
    · exact hA a
    · exact hB a
    · exact hC a
    · exact hD a
    · exact hE a
    · exact hF a
  have hSH : (weylS : Model F) ∈ H := by
    have hh := H.mul_mem (H.mul_mem (hF 1) (hconj (hF (-1)))) (hF 1)
    have hw := short_rank_one_word (F := F) (1 : Fˣ)
    have hneg : (-1 : Fˣ) = 1 := by
      apply Units.ext
      simp [CharTwo.neg_eq]
    simp only [Units.val_one, inv_one, hneg, torus_identity, one_mul] at hw
    rwa [hw] at hh
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  exact sup_le hU ((Subgroup.closure_le H).mpr (by simpa using hSH))

theorem local₁_solvableResidual_eq_top [Finite F] (hq : 2 < Nat.card F) :
    Subgroup.solvableResidual (local₁ (F := F)) = ⊤ := by
  let := local₁_isPerfect (F := F) hq
  exact Subgroup.solvableResidual_eq_top

theorem local₁_map_solvableResidual [Finite F] (hq : 2 < Nat.card F) :
    (Subgroup.solvableResidual (local₁ (F := F))).map (local₁ (F := F)).subtype =
      local₁ (F := F) := by
  rw [local₁_solvableResidual_eq_top hq, ← MonoidHom.range_eq_map,Subgroup.range_subtype]

end Atlas.G2.LieParabolicSetup
