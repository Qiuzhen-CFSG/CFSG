module

public import Theory.Representation.BinaryPermutation.TransvectionCoreMap.Centers
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.SubspaceAction
import Mathlib.Tactic

/-!
# The augmentation map from a transposition transvection

Let a faithful binary representation of S₈ have a transposition with fixed
codimension one. The transposition centers satisfy the triangle relation, so
sending a weight-two vector to its center extends to a linear map from the
augmentation core. The sum formula is independent of the chosen origin and
intertwines the full symmetric-group action.

Its range is exactly [E,A₈]: every center is a three-cycle displacement, and
induction on transpositions puts every symmetric-group displacement in the
range. The final theorem transports both the map and the literal commutator
along the specified isomorphism H ≃ S₈. No module-identification hypothesis or
indecomposable classification is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the module
recognition in 13.8.25, printed p.960 (PDF p.977), and the permutation core
of B.3.1, printed p.83. The kernel classification and conversion to natural
or seven-dimensional cover modules are handled by the existing consumers.
-/

public section

namespace BinaryPermutation.TransvectionCoreMap
open Equiv Representation.BinaryOffender
variable {E Ω : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Fintype Ω] [DecidableEq Ω]
variable (ρ : Representation (ZMod 2) (Perm Ω) E)
variable (hr : ∀ i j : Ω, i ≠ j →
  Module.finrank (ZMod 2) (LinearMap.range (ρ (swap i j) - LinearMap.id)) = 1)

/-- A weight-two vector of the augmentation core, allowing the zero diagonal. -/
def pair (i j : Ω) : core Ω :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

/-- Extend the transposition centers linearly, using one letter as origin. -/
noncomputable def coreMap (o : Ω) : core Ω →ₗ[ZMod 2] E where
  toFun v := ∑ i, v.val i • center ρ hr i o
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r v := by simp [mul_smul, Finset.smul_sum]

/-- The chosen origin disappears on the augmentation kernel. -/
theorem coreMap_origin (hρ : Function.Injective ρ) (o p : Ω) (v : core Ω) :
    coreMap ρ hr o v = coreMap ρ hr p v := by
  have ht (i : Ω) : center ρ hr i o = center ρ hr i p + center ρ hr p o :=
    (center_triangle ρ hr hρ i p o).symm
  change (∑ i, v.val i • center ρ hr i o) = ∑ i, v.val i • center ρ hr i p
  calc
    _ = ∑ i, v.val i • (center ρ hr i p + center ρ hr p o) :=
      Finset.sum_congr rfl (fun i _ => congrArg (fun x : E => v.val i • x) (ht i))
    _ = _ := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
      rw [show ∑ i, v.val i = 0 from v.property, zero_smul, add_zero]

/-- The core map takes a weight-two vector to its transposition center. -/
theorem coreMap_pair (hρ : Function.Injective ρ) (o i j : Ω) :
    coreMap ρ hr o (pair i j) = center ρ hr i j := by
  rw [coreMap_origin ρ hr hρ o j]
  simp [coreMap, pair, add_smul, Finset.sum_add_distrib]

/-- The core map intertwines the full symmetric-group action. -/
theorem coreMap_equivariant (hρ : Function.Injective ρ) (o : Ω)
    (g : Perm Ω) (v : core Ω) :
    coreMap ρ hr o (coreRepresentation Ω g v) = ρ g (coreMap ρ hr o v) := by
  rw [coreMap_origin ρ hr hρ o (g o)]
  change (∑ i, v.val (g.symm i) • center ρ hr i (g o)) =
    ρ g (∑ i, v.val i • center ρ hr i o)
  rw [map_sum]
  simp only [map_smul, center_equivariant]
  exact (Equiv.sum_comp g (fun i => v.val (g.symm i) • center ρ hr i (g o))).symm.trans
    (by simp only [g.symm_apply_apply])

private theorem center_mem_range (hρ : Function.Injective ρ) (o i j : Ω) :
    center ρ hr i j ∈ (coreMap ρ hr o).range :=
  ⟨pair i j, coreMap_pair ρ hr hρ o i j⟩

private theorem displacement_mem_range (hρ : Function.Injective ρ) (o : Ω)
    (g : Perm Ω) (v : E) : ρ g v - v ∈ (coreMap ρ hr o).range := by
  induction g using Perm.swap_induction_on with
  | one => simp
  | swap_mul g i j _ ih =>
    have ht : ρ (swap i j) (ρ g v) - ρ g v ∈ (coreMap ρ hr o).range := by
      rcases displacement_cases ρ hr i j (ρ g v) with h | h
      · rw [h]; exact Submodule.zero_mem _
      · rw [h]; exact center_mem_range ρ hr hρ o i j
    convert (coreMap ρ hr o).range.add_mem ht ih using 1
    simp only [map_mul, Module.End.mul_apply]
    abel

private theorem center_mem_alternatingCommutator (hρ : Function.Injective ρ)
    (hn : 3 ≤ Fintype.card Ω) (i j : Ω) :
    center ρ hr i j ∈ subspaceCommutator ρ ⊤ (alternatingGroup Ω) := by
  by_cases hij : i = j
  · subst j; rw [center_self]; exact Submodule.zero_mem _
  have hc : ({i,j} : Finset Ω).card < (Finset.univ : Finset Ω).card := by
    have := Finset.card_le_two (a := i) (b := j)
    simpa only [Finset.card_univ] using (lt_of_le_of_lt this (by omega))
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  let g : Perm Ω := swap i k * swap k j
  have hg : g ∈ alternatingGroup Ω := by
    simp [g, Perm.mem_alternatingGroup, Perm.sign_swap (Ne.symm hk.1),
      Perm.sign_swap hk.2]
  have hi : g i = k := by
    simp only [g, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hk.1) hij,
      swap_apply_left]
  have hj : g k = j := by
    simp only [g, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm hk.2)]
  have he : ρ g (center ρ hr i k) - center ρ hr i k = center ρ hr i j := by
    rw [center_equivariant, hi, hj]
    have hz : -(center ρ hr i k) = center ρ hr i k :=
      neg_eq_of_add_eq_zero_left (ZModModule.add_self _)
    rw [sub_eq_add_neg, hz, add_comm, center_triangle ρ hr hρ]
  exact he ▸ Submodule.subset_span ⟨g, hg, center ρ hr i k, Submodule.mem_top, rfl⟩

/-- The range is the actual alternating commutator, including on nonsplit modules. -/
theorem coreMap_range (hρ : Function.Injective ρ) (hn : 3 ≤ Fintype.card Ω) (o : Ω) :
    (coreMap ρ hr o).range = subspaceCommutator ρ ⊤ (alternatingGroup Ω) := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (center_mem_alternatingCommutator ρ hr hρ hn i o))
  · apply Submodule.span_le.mpr
    rintro v ⟨g, _, u, _, rfl⟩
    exact displacement_mem_range ρ hr hρ o g u

end BinaryPermutation.TransvectionCoreMap

namespace BinaryPermutation.TransvectionCoreMap
open Equiv Representation.BinaryOffender
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]

private theorem alternatingCommutator_transport
    (ρ : Representation (ZMod 2) H E) (eH : H ≃* Perm (Fin 8))
    (K : Subgroup H) (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) :
    subspaceCommutator (ρ.comp eH.symm.toMonoidHom) ⊤ (alternatingGroup (Fin 8)) =
      subspaceCommutator ρ ⊤ K := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨g, hg, w, hw, rfl⟩
    rw [← hK] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    exact ⟨k, hk, w, hw, by simp⟩
  · rintro ⟨k, hk, w, hw, rfl⟩
    refine ⟨eH k, ?_, w, hw, by simp⟩
    rw [← hK]
    exact ⟨k, hk, rfl⟩

/-- A transposition acting as a transvection constructs an equivariant map from
the eight-letter augmentation core with image exactly the alternating commutator. -/
theorem exists_core_map_of_transposition [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (hρ : Function.Injective ρ)
    (eH : H ≃* Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (a : H) (ha : (eH a).IsSwap)
    (ha_rank : fixedCodim ρ (Subgroup.zpowers a) = 1) :
    ∃ f : core (Fin 8) →ₗ[ZMod 2] E,
      (∀ g v, f (coreRepresentation (Fin 8) (eH g) v) = ρ g (f v)) ∧
      LinearMap.range f = subspaceCommutator ρ ⊤ K := by
  let σ : Representation (ZMod 2) (Perm (Fin 8)) E := ρ.comp eH.symm.toMonoidHom
  have hσ : Function.Injective σ := hρ.comp eH.symm.injective
  have ha' : Module.finrank (ZMod 2) (LinearMap.range (σ (eH a) - LinearMap.id)) = 1 := by
    have hs : σ (eH a) = ρ a := by simp [σ]
    rw [hs]
    exact (rank_displacement_eq_fixedCodim ρ a).trans ha_rank
  let hr := swap_rank_one σ ha ha'
  refine ⟨coreMap σ hr 0, ?_, ?_⟩
  · intro g v
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      eH.symm_apply_apply] using coreMap_equivariant σ hr hσ 0 (eH g) v
  · rw [coreMap_range σ hr hσ (by decide : 3 ≤ Fintype.card (Fin 8))]
    exact alternatingCommutator_transport ρ eH K hK

end BinaryPermutation.TransvectionCoreMap
