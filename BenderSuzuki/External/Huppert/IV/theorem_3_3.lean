/-
Authors: OpenAI
-/

module

public import Mathlib.GroupTheory.Transfer
public import BenderSuzuki.External.Huppert.IV.theorem_3_2

/-!
# Huppert IV.3.3

Book-order entry file for the Grun transfer-kernel step currently used by the
Thompson fixed-point-free development.


The declarations below record the source theorem itself. The source proof uses
IV.1.7, the transfer cycle formula; Mathlib already provides the transfer
homomorphism and the corresponding orbit-product formula in
`Mathlib.GroupTheory.Transfer`, and the focal transfer interface in
`Mathlib.GroupTheory.Focal`.
-/

namespace BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u

/-- The transfer map `Y = V_{G -> P}` from Huppert IV.3.3, with target
`P/P'`; Mathlib's `Abelianization P` is definitionally this quotient. -/
public noncomputable def huppertIV33TransferToSylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} (S : Sylow q Q) :
    Q →* Abelianization (S : Subgroup Q) :=
  MonoidHom.transfer (G := Q) (H := (S : Subgroup Q))
    (Abelianization.of (G := (S : Subgroup Q)))

/-- The subgroup `P ∩ G'`, regarded as a subgroup of the Sylow subgroup `P`. -/
public abbrev huppertIV33SylowDerivedSubgroup
    {Q : Type u} [Group Q] {q : ℕ} (S : Sylow q Q) :
    Subgroup (S : Subgroup Q) :=
  (commutator Q).comap (S : Subgroup Q).subtype

/-- Huppert IV.3.3, sentence 1.

Since `G/G'(q)` is a `q`-group, the image of a Sylow `q`-subgroup `P` in
that quotient is all of `G/G'(q)`, and hence
`G/G'(q) ≃ P/(P ∩ G'(q))`. -/
public theorem huppert_IV_3_3_quotient_equiv_sylow_mod_abelian_residual
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    letI : (hktAbelianPResidual q Q).Normal :=
      hktAbelianPResidual_normal (Q := Q) (q := q)
    Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
      ((S : Subgroup Q) ⧸ (hktAbelianPResidual q Q).subgroupOf (S : Subgroup Q))) := by
  classical
  let N : Subgroup Q := hktAbelianPResidual q Q
  haveI : N.Normal := hktAbelianPResidual_normal (Q := Q) (q := q)
  have hquot : IsPGroup q (Q ⧸ N) := by
    simpa [N] using hktAbelianPResidual_quotient_isPGroup (Q := Q) (q := q)
  have hmap_top : (S : Subgroup Q).map (QuotientGroup.mk' N) = ⊤ :=
    sylow_map_quotient_eq_top_of_quotient_isPGroup
      (G := Q) (p := q) S N hquot
  let eRange :
      ((S : Subgroup Q) ⧸ N.subgroupOf (S : Subgroup Q)) ≃*
        (S : Subgroup Q).map (QuotientGroup.mk' N) :=
    quotientSubgroupRangeEquiv (S : Subgroup Q) N
  let eTop :
      (S : Subgroup Q).map (QuotientGroup.mk' N) ≃* Q ⧸ N :=
    (MulEquiv.subgroupCongr hmap_top).trans
      (Subgroup.topEquiv : (⊤ : Subgroup (Q ⧸ N)) ≃* Q ⧸ N)
  exact ⟨(eRange.trans eTop).symm⟩

/-- Huppert IV.3.3, sentence 2.

The Sylow part of the abelian `q`-residual is the Sylow part of the ordinary
commutator subgroup: `P ∩ G'(q) = P ∩ G'`. -/
public theorem huppert_IV_3_3_sylow_inf_abelian_residual_eq_sylow_inf_commutator
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    (S : Subgroup Q) ⊓ hktAbelianPResidual q Q =
      (S : Subgroup Q) ⊓ commutator Q := by
  classical
  let H : Subgroup Q := S
  let V : Q →* H ⧸ H.focalSubgroupOf := H.transferFocal
  have htarget_p : IsPGroup q (H ⧸ H.focalSubgroupOf) := by
    simpa [H] using S.2.to_quotient ((S : Subgroup Q).focalSubgroupOf)
  have hquot_ker_p : IsPGroup q (Q ⧸ V.ker) := by
    let e : Q ⧸ V.ker ≃* V.range := QuotientGroup.quotientKerEquivRange V
    have hrange_p : IsPGroup q V.range := htarget_p.to_subgroup V.range
    exact hrange_p.of_equiv e.symm
  have hpResidual_le_ker : hktPResidual q Q ≤ V.ker :=
    hktPResidual_le (Q := Q) (q := q) V.ker inferInstance hquot_ker_p
  have hcomm_le_ker : commutator Q ≤ V.ker :=
    Abelianization.commutator_subset_ker (f := V)
  have habResidual_le_ker : hktAbelianPResidual q Q ≤ V.ker :=
    hktAbelianPResidual_le (Q := Q) (q := q) (N := V.ker)
      hcomm_le_ker hpResidual_le_ker
  apply le_antisymm
  · intro x hx
    have hxker : x ∈ V.ker ⊓ H := ⟨habResidual_le_ker hx.2, hx.1⟩
    have hxfocal : x ∈ H.focalSubgroup := by
      rw [← Subgroup.ker_transferFocal_inf_eq_focalSubgroup (P := S)]
      simpa [V, H] using hxker
    exact ⟨hx.1, H.focalSubgroup_le_commutator hxfocal⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact commutator_le_hktAbelianPResidual (Q := Q) (q := q) hx.2

/-- Huppert IV.3.3. -/
public theorem huppert_IV_3_3_sylow_abelian_residual
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    let K : Subgroup (S : Subgroup Q) :=
      huppertIV33SylowDerivedSubgroup (Q := Q) (q := q) S
    letI : (hktAbelianPResidual q Q).Normal :=
      hktAbelianPResidual_normal (Q := Q) (q := q)
    letI : K.Normal := inferInstance
    (S : Subgroup Q) ⊓ hktAbelianPResidual q Q =
        (S : Subgroup Q) ⊓ commutator Q ∧
      Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
        ((S : Subgroup Q) ⧸ K)) := by
  classical
  let N : Subgroup Q := hktAbelianPResidual q Q
  have hNnormal : N.Normal := by
    simpa [N] using hktAbelianPResidual_normal (Q := Q) (q := q)
  haveI : (N.subgroupOf (S : Subgroup Q)).Normal :=
    Subgroup.Normal.subgroupOf (H := N) (K := (S : Subgroup Q)) hNnormal
  let K : Subgroup (S : Subgroup Q) :=
    huppertIV33SylowDerivedSubgroup (Q := Q) (q := q) S
  have hSN : (S : Subgroup Q) ⊓ N = (S : Subgroup Q) ⊓ commutator Q := by
    simpa [N] using
      huppert_IV_3_3_sylow_inf_abelian_residual_eq_sylow_inf_commutator
        (Q := Q) (q := q) S
  have hsub : N.subgroupOf (S : Subgroup Q) = K := by
    ext x
    constructor
    · intro hxN
      have hxinf : (x : Q) ∈ (S : Subgroup Q) ⊓ N := ⟨x.2, hxN⟩
      have hxcomm : (x : Q) ∈ (S : Subgroup Q) ⊓ commutator Q := by
        simpa [hSN] using hxinf
      simpa [K, huppertIV33SylowDerivedSubgroup, Subgroup.mem_comap] using hxcomm.2
    · intro hxK
      have hxcomm : (x : Q) ∈ (S : Subgroup Q) ⊓ commutator Q := by
        refine ⟨x.2, ?_⟩
        simpa [K, huppertIV33SylowDerivedSubgroup, Subgroup.mem_comap] using hxK
      have hxN : (x : Q) ∈ (S : Subgroup Q) ⊓ N := by
        simpa [hSN] using hxcomm
      exact hxN.2
  have hKnormal : K.Normal := by
    rw [← hsub]
    infer_instance
  haveI : K.Normal := hKnormal
  constructor
  · simpa [N] using hSN
  · rcases huppert_IV_3_3_quotient_equiv_sylow_mod_abelian_residual
        (Q := Q) (q := q) S with ⟨e⟩
    exact ⟨by
      simpa [N, K] using e.trans (QuotientGroup.quotientMulEquivOfEq hsub)⟩

private theorem hkt_monoidHom_comp_transfer
    {G A B : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    [CommGroup A] [CommGroup B] (φ : H →* A) (ψ : A →* B) :
    ψ.comp (MonoidHom.transfer φ) = MonoidHom.transfer (ψ.comp φ) := by
  classical
  ext g
  change ψ (MonoidHom.transfer φ g) = MonoidHom.transfer (ψ.comp φ) g
  let T : H.LeftTransversal := default
  calc
    ψ (MonoidHom.transfer φ g) = ψ (Subgroup.leftTransversals.diff φ T (g • T)) := by
      rw [MonoidHom.transfer_def φ T g]
    _ = Subgroup.leftTransversals.diff (ψ.comp φ) T (g • T) := by
      dsimp [Subgroup.leftTransversals.diff]
      rw [map_prod]
    _ = MonoidHom.transfer (ψ.comp φ) g := by
      rw [MonoidHom.transfer_def (ψ.comp φ) T g]

private theorem huppert_IV_3_3_transfer_image_eq_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    let Y := huppertIV33TransferToSylow (Q := Q) (q := q) S
    MonoidHom.range Y = MonoidHom.range (Y.restrict (S : Subgroup Q)) := by
  classical
  let H : Subgroup Q := S
  let Y : Q →* Abelianization H := huppertIV33TransferToSylow (Q := Q) (q := q) S
  let N : Subgroup Q := hktAbelianPResidual q Q
  haveI : N.Normal := hktAbelianPResidual_normal (Q := Q) (q := q)
  have hquot_p : IsPGroup q (Q ⧸ N) := by
    simpa [N] using hktAbelianPResidual_quotient_isPGroup (Q := Q) (q := q)
  have hN_le_ker : N ≤ Y.ker := by
    have hcomm_le : commutator Q ≤ Y.ker :=
      Abelianization.commutator_subset_ker (f := Y)
    have hquot_ker_p : IsPGroup q (Q ⧸ Y.ker) := by
      let e : Q ⧸ Y.ker ≃* Y.range := QuotientGroup.quotientKerEquivRange Y
      have hrange_p : IsPGroup q Y.range := by
        have hH_p : IsPGroup q H := by
          simpa [H] using S.isPGroup'
        have hAb_p : IsPGroup q (Abelianization H) := by
          change IsPGroup q (H ⧸ commutator H)
          exact hH_p.to_quotient (commutator H)
        exact hAb_p.to_subgroup Y.range
      exact hrange_p.of_equiv e.symm
    exact hktAbelianPResidual_le (Q := Q) (q := q) (N := Y.ker)
      hcomm_le (hktPResidual_le (Q := Q) (q := q) Y.ker inferInstance hquot_ker_p)
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨g, rfl⟩
    rcases hkt_exists_sylow_div_mem_of_quotient_isPGroup
        (G := Q) (p := q) S N hquot_p g with ⟨s, hsS, hgsN⟩
    have hgs_ker : g * s⁻¹ ∈ Y.ker := hN_le_ker hgsN
    have hYgs : Y (g * s⁻¹) = 1 := MonoidHom.mem_ker.mp hgs_ker
    refine ⟨⟨s, hsS⟩, ?_⟩
    have hYeq : Y g = Y s := by
      have hcalc : Y (g * s⁻¹) = Y g * (Y s)⁻¹ := by simp
      rw [hcalc] at hYgs
      exact mul_inv_eq_one.mp hYgs
    simpa [Y, H, huppertIV33TransferToSylow, MonoidHom.restrict_apply] using hYeq.symm
  · intro y hy
    rcases hy with ⟨s, rfl⟩
    exact ⟨(s : Q), by rfl⟩

private theorem huppert_IV_3_3_transfer_kernel_inf_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    let Y := huppertIV33TransferToSylow (Q := Q) (q := q) S
    Y.ker ⊓ (S : Subgroup Q) = (S : Subgroup Q) ⊓ commutator Q := by
  classical
  let H : Subgroup Q := S
  let Y : Q →* Abelianization H := huppertIV33TransferToSylow (Q := Q) (q := q) S
  let πF : H →* H ⧸ H.focalSubgroupOf := QuotientGroup.mk' H.focalSubgroupOf
  have hkerF : (MonoidHom.transfer πF).ker ⊓ H = H.focalSubgroup := by
    simpa [H] using Subgroup.ker_transferFocal_inf_eq_focalSubgroup (P := S)
  let ρ : Abelianization H →* H ⧸ H.focalSubgroupOf :=
    Abelianization.lift πF
  have hcomp : ρ.comp Y = MonoidHom.transfer πF := by
    simpa [Y, huppertIV33TransferToSylow, H, ρ, πF] using
      (hkt_monoidHom_comp_transfer
        (G := Q) (H := H) (A := Abelianization H) (B := H ⧸ H.focalSubgroupOf)
        (Abelianization.of (G := H)) ρ)
  apply le_antisymm
  · intro x hx
    have hxY : x ∈ Y.ker := by
      simpa [Y] using hx.1
    have hxFker : x ∈ (MonoidHom.transfer πF).ker ⊓ H := by
      refine ⟨?_, hx.2⟩
      rw [← hcomp]
      exact MonoidHom.mem_ker.mpr (by
        change ρ (Y x) = 1
        rw [MonoidHom.mem_ker.mp hxY]
        simp)
    have hxfocal : x ∈ H.focalSubgroup := by
      simpa [hkerF] using hxFker
    exact ⟨hx.2, H.focalSubgroup_le_commutator hxfocal⟩
  · intro x hx
    refine ⟨?_, hx.1⟩
    exact Abelianization.commutator_subset_ker (f := Y) hx.2

/-- Huppert IV.3.3, transfer side. -/
public theorem huppert_IV_3_3_transfer
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    (let Y := huppertIV33TransferToSylow (Q := Q) (q := q) S
     MonoidHom.range Y = MonoidHom.range (Y.restrict (S : Subgroup Q))) ∧
      (let Y := huppertIV33TransferToSylow (Q := Q) (q := q) S
       Y.ker ⊓ (S : Subgroup Q) = (S : Subgroup Q) ⊓ commutator Q) := by
  exact ⟨huppert_IV_3_3_transfer_image_eq_sylow (Q := Q) (q := q) S,
    huppert_IV_3_3_transfer_kernel_inf_sylow (Q := Q) (q := q) S⟩

/-- Huppert IV.3.3, complete source statement. -/
public theorem huppert_IV_3_3
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    ((let Y := huppertIV33TransferToSylow (Q := Q) (q := q) S
      MonoidHom.range Y = MonoidHom.range (Y.restrict (S : Subgroup Q))) ∧
        (let Y := huppertIV33TransferToSylow (Q := Q) (q := q) S
         Y.ker ⊓ (S : Subgroup Q) = (S : Subgroup Q) ⊓ commutator Q)) ∧
      (let K : Subgroup (S : Subgroup Q) :=
        huppertIV33SylowDerivedSubgroup (Q := Q) (q := q) S
       letI : (hktAbelianPResidual q Q).Normal :=
        hktAbelianPResidual_normal (Q := Q) (q := q)
       letI : K.Normal := inferInstance
       (S : Subgroup Q) ⊓ hktAbelianPResidual q Q =
          (S : Subgroup Q) ⊓ commutator Q ∧
        Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
          ((S : Subgroup Q) ⧸ K))) := by
  exact ⟨huppert_IV_3_3_transfer (Q := Q) (q := q) S,
    huppert_IV_3_3_sylow_abelian_residual (Q := Q) (q := q) S⟩

end External
end BenderSuzuki
