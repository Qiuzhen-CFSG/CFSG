module
public import Theory.SpecificGroups.Suzuki.NormalizedRootCentralizers
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.Suzuki.BorelElementary
public import Theory.SpecificGroups.Suzuki.SupplementInvariantSubgroups
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Suzuki

/-!
# Odd automorphisms fixing a Suzuki Sylow center

The inner-field description of Suzuki automorphisms shows that fixing the
root center forces the inner element into the root group and kills the
field automorphism. An odd such automorphism is therefore identity.
Sylow conjugacy keeps an arbitrary supplied model marking and Sylow.

A nontrivial subgroup of a Suzuki Sylow invariant under a normalizer
supplement contains its whole center: use the central-or-full dichotomy
and transitivity on nonidentity central elements. These two facts control
the actual quotient action of odd actors centralizing a complement-invariant
incoming core in DGS85.CommutingThreeProfile.SuzukiCentralizerPropagation.

Source: Huppert--Blackburn III, XI.3.1--3.3; the Suzuki inner-field
calculation of GLS3, Theorem 2.5.12. The consumer is DGS, Groups and Graphs
(1985), proof of (12.9), printed p.189.
-/

public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups
open SchurCover.Family PFAppendixIII
private theorem field_root_center (m : ℕ)
    (σ : Field m ≃ₐ[ZMod 2] Field m) (b : Field m) :
    suzukiFieldAut m σ (rootPoint m 0 b : SuzukiMatrixGroup m) =
      (rootPoint m 0 (σ b) : SuzukiMatrixGroup m) := by
  ext i j
  rw [suzukiFieldAut_apply_entry]
  fin_cases i <;> fin_cases j <;> simp [rootPoint, SuzukiRootGL, SuzukiRootMatrix]

private theorem root_center_point (m : ℕ) (hm : 0 < m) (b : Field m) :
    (rootPoint m 0 b : SuzukiMatrixGroup m) ∈
      (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype :=
  (NormalizedRootCentralizers.mem_center_iff_coordinates m hm _).mpr ⟨b,rfl⟩

/-- Fixing the root center pointwise makes a Suzuki automorphism inner by a root element. -/
theorem suzuki_aut_fixing_root_center_inner (m : ℕ) (hm : 0 < m)
    (α : MulAut (SuzukiMatrixGroup m))
    (hfix : ∀ z ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype,
      α z = z) :
    ∃ g ∈ SuzukiRootSubgroup m, α = MulAut.conj g := by
  obtain ⟨g,σ,hα⟩ := suzukiAut_eq_inner_mul_field m hm α
  have hc (b : Field m) :
      g * (rootPoint m 0 (σ b) : SuzukiMatrixGroup m) * g⁻¹ = rootPoint m 0 b := by
    have he := hfix _ (root_center_point m hm b)
    rw [hα,MulAut.mul_apply,field_root_center] at he
    exact he
  have hg : g ∈ SuzukiRootSubgroup m := by
    have hz : (rootPoint m 0 1 : SuzukiMatrixGroup m) ≠ 1 := by
      intro he
      have h02 := congrArg (fun x : SuzukiMatrixGroup m => x.val (0 : Fin 4) (2 : Fin 4)) he
      change (1 : Field m) = 0 at h02
      exact one_ne_zero h02
    apply suzukiRootSubgroup_centralizer_le m hm (rootPoint m 0 1).property hz
    rw [mem_centralizer_singleton_iff]
    have he := hc 1
    rw [map_one] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hσ (b : Field m) : σ b = b := by
    obtain ⟨a,c,hgac⟩ := rootPoint_surjective m ⟨g,hg⟩
    have hgac' : g = (rootPoint m a c : SuzukiMatrixGroup m) := congrArg Subtype.val hgac
    have he := mul_inv_eq_iff_eq_mul.mp (hc b)
    rw [hgac'] at he
    change ((rootPoint m a c * rootPoint m 0 (σ b) : SuzukiRootSubgroup m) : SuzukiMatrixGroup m) =
      ((rootPoint m 0 b * rootPoint m a c : SuzukiRootSubgroup m) : SuzukiMatrixGroup m) at he
    rw [rootPoint_mul m hm,rootPoint_mul m hm] at he
    have h02 := congrArg (fun x : SuzukiMatrixGroup m => x.val (0 : Fin 4) (2 : Fin 4)) he
    change c + σ b + a * suzukiTits m 0 = b + c + 0 * suzukiTits m a at h02
    simp only [map_zero,mul_zero,zero_mul,add_zero] at h02
    exact add_left_cancel (h02.trans (add_comm b c))
  have hf : suzukiFieldAut m σ = 1 := by
    ext x i j
    rw [suzukiFieldAut_apply_entry]
    exact hσ (x.val i j)
  exact ⟨g,hg,by simpa only [hf,mul_one] using hα⟩

/-- An odd automorphism fixing the center of a prescribed Suzuki Sylow is identity. -/
theorem suzuki_odd_aut_eq_one_of_fixing_sylow_center
    {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 0 < m)
    (e : X ≃* SuzukiMatrixGroup m) (P : Sylow 2 X)
    (α : MulAut X) (ho : Odd (orderOf α))
    (hfix : ∀ z ∈ (center P).map (P : Subgroup X).subtype, α z = z) : α = 1 := by
  obtain ⟨f,hP,_⟩ := suzukiSylow_aligned_equiv hm e P
  let β := MulAut.congr f.symm α
  have hβfix : ∀ z ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype,
      β z = z := by
    intro z hz
    have hzP : f z ∈ (center P).map (P : Subgroup X).subtype := by
      rw [←hP,←map_embeddedCenter _ _ f.injective]
      exact mem_map_of_mem f.toMonoidHom hz
    change f.symm (α (f z)) = z
    rw [hfix _ hzP,f.symm_apply_apply]
  obtain ⟨g,hg,hβ⟩ := suzuki_aut_fixing_root_center_inner m hm β hβfix
  have hoβ : Odd (orderOf β) := by
    simpa only [β,MulEquiv.orderOf_eq] using ho
  have hp : IsPGroup 2 ((SuzukiRootSubgroup m).map (MulAut.conj : SuzukiMatrixGroup m →* _)) :=
    (suzukiRootSubgroup_isPGroup m hm).map _
  have hmem : β ∈ (SuzukiRootSubgroup m).map (MulAut.conj : SuzukiMatrixGroup m →* _) :=
    ⟨g,hg,hβ.symm⟩
  obtain ⟨j,hj⟩ := hp.exists_orderOf_dvd_pow ⟨β,hmem⟩
  rw [Subgroup.orderOf_mk] at hj
  have he : β = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hoβ.coprime_two_right.pow_right j) dvd_rfl hj)
  exact (MulAut.congr f.symm).injective (he.trans (map_one _).symm)

/-- Every nontrivial subgroup invariant under a Suzuki Borel supplement contains the full root center. -/
theorem suzuki_center_le_of_supplement_invariant
    {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 0 < m)
    (e : X ≃* SuzukiMatrixGroup m) (P : Sylow 2 X) (J K : Subgroup X)
    (hJP : J ≤ P) (hne : J ≠ ⊥)
    (hK : (P : Subgroup X) ⊔ K = normalizer (P : Set X))
    (hn : K ≤ normalizer (J : Set X)) :
    (center P).map (P : Subgroup X).subtype ≤ J := by
  rcases suzuki_supplement_invariant_dichotomy hm e P J K hJP hK hn with hz | he
  · have hZelem : IsElementaryAbelian 2 ((center P).map (P : Subgroup X).subtype) := by
      rw [←suzukiSylow_omega_eq_center hm e P]
      exact suzukiSylow_omega_elementary hm e P
    let := hZelem
    let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_injective (inclusion hz) (inclusion_injective _)
    have hPJ : (P : Subgroup X) ≤ normalizer (J : Set X) := by
      apply le_trans _ (centralizer_le_normalizer J)
      apply le_centralizer_iff.mpr
      rintro z hzJ x hx
      obtain ⟨z,hz,rfl⟩ := hz hzJ
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)
    have hN : normalizer (P : Set X) ≤ normalizer (J : Set X) := by
      rw [←hK]; exact sup_le hPJ hn
    exact (suzuki_elementary_eq_center_of_borel_normalized hm e P J hJP hne hN).ge
  · rw [he]; exact map_subtype_le _
end BenderSuzuki.MatrixGroups
