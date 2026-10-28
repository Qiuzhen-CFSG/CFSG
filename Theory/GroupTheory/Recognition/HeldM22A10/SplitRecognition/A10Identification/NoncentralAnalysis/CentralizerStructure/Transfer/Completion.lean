module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.Interface
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.IndexNormal

/-!
# Completing the properties of Held's index-four subgroup

Suppose the normal subgroup M of index four has Sylow intersection
R = <lt,zm>. Projection identifies this intersection with the dihedral
group of order eight. Since the whole Sylow subgroup centralizes p,
ambient conjugacy of p to an element of M can be realized inside M.
Every index-two subgroup of M contains p = [lt,zm], hence its two fused
generators lt and zm and therefore a full Sylow subgroup, a contradiction.
The odd core is trivial by the fused-four-group argument and normality.

These are the final properties in the transfer paragraph of Held,
Illinois J. Math. 13 (1969), 224--240, p.234,
DOI 10.1215/ijm/1256053756. Existence of M and the source fusion data are
separate obligations; no recognition theorem is used here.
-/

open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
open TransferModel (Model l z t m R)
namespace TransferFusion
variable {K : Type u} [Group K] [Finite K] {p : K} (F : TransferFusion K p)

private theorem sylow_sup_normal (M : Subgroup K) [M.Normal] (hM : M.index = 4) :
    M ⊔ (F.sylow : Subgroup K) = ⊤ := by
  have hd : (M ⊔ (F.sylow : Subgroup K)).index ∣ 4 :=
    hM ▸ index_dvd_of_le (show M ≤ M ⊔ (F.sylow : Subgroup K) from le_sup_left)
  have ho : ¬ 2 ∣ (M ⊔ (F.sylow : Subgroup K)).index := fun h =>
    F.sylow.not_dvd_index (h.trans (index_dvd_of_le le_sup_right))
  apply index_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes
    (show Nat.Coprime 4 (M ⊔ (F.sylow : Subgroup K)).index from
      (Nat.prime_two.coprime_iff_not_dvd.mpr ho).pow_left 2) hd dvd_rfl

include F in
private theorem isConj_in_normal (M : Subgroup K) [M.Normal] (hM : M.index = 4)
    (hpM : p ∈ M) (y : M) (hy : IsConj p (y : K)) :
    IsConj (⟨p, hpM⟩ : M) y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have hgin : g ∈ M ⊔ (F.sylow : Subgroup K) := by rw [F.sylow_sup_normal M hM]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_left.mp hgin
  have hbp : b * p * b⁻¹ = p := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact mem_centralizer_singleton_iff.mp (F.centralizer_eq.symm ▸ hb)
  refine isConj_iff.mpr ⟨⟨a, ha⟩, Subtype.ext ?_⟩
  change a * p * a⁻¹ = (y : K)
  calc
    a * p * a⁻¹ = a * (b * p * b⁻¹) * a⁻¹ := by rw [hbp]
    _ = (a * b) * p * (a * b)⁻¹ := by group
    _ = y := hg

omit [Finite K] in
private theorem core_le (M : Subgroup K)
    (hinter : M ⊓ (F.sylow : Subgroup K) = R.map F.into) : R.map F.into ≤ M :=
  hinter.symm.le.trans inf_le_left

omit [Finite K] in
public theorem p_mem (M : Subgroup K)
    (hinter : M ⊓ (F.sylow : Subgroup K) = R.map F.into) : p ∈ M := by
  rw [← F.into_p]
  exact F.core_le M hinter (mem_map_of_mem F.into TransferModel.p_mem_R)

public theorem no_index_two (M : Subgroup K) [M.Normal] (hM : M.index = 4)
    (hinter : M ⊓ (F.sylow : Subgroup K) = R.map F.into)
    (N : Subgroup M) [N.Normal] : N.index ≠ 2 := by
  intro hN
  have hRM := F.core_le M hinter
  let a : M := ⟨F.into (l * t), hRM (mem_map_of_mem F.into TransferModel.lt_mem_R)⟩
  let b : M := ⟨F.into (z * m), hRM (mem_map_of_mem F.into TransferModel.zm_mem_R)⟩
  let pM : M := ⟨p, F.p_mem M hinter⟩
  have hcomm : ⁅a, b⁆ = pM := by
    apply Subtype.ext
    change ⁅F.into (l * t), F.into (z * m)⁆ = p
    rw [← map_commutatorElement, TransferModel.commutator_lt_zm, F.into_p]
  have hpN : pM ∈ N := by
    rw [← hcomm]
    simp only [commutatorElement_def, N.mul_mem_iff_of_index_two hN, N.inv_mem_iff]
    tauto
  have hconj (y : M) (hy : IsConj p (y : K)) : y ∈ N := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (F.isConj_in_normal M hM pM.property y hy)
    exact hg ▸ (inferInstance : N.Normal).conj_mem pM hpN g
  have haN : a ∈ N := hconj a F.conj_lt
  have hbN : b ∈ N := hconj b F.conj_zm
  have hRN : R.map F.into ≤ N.map M.subtype := by
    apply map_le_iff_le_comap.mpr
    apply TransferModel.R_le
    · exact mem_map_of_mem M.subtype haN
    · exact mem_map_of_mem M.subtype hbN
  obtain ⟨S, hS⟩ := F.sylow.exists_subgroupOf_eq_of_normal M
  have hSN : (S : Subgroup M) ≤ N := by
    intro x hx
    have hxT : (x : K) ∈ F.sylow := by
      change x ∈ (F.sylow : Subgroup K).subgroupOf M
      rwa [← hS]
    have hxR : (x : K) ∈ R.map F.into := by
      rw [← hinter]
      exact ⟨x.property, hxT⟩
    obtain ⟨y, hy, he⟩ := hRN hxR
    exact (Subtype.ext he : y = x) ▸ hy
  exact S.not_dvd_index (by simpa only [hN] using index_dvd_of_le hSN)

include F in
public theorem oddCore_subgroup (M : Subgroup K) [M.Normal] : pPrimeCore 2 M = ⊥ := by
  apply (map_eq_bot_iff_of_injective (pPrimeCore 2 M) M.subtype_injective).mp
  exact eq_bot_mono (pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 M) F.oddCore

public theorem sylow_structure (M : Subgroup K) [M.Normal]
    (hinter : M ⊓ (F.sylow : Subgroup K) = R.map F.into) :
    ∃ S : Sylow 2 M, Nonempty (S ≃* DihedralGroup 4) ∧
      centralizer ({⟨p, F.p_mem M hinter⟩} : Set M) = (S : Subgroup M) := by
  obtain ⟨S, hS⟩ := F.sylow.exists_subgroupOf_eq_of_normal M
  have himage : (S : Subgroup M).map M.subtype = R.map F.into := by
    rw [hS, subgroupOf_map_subtype, inf_comm, hinter]
  let equiv := ((S : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective).trans
    ((MulEquiv.subgroupCongr himage).trans
      ((R.equivMapOfInjective F.into F.into_injective).symm.trans TransferModel.coreEquiv.symm))
  refine ⟨S, ⟨equiv⟩, ?_⟩
  rw [hS]
  ext x
  rw [← F.centralizer_eq]
  simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

end TransferFusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
