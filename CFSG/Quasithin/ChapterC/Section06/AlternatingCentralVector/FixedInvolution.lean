module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.OvergroupNormalizer

/-!
# The fixed-center involution in the nonstationary Thompson branch

The normalizer of each maximum elementary subgroup of M lies in M:
conjugate it to the original Q and apply C.6.4(II). The centralizer
in M of a noncentral involution is maximum elementary. Thus an actor
outside M can fix only central involutions of M.

If J(NΛ(M))≠M, choose a maximum elementary subgroup A crossing M.
The index-two count forces A∩M=Z(M), so every involution in A−M
centralizes Z(M). This constructs the actual actor needed to enlarge
the dihedral factor; the enlargement itself is not assumed here.

Source: Aschbacher–Smith C.6.4, printed p.169, the final paragraph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- C.6.4(II) controls the Λ-normalizer of every maximum elementary
subgroup of a proper dihedral overgroup. -/
theorem Input.dihedral_maximum_normalizer_le (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M) (hproper : M < Λ)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups M) :
    Λ ⊓ normalizer (A : Set G) ≤ M := by
  obtain ⟨n,hn,rfl⟩ := d.dihedral_overgroup_maximum_conjugate M hM hproper A hA
  have hΛ : Λ.map (MulAut.conj n).toMonoidHom = Λ :=
    mem_normalizer_iff_map_conj_eq.mp (Λ.le_normalizer hn.1)
  have hMM : M.map (MulAut.conj n).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp hn.2
  rw [← map_equiv_normalizer_eq]
  conv_lhs => lhs; rw [← hΛ]
  rw [← map_inf _ _ _ (MulAut.conj n).injective,d.core_normalizer]
  exact (map_mono hM.1).trans_eq hMM

/-- An actor outside M fixes no noncentral involution of M. -/
theorem Input.dihedral_fixed_involution_mem_center (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M) (hproper : M < Λ)
    (y : G) (hy : y ∈ Λ ⊓ normalizer (M : Set G)) (hyM : y ∉ M)
    (a : G) (ha : a ∈ M) (ha2 : a ^ 2 = 1) (hay : a*y=y*a) : a ∈ centerIn M := by
  by_contra hnc
  have hfamily : M ⊓ centralizer ({a} : Set G) ∈ elementaryAbelianMaxSubgroups M := by
    obtain ⟨_,_,E,hE,n,hn,⟨e⟩⟩ := hM
    let := hE
    exact ElementaryDihedral.involution_centralizer_max_ambient M hn e a ha ha2 hnc
  apply hyM
  apply d.dihedral_maximum_normalizer_le M hM hproper _ hfamily
  refine ⟨hy.1,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj y).injective])
  have hfix : MulAut.conj y a = a := by
    change y*a*y⁻¹=a
    rw [← hay,mul_inv_cancel_right]
  rintro b ⟨c,hc,rfl⟩
  refine ⟨(mem_normalizer_iff.mp hy.2 c).mp hc.1,mem_centralizer_singleton_iff.mpr ?_⟩
  have hh := congrArg (MulAut.conj y) (mem_centralizer_singleton_iff.mp hc.2)
  change (MulAut.conj y c) * a = a * (MulAut.conj y c)
  simpa only [map_mul,hfix] using hh

/-- In the nonstationary Thompson branch there is an actual external
involution centralizing all of the original center. -/
theorem Input.exists_dihedral_enlarging_involution (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M) (hproper : M < Λ)
    (hJ : elementaryAbelianMaxJ (Λ ⊓ normalizer (M : Set G)) ≠ M) :
    ∃ y ∈ Λ ⊓ normalizer (M : Set G), y ∉ M ∧ y ^ 2 = 1 ∧
      y ∈ centralizer (centerIn M : Set G) := by
  classical
  let N := Λ ⊓ normalizer (M : Set G)
  have hMN : M ≤ N := le_inf hM.2.1 M.le_normalizer
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups N, ¬ A ≤ M := by
    by_contra hn
    have hle : elementaryAbelianMaxJ N ≤ M := sSup_le (by simpa using hn)
    have he := elementaryAbelianMaxJ_eq_of_intermediate_finite N M hle hMN
    exact hJ (he.symm.trans (dihedral_overgroup_thompson M hM))
  obtain ⟨A,hA,hAM⟩ := hex
  let : IsElementaryAbelian 2 A := hA.2.1
  obtain ⟨y,hyA,hyM⟩ := SetLike.not_le_iff_exists.mp hAM
  have hyN : y ∈ N := hA.1 hyA
  have hAZ : A ⊓ M ≤ centerIn M := by
    rintro a ⟨haA,haM⟩
    exact d.dihedral_fixed_involution_mem_center M hM hproper y hyN hyM a haM
      (elemPow_eq_one_of_isElementaryAbelian a haA) (congrArg Subtype.val (mul_comm (⟨a,haA⟩ : A) ⟨y,hyA⟩))
  have hi : M.relIndex A ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := M) hA.1 (by
        change M.relIndex (Λ ⊓ normalizer (M : Set G)) ≠ 0
        rw [d.dihedral_overgroup_normalizer_index M hM hproper]
        omega)
    change M.relIndex A ≤ M.relIndex (Λ ⊓ normalizer (M : Set G)) at hh
    rwa [d.dihedral_overgroup_normalizer_index M hM hproper] at hh
  have hcount : Nat.card (A ⊓ M : Subgroup G) * M.relIndex A = Nat.card A := by
    simpa only [relIndex_bot_left,inf_relIndex_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ M) A bot_le inf_le_left
  have hQ := d.core_maximum_in_dihedral_overgroup M hM
  have hlarge := hA.2.2 _ (hQ.1.trans hMN) hQ.2.1
  rw [d.core_card_eq_twice_center,← d.dihedral_overgroup_center M hM] at hlarge
  have hZA : centerIn M ≤ A := by
    have heq : A ⊓ M = centerIn M := eq_of_le_of_card_ge hAZ (by nlinarith)
    rw [← heq]
    exact inf_le_left
  exact ⟨y,hyN,hyM,elemPow_eq_one_of_isElementaryAbelian y hyA,
    fun z hz => congrArg Subtype.val (mul_comm (⟨z,hZA hz⟩ : A) ⟨y,hyA⟩)⟩

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
