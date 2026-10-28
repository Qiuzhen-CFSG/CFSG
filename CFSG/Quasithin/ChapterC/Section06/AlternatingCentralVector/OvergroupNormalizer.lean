module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.OvergroupGeometry
public import Theory.GroupTheory.PGroup.ElementaryDihedralPlanes
public import Theory.GroupTheory.MaximumElementaryNormalizerBound

/-!
# The index-two normalizer and its orbit of elementary subgroups

For M an elementary-by-dihedral overgroup of the marked R, the original
Q is maximum elementary and has Λ-normalizer R. The reflection-plane
count bounds |NΛ(M):R|. Since |R:Q|=2, this gives |NΛ(M):M|≤2;
the normalizer condition gives equality for M<Λ. Equality in the count
also makes every maximum elementary subgroup an NΛ(M)-conjugate of Q.

Source: Aschbacher–Smith C.6.4, printed pp.168–169. The proof counts
the actual elementary family and requires no extra section-action premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

private theorem Input.dihedral_overgroup_indices (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M) (hproper : M < Λ) :
    M.relIndex (Λ ⊓ normalizer (M : Set G)) = 2 ∧
    Nat.card {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups M} ≤
      R.relIndex (Λ ⊓ normalizer (M : Set G)) := by
  let N := Λ ⊓ normalizer (M : Set G)
  let Q := (K ⊔ S).pCoreIn 2
  have hQM := d.core_maximum_in_dihedral_overgroup M hM
  have hcenter := d.dihedral_overgroup_center M hM
  obtain ⟨hRM,hMΛ,E,hE,n,hn,⟨e⟩⟩ := hM
  let := hE
  have hMN : M ≤ N := le_inf hMΛ M.le_normalizer
  have hRN := hRM.trans hMN
  have hQR : Q.relIndex R = 2 := by
    let := d.core_normal_in_R
    let := d.quotient_elementary_rank_one.1
    rw [c6_3_order_of_elementary_quotient,d.quotient_elementary_rank_one.2]
    rfl
  have hRc : Nat.card R = 2 * Nat.card Q := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) Q R bot_le d.core_le
    simpa only [relIndex_bot_left,hQR,Nat.mul_comm] using hc.symm
  have hZc : Nat.card (centerIn R) = Nat.card E * 2 := by
    rw [← hcenter,centerIn_eq_map_center,card_map_of_injective M.subtype_injective,
      Nat.card_congr (centerCongr e).toEquiv,Subgroup.center_prod,center_eq_top,
      Nat.card_congr (prodEquiv (⊤ : Subgroup E) (center (DihedralGroup (2 ^ n)))).toEquiv,
      Nat.card_prod,Nat.card_congr (topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv,
      DihedralGroup.center_card_of_equiv hn (MulEquiv.refl _)]
  have hRcard : Nat.card R = 8 * Nat.card E := by
    rw [hRc,d.core_card_eq_twice_center,hZc]
    omega
  have hMcard : Nat.card M = Nat.card E * (2 * 2 ^ n) := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,DihedralGroup.nat_card]
  have hbound := (normalizer_index_le_max_family_card N M Q inf_le_right hQM).trans
    (ElementaryDihedral.max_family_card_le_ambient M hn e)
  have hstab : N ⊓ normalizer (Q : Set G) = R := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans d.core_normalizer.le
    · exact le_inf hRN (d.core_normalizer ▸ inf_le_right)
  have hidx : R.relIndex N ≤ 2 ^ (n - 1) := by
    rw [← hstab,inf_relIndex_left]
    exact hbound
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) R N bot_le hRN
  simp only [relIndex_bot_left] at hcount
  have hcountM := relIndex_mul_relIndex (⊥ : Subgroup G) M N bot_le hMN
  simp only [relIndex_bot_left] at hcountM
  have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hNbound : Nat.card N ≤ 2 * Nat.card M := by
    calc Nat.card N = Nat.card R * R.relIndex N := hcount.symm
      _ ≤ (8 * Nat.card E) * 2 ^ (n - 1) := by rw [hRcard]; exact Nat.mul_le_mul_left _ hidx
      _ = 2 * Nat.card M := by rw [hMcard,hp]; ring
  have hle : M.relIndex N ≤ 2 := by
    have hpos : 0 < Nat.card M := Nat.card_pos
    nlinarith
  have hlt : M < N := by
    let : Group.IsNilpotent Λ := d.Λ_two.isNilpotent
    have ht : M.subgroupOf Λ < ⊤ := lt_top_iff_ne_top.mpr
      (fun he => hproper.not_ge (subgroupOf_eq_top.mp he))
    obtain ⟨x,hxn,hxm⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (M.subgroupOf Λ) ht)
    have hx : (x : G) ∈ normalizer (M : Set G) := by
      rwa [← subgroupOf_normalizer_eq hMΛ] at hxn
    exact lt_of_le_not_ge hMN (fun h => hxm (h ⟨x.property,hx⟩))
  have hne : M.relIndex N ≠ 1 := fun hh => hlt.not_ge (relIndex_eq_one.mp hh)
  have hpos : 0 < M.relIndex N := by
    have hNc : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hi : M.relIndex N = 2 := by omega
  refine ⟨hi,?_⟩
  have hRi : R.relIndex N = 2 ^ (n - 1) := by
    rw [hi,hMcard,hp] at hcountM
    rw [hRcard] at hcount
    have hEp : 0 < Nat.card E := Nat.card_pos
    nlinarith
  rw [hRi]
  exact ElementaryDihedral.max_family_card_le_ambient M hn e

/-- Every proper actual dihedral overgroup has normalizer index two. -/
theorem Input.dihedral_overgroup_normalizer_index (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M) (hproper : M < Λ) :
    M.relIndex (Λ ⊓ normalizer (M : Set G)) = 2 :=
  (d.dihedral_overgroup_indices M hM hproper).1

/-- Every maximum elementary subgroup is conjugate to the original Q under
the actual relative normalizer of the dihedral overgroup. -/
theorem Input.dihedral_overgroup_maximum_conjugate (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M) (hproper : M < Λ) :
    ∀ A ∈ elementaryAbelianMaxSubgroups M,
      ∃ n ∈ Λ ⊓ normalizer (M : Set G),
        ((K ⊔ S).pCoreIn 2).map (MulAut.conj n).toMonoidHom = A := by
  have hstab : (Λ ⊓ normalizer (M : Set G)) ⊓
      normalizer ((K ⊔ S).pCoreIn 2 : Set G) = R := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans d.core_normalizer.le
    · exact le_inf (le_inf d.proper.le (hM.1.trans M.le_normalizer))
        (d.core_normalizer ▸ inf_le_right)
  apply max_family_conjugate_of_card_le_index _ M _ inf_le_right
    (d.core_maximum_in_dihedral_overgroup M hM)
  rw [← inf_relIndex_left, hstab]
  exact (d.dihedral_overgroup_indices M hM hproper).2

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
