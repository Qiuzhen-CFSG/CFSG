module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelSquares
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.CoreCenter
public import Theory.GroupTheory.DihedralCentralProductThree

/-!
# The literal two-central Mathieu kernel is extraspecial of plus type

The proved square calculation makes its whole central quotient elementary.
Its center has order two, and the original octad translations give an
elementary subgroup of order sixteen containing that center. Intrinsic
recognition therefore gives the actual threefold dihedral central product.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

private theorem center_card : Nat.card (center kernel)=2 := by
  have hle : Nat.card (center kernel)≤2 := by rw [kernel_eq_twoCore]; exact core_center_card_le_two
  let : Nontrivial kernel := Finite.one_lt_card_iff_nontrivial.mp (by rw [kernel_card]; decide)
  let : Nontrivial (center kernel) := kernel_isTwoGroup.center_nontrivial
  exact Nat.le_antisymm hle (Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance))

private theorem square_mem_center (q : kernel) : q^2∈center kernel := by
  have hz : zpowers (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A)≤
      center centralizer2A := zpowers_le.mpr (mem_center_iff.mpr (fun g =>
        Subtype.ext (mem_centralizer_singleton_iff.mp g.property)))
  have hh := hz (kernel_squares_mem_marked q)
  apply mem_center_iff.mpr
  intro r
  exact Subtype.ext (mem_center_iff.mp hh r.val)

public theorem kernel_extraspecial : IsExtraspecial 2 kernel := by
  have hs (x : kernel ⧸ center kernel) : x^2=1 := by
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [←QuotientGroup.mk_pow,QuotientGroup.eq_one_iff]
      exact square_mem_center x
  have hi (x : kernel ⧸ center kernel) : x⁻¹=x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
  have he : IsElementaryAbelian 2 (kernel ⧸ center kernel) := {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc x*y=(x*y)⁻¹ := (hi _).symm
           _=y*x := by rw [mul_inv_rev,hi,hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  have hc : Nat.card (kernel ⧸ center kernel)=64 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (center kernel)
    rw [kernel_card,center_card] at hh
    omega
  exact ⟨center_card,he,Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)⟩

public theorem kernel_equiv_dihedral_three : Nonempty (kernel≃*DihedralCentralProductThree.Model) := by
  let := kernel_extraspecial
  let A := translationKernel.subgroupOf kernel
  have hA : Nat.card A=16 :=
    (Nat.card_congr (subgroupOfEquivOfLe translationKernel_le_kernel).toEquiv).trans translationKernel_card
  let : IsElementaryAbelian 2 translationKernel := {
    toIsMulCommutative := ⟨⟨fun a b => translationCoordinates.injective (by
      rw [map_mul,map_mul,mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => by
      apply translationCoordinates.injective
      rw [map_pow,map_one,pow_two]
      apply Multiplicative.toAdd.injective
      change (translationCoordinates a).toAdd+(translationCoordinates a).toAdd=0
      rw [←two_smul (ZMod 2),show (2:ZMod 2)=0 from rfl,zero_smul]) }
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf translationKernel_le_kernel
  have hZA : center kernel≤A := by
    intro x hx
    apply translationKernel_selfCentralizing
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,translationKernel_le_kernel hy⟩)
  exact DihedralCentralProductThree.exists_mulEquiv_of_elementary_sixteen kernel_card A hA hZA

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
