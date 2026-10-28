module
public import Theory.GroupAction.CoprimeNormalizerDecomposition
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Injective

/-!
# Pointwise fixed kernel of a binary cubic normalizer

For an elementary sixteen, a cubic with a fixed four splits the group into
two four-groups. An automorphism normalizing the cubic and fixing the first
factor acts faithfully on the second, whose automorphism group has order six.
This is the small action bound in Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
variable {E:Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- Automorphisms normalizing a cubic and fixing its four-space pointwise have order dividing six. -/
theorem cubic_fixed_kernel_card_dvd_six (hE:Nat.card E=16)
    (D:Subgroup (MulAut E)) (hD:Nat.card D=3)
    (hF:Nat.card (FixedPoints.subgroup D E)=4) :
    Nat.card (normalizer (D:Set (MulAut E)) ⊓
      fixingSubgroup (MulAut E) (FixedPoints.subgroup D E:Set E) : Subgroup (MulAut E))∣6 := by
  let F:=FixedPoints.subgroup D E
  let C:=commutatorAction D E
  let K:=normalizer (D:Set (MulAut E)) ⊓ fixingSubgroup (MulAut E) (F:Set E)
  have hcop:Nat.Coprime (Nat.card D) (Nat.card E) := by rw [hD,hE]; decide
  have hcompl:IsCompl F C :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun a b:E=>mul_comm a b)) hcop inferInstance
  have hC:Nat.card C=4 := by
    have hh:=card_sup_eq_mul_of_normalizes_of_disjoint F C
      (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
    rw [hcompl.sup_eq_top,card_top,hE,hF] at hh
    omega
  let : IsInvariant K E C := commutatorAction_isInvariant_of_normalizing_actor K D inf_le_left
  let f:=MulDistribMulAction.toMulAut K C
  have hf:Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨u,hu,c,hc,rfl⟩:=Subgroup.mem_sup.mp (show x∈F⊔C from hcompl.sup_eq_top ▸ mem_top x)
    have huf : (a:MulAut E) u=u := (mem_fixingSubgroup_iff (MulAut E)).mp a.property.2 u hu
    have hcf : (a:MulAut E) c=c := congrArg Subtype.val (MulEquiv.congr_fun ha (⟨c,hc⟩:C))
    change (a:MulAut E) (u*c)=u*c
    rw [map_mul,huf,hcf]
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective C.subtype C.subtype_injective
  have hAut:Nat.card (MulAut C)=6 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 (by simpa using hC)]
    decide
  exact hAut ▸ card_dvd_of_injective f hf
end Theory.GroupAction
