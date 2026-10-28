module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.OddKernel
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.CommutatorPreimage
/-!
# The common order-twenty-seven cubic layer

For the original elementary kernel V of order81 and cubic line W, coprime
conjugation splits V into its fixed nine and its displaced nine. The normalizer
odd-core decomposition puts the displaced group in D; the fixed intersection
is exactly W. Thus V∩D=[V,z]W has order27, with all ambient maps retained.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_kernel_intersection (X W:Subgroup G) (hX:Nat.card X=9) (hXH:X≤centralizer z)
    (hW:Nat.card W=3) (hWX:W≤X)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hV:IsElementaryAbelian 3 (CubicNormalizer.oddKernel X))
    (hVcard:Nat.card (CubicNormalizer.oddKernel X)=81) :
    CubicNormalizer.oddKernel X⊓CubicLine.oddKernel W=
      ⁅CubicNormalizer.oddKernel X,zpowers z⁆⊔W ∧
    Nat.card (CubicNormalizer.oddKernel X⊓CubicLine.oddKernel W:Subgroup G)=27 := by
  let V:=CubicNormalizer.oddKernel X
  let D:=CubicLine.oddKernel W
  let M:=normalizer (W:Set G)
  let L:=M⊓centralizer z
  let Z:=zpowers z
  let E:=⁅V,Z⁆
  let : IsElementaryAbelian 3 V:=hV
  have hXV:X≤V:=CubicNormalizer.le_oddKernel X hX (h.toCentralizerHypothesis.cubic_centralizer X hX hXH)
  have hWH:W≤centralizer z:=hWX.trans hXH
  have hVM:V≤M:=
    ((map_subtype_le _:V≤Subgroup.centralizer (X:Set G)).trans (centralizer_le hWX)).trans
      (centralizer_le_normalizer _)
  have hzM:z∈M:=centralizer_le_normalizer _ (fun w hw=>mem_centralizer_singleton_iff.mp (hWH hw))
  have hMN:M≤normalizer (D:Set G):=CubicLine.normalizer_normalizes_oddKernel W
  have hZN:Z≤normalizer (D:Set G):=zpowers_le.mpr (hMN hzM)
  have hLZ:L≤Subgroup.centralizer (Z:Set G):=by
    rw [le_centralizer_iff,zpowers_le]
    intro l hl
    exact mem_centralizer_singleton_iff.mp hl.2
  have hpre:M≤commutatorPreimage M Z D:=by
    apply (show M=D⊔L from hsplit).le.trans
    apply sup_le
    · exact le_commutatorPreimage (map_subtype_le _)
        (le_normalizer_iff_commutator_le_left.mp hZN)
    · exact le_commutatorPreimage inf_le_left
        (by rw [commutator_eq_bot_iff_le_centralizer.mpr hLZ];exact bot_le)
  have hED:E≤D:=
    (commutator_mono (hVM.trans hpre) le_rfl).trans
      (commutator_commutatorPreimage_le M Z D hMN)
  have hZV:Z≤normalizer (V:Set G):=zpowers_le.mpr
    (CubicNormalizer.normalizer_normalizes_oddKernel X
      (centralizer_le_normalizer _ (fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx))))
  have hEV:E≤V:=le_normalizer_iff_commutator_le_left.mp hZV
  have hcenZ:Subgroup.centralizer (Z:Set G)=centralizer z:=by
    change Subgroup.centralizer (zpowers z:Set G)=Subgroup.centralizer {z}
    rw [Subgroup.zpowers_eq_closure,centralizer_closure]
  have hVX:V⊓Subgroup.centralizer (Z:Set G)=X:=by
    rw [hcenZ]
    exact h.toCentralizerHypothesis.cubic_oddKernel_fixed X hX hXH
  have hcop:Nat.Coprime (Nat.card Z) (Nat.card V):=by
    rw [Nat.card_zpowers,h.involution,hVcard]
    decide
  have hgen:V=E⊔X:=by
    simpa only [hVX] using eq_commutator_sup_centralizer_of_solvable_coprime V Z hZV
      (Group.isSolvable_of_comm fun x y=>IsMulCommutative.is_comm.comm x y) hcop
  have hdis:Disjoint E X:=by
    simpa only [hVX] using commutator_disjoint_centralizer_of_coprime V Z hZV hcop
  have hVV:V≤Subgroup.centralizer (V:Set G):=by
    intro x hx y hy
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=V)).comm (⟨y,hy⟩:V) ⟨x,hx⟩)
  have hXE:X≤normalizer (E:Set G):=
    (hXV.trans hVV |>.trans (centralizer_le hEV)).trans (centralizer_le_normalizer _)
  have hEc:Nat.card E=9:=by
    have hh:=card_sup_eq_mul_of_normalizes_of_disjoint E X hXE hdis
    rw [←hgen,hVcard,hX] at hh
    omega
  have hDX:D⊓X=W:=by
    apply le_antisymm
    · exact (inf_le_inf_left D hXH).trans (h.cubic_line_oddKernel_fixed W hW hWH hfixed).le
    · exact le_inf (CubicLine.le_oddKernel W hW) hWX
  have heq:V⊓D=E⊔W:=by
    apply le_antisymm
    · intro v hv
      have hh:v∈(E:Set G)*(X:Set G):=by
        rw [←coe_mul_of_right_le_normalizer_left E X hXE,←hgen]
        exact hv.1
      obtain ⟨e,he,x,hx,hex⟩:=hh
      have hxd:x∈D:=by
        have hd:=D.inv_mem (hED he)
        have hh:=D.mul_mem hd hv.2
        rw [←hex] at hh
        simpa only [inv_mul_cancel_left] using hh
      rw [←hex]
      exact mul_mem_sup he (hDX.le ⟨hxd,hx⟩)
    · exact sup_le (le_inf hEV hED)
        (le_inf (hWX.trans hXV) (CubicLine.le_oddKernel W hW))
  refine ⟨heq,?_⟩
  rw [heq,card_sup_eq_mul_of_normalizes_of_disjoint E W (hWX.trans hXE)
    (hdis.mono_right hWX),hEc,hW]
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
