module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.LocalBound
public import Theory.GroupTheory.QuaternionSylowOddDecomposition
public import Theory.GroupTheory.QuaternionSixteenSylowPromotion
/-!
# Quaternion Sylow and odd-core structure of the original cubic-line normalizer

The marked reflection rotation constructs Q₁₆. The earlier elementary
sixteen gives the local order bound; unique-involution normalizer control
promotes the same quaternion subgroup to a Sylow subgroup of N_G(W).
Brauer–Suzuki then supplies the canonical odd-core decomposition.

Only the genuine earlier reflected actors and elementary sixteen remain
explicit. Neither an ambient quaternion Sylow nor a full-normalizer product
is assumed. This is the first paragraph of Aschbacher(1994),45.8,pp245–246;
the subsequent order243 argument is a separate source step.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace CubicLine
def oddKernel (W:Subgroup G):Subgroup G:=
  (pPrimeCore 2 (normalizer (W:Set G))).map (normalizer (W:Set G)).subtype

theorem normalizer_oddCore_split (W:Subgroup G) (hz:orderOf z=2)
    (hzN:z∈normalizer (W:Set G)) (P:Sylow 2 (normalizer (W:Set G)))
    (hP:Nonempty (P≃*QuaternionGroup 4)) :
    normalizer (W:Set G)=oddKernel W⊔(normalizer (W:Set G)⊓centralizer z) := by
  let M:=normalizer (W:Set G)
  let zz:M:=⟨z,hzN⟩
  have he:=oddCore_sup_centralizer_of_quaternion_sylow P (n:=4) (by decide) hP zz
    (by rwa [orderOf_mk])
  have hcenter:(Subgroup.centralizer ({zz}:Set M)).map M.subtype=M⊓centralizer z:=by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
    · rintro ⟨hx,hxz⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hxz)),rfl⟩
  have hm:=congrArg (fun A:Subgroup M=>A.map M.subtype) he
  rw [Subgroup.map_sup,hcenter,←MonoidHom.range_eq_map,M.range_subtype] at hm
  exact hm.symm
end CubicLine
namespace IsType
variable (h:IsType z)
include h in
theorem exists_cubic_line_quaternion_normalizer (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (E:Subgroup G) [IsElementaryAbelian 2 E]
    (hEH:E≤centralizer z) (hE:Nat.card E=16) (hEQ:Nat.card (E⊓core z:Subgroup G)=8) :
    ∃W:Subgroup G,Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2) ∧
      (∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4)) ∧
      normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z) := by
  obtain ⟨W,S,hW,hWX,hfixed,hS,hzS,hmodel⟩:=h.exists_cubic_line_quaternion_sixteen_marked P m
  have hWH:W≤centralizer z:=hWX.trans (map_subtype_le _)
  have hb:Nat.card (normalizer (W:Set G)⊓centralizer z:Subgroup G)∣144:=by
    rw [inf_comm]
    exact h.cubic_line_normalizer_card_dvd W hW hWH hfixed E hEH hE hEQ
  obtain ⟨T,hT,hTe⟩:=exists_sylow_of_quaternion_sixteen_local_bound (normalizer (W:Set G)) S z
    h.involution hzS hS hmodel.some hb
  have hzN:z∈normalizer (W:Set G):=hS hzS |>.1
  exact ⟨W,hW,hWX,hfixed,⟨T,hTe⟩,CubicLine.normalizer_oddCore_split W h.involution hzN T hTe⟩
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
