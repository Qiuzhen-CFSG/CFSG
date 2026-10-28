module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Extraspecial
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.OriginalKernel
public import Theory.GroupTheory.QuaternionOddCoreFitting

/-!
# The actual generalized Fitting subgroup of the cubic-line normalizer

Quaternion Sylow conjugacy makes the centralizer of D odd; by definition
it then lies in D. The marked z acts nontrivially, so F*(N_G(W))=D, with
D's ambient centralizer exactly W. The final original-source consumer has
all binary-local witnesses discharged. The actual moved line and its
normalizer quotient remain with the independent U-line source family.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_generalizedFitting (W:Subgroup G) (hW:Nat.card W=3) (hWH:W≤centralizer z)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hS:∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4))
    (hD:Nat.card (CubicLine.oddKernel W)=243) :
    (Theory.GroupTheory.generalizedFitting (normalizer (W:Set G))).map (normalizer (W:Set G)).subtype=
      CubicLine.oddKernel W ∧
    Subgroup.centralizer (CubicLine.oddKernel W:Set G)≤CubicLine.oddKernel W := by
  let M:=normalizer (W:Set G)
  have hzM:z∈M:=centralizer_le_normalizer _ (fun w hw=>mem_centralizer_singleton_iff.mp (hWH hw))
  let zz:M:=⟨z,hzM⟩
  have hz:orderOf zz=2:=by rw [orderOf_mk];exact h.involution
  have hp:IsPGroup 2 (zpowers zz):=IsPGroup.of_card (n:=1) (by simp [Nat.card_zpowers,hz])
  obtain ⟨P,hP⟩:=hp.exists_le_sylow
  obtain ⟨Q,hQ⟩:=hS
  let e:P≃*QuaternionGroup 4:=(P.equiv Q).trans hQ.some
  have hm:zz∉Subgroup.centralizer (pPrimeCore 2 M:Set M):=by
    intro hh
    have hDH:CubicLine.oddKernel W≤centralizer z:=by
      rintro x ⟨y,hy,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (hh y hy)
    have hDW:CubicLine.oddKernel W≤W:=(le_inf le_rfl hDH).trans
      (h.cubic_line_oddKernel_fixed W hW hWH hfixed).le
    have hc:=card_le_of_le hDW
    rw [hD,hW] at hc
    omega
  have hc:Nat.card (pPrimeCore 2 M)=243:=by
    rw [←card_map_of_injective M.subtype_injective]
    exact hD
  have he:=generalizedFitting_eq_oddCore_of_quaternion_sylow P e zz (hP (mem_zpowers zz)) hz hm hc
  refine ⟨congrArg (fun A:Subgroup M=>A.map M.subtype) he,?_⟩
  have hcN:=oddCore_centralizer_le_of_quaternion_sylow P e zz (hP (mem_zpowers zz)) hz hm
  intro x hx
  have hxM:x∈M:=centralizer_le_normalizer _
    ((centralizer_le (CubicLine.le_oddKernel W hW)) hx)
  have hxl:(⟨x,hxM⟩:M)∈Subgroup.centralizer (pPrimeCore 2 M:Set M):=by
    intro d hd
    apply Subtype.ext
    exact hx d ⟨d,hd,rfl⟩
  exact ⟨⟨x,hxM⟩,hcN hxl,rfl⟩
include h in
theorem original_cubic_line_fitting_of_moved_line (P:Sylow 3 (centralizer z))
    (W F:Subgroup G) (hW:Nat.card W=3)
    (hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hS:∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4))
    (hF:Nat.card F=3)
    (hFV:F≤CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hFD:F≤CubicLine.oddKernel W)
    (hVN:normalizer (F:Set G)≤normalizer
      (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype):Set G))
    (hindex:(CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer (F:Set G))=24) :
    (Theory.GroupTheory.generalizedFitting (normalizer (W:Set G))).map (normalizer (W:Set G)).subtype=
      CubicLine.oddKernel W ∧
    Nat.card (CubicLine.oddKernel W)=243 ∧
    Subgroup.centralizer (CubicLine.oddKernel W:Set G)=W ∧
    IsExtraspecial 3 (CubicLine.oddKernel W) ∧ ∀d∈CubicLine.oddKernel W,d^3=1 := by
  obtain ⟨m⟩:=h.original_reflected_marking P
  obtain ⟨hD,hcenter,he,hpow⟩:=h.source_cubic_line_extraspecial_of_moved_line P m W F hW hWX hfixed hsplit hS
    hF hFV hFD hVN hindex
  obtain ⟨hfit,hCD⟩:=h.cubic_line_generalizedFitting W hW (hWX.trans (map_subtype_le _)) hfixed hS hD
  refine ⟨hfit,hD,?_,he,hpow⟩
  apply le_antisymm
  · intro x hx
    apply hcenter.le
    exact ⟨⟨x,hCD hx⟩,mem_center_iff.mpr (fun d=>Subtype.ext (hx d d.property)),rfl⟩
  · exact le_centralizer_iff.mp (CubicLine.oddKernel_centralizes W hW)
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
