module
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.QuaternionElementaryEightCentralizer

/-! Elementary factors in a parabolic meet its quaternion core in elementary
eights. Involution generation of the centralizer W forces both intersections
strictly above the shared four. The quaternion rank bound and divisibility
then force order eight. Source:14.3.18(4),(6). -/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]

theorem quaternion_factor_intersection_card_eight
    (U R W V A B:Subgroup G) (dU:QuaternionCentralProductData U)
    (hAR:A≤R) (hBR:B≤R) (hRU:R⊓U=W) (hWc:Nat.card W=16) (hVc:Nat.card V=4)
    (hVW:V≤W) (hVA:V≤A) (hVB:V≤B)
    (hEA:IsElementaryAbelian 2 A) (hEB:IsElementaryAbelian 2 B)
    (hmax:∀E:Subgroup G,IsElementaryAbelian 2 E→E≤R→E≤A∨E≤B)
    (hgen:closure {x:W|x^2=1}=⊤) :
    Nat.card (A⊓U:Subgroup G)=8 ∧ Nat.card (B⊓U:Subgroup G)=8 := by
  have hWU:W≤U := hRU.symm.le.trans inf_le_right
  have hWR:W≤R := hRU.symm.le.trans inf_le_left
  have hbound (E:Subgroup G) (he:IsElementaryAbelian 2 E) (hu:E≤U) : Nat.card E≤8 := by
    let := he
    have hh := dU.elementary_card_le_eight (E.subgroupOf U)
      (IsElementaryAbelian.subgroupOf hu)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hu).toEquiv] at hh
  have hcalc (C D:Subgroup G) (hc:IsElementaryAbelian 2 C) (hd:IsElementaryAbelian 2 D)
      (hvC:V≤C) (hvD:V≤D)
      (hcases:∀E:Subgroup G,IsElementaryAbelian 2 E→E≤R→E≤C∨E≤D) :
      Nat.card (C⊓W:Subgroup G)=8 := by
    let := hc
    let := hd
    have he:IsElementaryAbelian 2 (C⊓W:Subgroup G) := IsElementaryAbelian.of_le inf_le_left
    have hsmall := hbound (C⊓W) he (inf_le_right.trans hWU)
    have hv:V≤C⊓W := le_inf hvC hVW
    have hne:C⊓W≠V := by
      intro hh
      have hWnotD:¬W≤D := by
        intro hWD
        have hE:IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWD
        have hb:=hbound W hE hWU
        rw [hWc] at hb
        omega
      apply hWnotD
      have hcl:closure {x:W|x^2=1}≤D.subgroupOf W := by
        apply (closure_le _).mpr
        intro x hx
        have hx2:(x:G)^2=1 := congrArg Subtype.val hx
        have hE:IsElementaryAbelian 2 (zpowers (x:G)) :=
          IsElementaryAbelian.zpowers_of_pow_eq_one hx2
        rcases hcases (zpowers (x:G)) hE (zpowers_le.mpr (hWR x.property)) with hC|hD
        · exact hvD (hh ▸ (show (x:G)∈C⊓W from ⟨hC (mem_zpowers _),x.property⟩))
        · exact hD (mem_zpowers _)
      rw [hgen] at hcl
      intro x hx
      exact hcl (mem_top (⟨x,hx⟩:W))
    have hlarge:4<Nat.card (C⊓W:Subgroup G) := by
      have hh:=card_le_of_le hv
      rw [hVc] at hh
      have hneq:Nat.card (C⊓W:Subgroup G)≠4 := by
        intro heq
        exact hne (eq_of_le_of_card_ge hv (by rw [heq,hVc])).symm
      omega
    have hdiv:4∣Nat.card (C⊓W:Subgroup G) := hVc ▸ card_dvd_of_le hv
    obtain ⟨n,hn⟩:=hdiv
    omega
  have hAc:=hcalc A B hEA hEB hVA hVB hmax
  have hBc:=hcalc B A hEB hEA hVB hVA (fun E he hr=>(hmax E he hr).symm)
  have hAUeq:A⊓U=A⊓W := by rw [←hRU,←inf_assoc,inf_eq_left.mpr hAR]
  have hBUeq:B⊓U=B⊓W := by rw [←hRU,←inf_assoc,inf_eq_left.mpr hBR]
  exact ⟨hAUeq.symm ▸ hAc,hBUeq.symm ▸ hBc⟩
end Subgroup
