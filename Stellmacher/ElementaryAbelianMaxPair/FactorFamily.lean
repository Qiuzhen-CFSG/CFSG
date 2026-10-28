module
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.CentralProductProjection
public import Stellmacher.ElementaryAbelianMaxPair.CentralProduct
/-! # Maximum elementary subgroups across a central cover
A maximum elementary subgroup of a commuting product absorbs the full
preimage of its quotient image whenever that preimage is elementary. It
therefore splits into its two factor intersections. The exact order formula
for a commuting product shows that both intersections have maximum order
in their own factors, even when the shared central kernel is nontrivial.
Source: Aschbacher--Smith 2.5.7, printed p.555, the second Thompson claim.
-/
public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
variable {G Y:Type*} [Group G] [Finite G] [Group Y]
theorem maxFamily_factors_of_split (S K C A:Subgroup G)
    (hKS:K≤S) (hCS:C≤S) (hc:K≤centralizer (C:Set G))
    (hA:A∈elementaryAbelianMaxSubgroups S)
    (hZ:K⊓C≤A) (ha:A=(A⊓K)⊔(A⊓C)) :
    A⊓K∈elementaryAbelianMaxSubgroups K ∧
      A⊓C∈elementaryAbelianMaxSubgroups C := by
  let : IsElementaryAbelian 2 A:=hA.2.1
  let : IsElementaryAbelian 2 (A⊓K:Subgroup G):=IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A⊓C:Subgroup G):=IsElementaryAbelian.of_le inf_le_left
  have hc':A⊓K≤centralizer (A⊓C:Set G):=
    inf_le_right.trans (hc.trans (centralizer_le inf_le_right))
  have hi:(A⊓K)⊓(A⊓C)=K⊓C:=by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    · exact le_inf (le_inf hZ inf_le_left) (le_inf hZ inf_le_right)
  have hprod:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (A⊓K) (A⊓C)
    ((le_centralizer_iff.mp hc').trans (Subgroup.centralizer_le_normalizer _))
  rw [hi,←ha] at hprod
  constructor
  · refine ⟨inf_le_right,inferInstance,?_⟩
    intro B hBK hB
    let :=hB
    have hbc:B≤centralizer (A⊓C:Set G):=hBK.trans (hc.trans (centralizer_le inf_le_right))
    have hbe:IsElementaryAbelian 2 (B⊔(A⊓C):Subgroup G):=
      IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hbc)
    have hsize:=hA.2.2 (B⊔(A⊓C)) (sup_le (hBK.trans hKS) (inf_le_right.trans hCS)) hbe
    have hb:=card_mul_eq_card_inf_mul_card_sup_of_normalizes B (A⊓C)
      ((le_centralizer_iff.mp hbc).trans (Subgroup.centralizer_le_normalizer _))
    have hic:Nat.card (B⊓(A⊓C):Subgroup G)≤Nat.card (K⊓C:Subgroup G):=
      card_le_of_le (le_inf (inf_le_left.trans hBK) (inf_le_right.trans inf_le_right))
    have he:Nat.card B*Nat.card (A⊓C:Subgroup G)≤Nat.card (A⊓K:Subgroup G)*Nat.card (A⊓C:Subgroup G):=by
      rw [hb,hprod]
      exact Nat.mul_le_mul hic hsize
    exact Nat.le_of_mul_le_mul_right he Nat.card_pos
  · refine ⟨inf_le_right,inferInstance,?_⟩
    intro B hBC hB
    let :=hB
    have hbc:A⊓K≤centralizer (B:Set G):=inf_le_right.trans (hc.trans (centralizer_le hBC))
    have hbe:IsElementaryAbelian 2 ((A⊓K)⊔B:Subgroup G):=
      IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hbc)
    have hsize:=hA.2.2 ((A⊓K)⊔B) (sup_le (inf_le_right.trans hKS) (hBC.trans hCS)) hbe
    have hb:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (A⊓K) B
      ((le_centralizer_iff.mp hbc).trans (Subgroup.centralizer_le_normalizer _))
    have hic:Nat.card ((A⊓K)⊓B:Subgroup G)≤Nat.card (K⊓C:Subgroup G):=
      card_le_of_le (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans hBC))
    have he:Nat.card (A⊓K:Subgroup G)*Nat.card B≤Nat.card (A⊓K:Subgroup G)*Nat.card (A⊓C:Subgroup G):=by
      rw [hb,hprod]
      exact Nat.mul_le_mul hic hsize
    exact Nat.le_of_mul_le_mul_left he Nat.card_pos

theorem maxFamily_split_central_cover_of_le (S K C:Subgroup G) (q:K→*Y)
    (hq:q.ker=C.subgroupOf K)
    (hlift:∀W:Subgroup Y,IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q))
    (hc:K≤centralizer (C:Set G)) (hKCS:K⊔C≤S)
    (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups S) (hAKC:A≤K⊔C) :
    A=(A⊓K)⊔(A⊓C) ∧
      A⊓K∈elementaryAbelianMaxSubgroups K ∧
      A⊓C∈elementaryAbelianMaxSubgroups C := by
  obtain ⟨π,hπ,hker⟩:=Subgroup.exists_sup_projection K C hc q hq
  let f:=π.comp (inclusion hAKC)
  let W:=f.range
  let : IsElementaryAbelian 2 A:=hA.2.1
  let : IsElementaryAbelian 2 W:=IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let V:=(W.comap q).map K.subtype
  let : IsElementaryAbelian 2 (W.comap q):=hlift W inferInstance
  let : IsElementaryAbelian 2 V:=IsElementaryAbelian.map K.subtype
  have hVK:V≤K:=map_subtype_le _
  have hVC:V≤centralizer (C:Set G):=hVK.trans hc
  have hAVC:A≤V⊔C:=by
    intro a ha
    have hp:a∈(K:Set G)*(C:Set G):=by
      rw [←coe_mul_of_left_le_normalizer_right K C (hc.trans (Subgroup.centralizer_le_normalizer _))]
      exact hAKC ha
    obtain ⟨k,hk,c,hc',hkc⟩:=hp
    have he:inclusion hAKC (⟨a,ha⟩:A)=
        inclusion le_sup_left (⟨k,hk⟩:K)*inclusion le_sup_right (⟨c,hc'⟩:C):=Subtype.ext hkc.symm
    have hcp:π (inclusion le_sup_right (⟨c,hc'⟩:C))=1:=by
      apply MonoidHom.mem_ker.mp
      rw [hker]
      exact hc'
    have hqk:q ⟨k,hk⟩∈W:=by
      refine ⟨⟨a,ha⟩,?_⟩
      change π (inclusion hAKC (⟨a,ha⟩:A))=q ⟨k,hk⟩
      rw [he,map_mul,hπ,hcp,mul_one]
    rw [←hkc]
    exact mul_mem_sup ⟨⟨k,hk⟩,hqk,rfl⟩ hc'
  have hVV:V≤centralizer (V:Set G):=by
    intro v hv w hw
    let : CommGroup V:=IsMulCommutative.instCommGroup
    exact congrArg Subtype.val (mul_comm (⟨w,hw⟩:V) ⟨v,hv⟩)
  have hVA:V≤centralizer (A:Set G):=by
    exact le_centralizer_iff.mp (hAVC.trans
      (sup_le hVV (le_centralizer_iff.mp hVC)))
  have hve:IsElementaryAbelian 2 (A⊔V:Subgroup G):=IsElementaryAbelian.sup_of_le_centralizer hVA
  have hVA':V≤A:=by
    have he:A=A⊔V:=eq_of_le_of_card_ge le_sup_left
      (hA.2.2 _ (sup_le hA.1 (hVK.trans (le_sup_left.trans hKCS))) hve)
    rw [he]
    exact le_sup_right
  have hZ:K⊓C≤A:=by
    intro k hk
    apply hVA'
    refine ⟨⟨k,hk.1⟩,?_,rfl⟩
    change q ⟨k,hk.1⟩∈W
    have he:q ⟨k,hk.1⟩=1:=MonoidHom.mem_ker.mp (hq.symm ▸ hk.2)
    rw [he]
    exact W.one_mem
  have ha:A=(A⊓K)⊔(A⊓C):=by
    apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    intro a ha
    have hp:a∈(V:Set G)*(C:Set G):=by
      rw [←coe_mul_of_left_le_normalizer_right V C (hVC.trans (Subgroup.centralizer_le_normalizer _))]
      exact hAVC ha
    obtain ⟨v,hv,c,hc',hvc⟩:=hp
    have hcA:c∈A:=by
      have hh:=A.mul_mem (A.inv_mem (hVA' hv)) ha
      rw [←hvc,inv_mul_cancel_left] at hh
      exact hh
    rw [←hvc]
    exact mul_mem_sup ⟨hVA' hv,hVK hv⟩ ⟨hcA,hc'⟩
  exact ⟨ha,maxFamily_factors_of_split S K C A (le_sup_left.trans hKCS)
    (le_sup_right.trans hKCS) hc hA hZ ha⟩
theorem maxFamily_split_central_cover (S K C:Subgroup G) (q:K→*Y)
    (hq:q.ker=C.subgroupOf K)
    (hlift:∀W:Subgroup Y,IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q))
    (hJ:elementaryAbelianMaxJ S=K⊔C) (hc:K≤centralizer (C:Set G))
    (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups S) :
    A=(A⊓K)⊔(A⊓C) ∧
      A⊓K∈elementaryAbelianMaxSubgroups K ∧
      A⊓C∈elementaryAbelianMaxSubgroups C := by
  have hJS:elementaryAbelianMaxJ S≤S:=sSup_le fun _ h=>h.1
  exact maxFamily_split_central_cover_of_le S K C q hq hlift hc
    (hJ ▸ hJS) A hA (hJ ▸ le_sSup hA)
end Stellmacher
