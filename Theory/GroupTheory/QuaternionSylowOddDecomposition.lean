module

public import Theory.GroupTheory.QuaternionSylowCentrality
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Odd-core decomposition for quaternion Sylow normalizers

Brauer–Suzuki makes the marked involution central modulo the odd core.
Coprime normalizer lifting then gives the original involution centralizer
as a supplement to the canonical odd core, retaining the original map.
Source: Aschbacher, *Sporadic Groups* (1994),45.8,p246.
-/

public section
open Subgroup BenderSuzuki.PFAppendixIII
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem oddCore_sup_centralizer_of_quaternion_sylow
    (P : Sylow 2 G) {n:ℕ} (hn:3≤n)
    (hP:Nonempty (P≃*QuaternionGroup (2^(n-2))))
    (z:G) (hz:orderOf z=2) :
    pPrimeCore 2 G⊔centralizer ({z}:Set G)=⊤ := by
  let D:=pPrimeCore 2 G
  let q:=QuotientGroup.mk' D
  have hzI : IsInvolution z := ⟨by intro he; simp [he] at hz,by rw [←hz]; exact pow_orderOf_eq_one z⟩
  have hzC := BenderSuzuki.PFAppendixII.appendixII_quotient_involution_central_public P hn hP z hzI
  let Z:=zpowers z
  let : Fact (IsPGroup 2 Z) := ⟨IsPGroup.of_card (n:=1) (by simp [Z,Nat.card_zpowers,hz])⟩
  have hZc : Z.map q≤center (G⧸D) := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hzC
  have hZnormal : (Z.map q).Normal := ⟨fun x hx g=>by
    rw [(mem_center_iff.mp (hZc hx)) g,mul_inv_cancel_right]
    exact hx⟩
  have he := normalizer_map_quotient_eq_map_normalizer 2 Z D inferInstance
    (pPrimeCore_coprime_card (p:=2) (G:=G))
  let : (Z.map q).Normal := hZnormal
  change normalizer ((Z.map q):Set (G⧸D))=(normalizer (Z:Set G)).map q at he
  rw [show normalizer ((Z.map q):Set (G⧸D))=⊤ from normalizer_eq_top (Z.map q)] at he
  rw [show normalizer (Z:Set G)=centralizer ({z}:Set G) from
    normalizer_zpowers_eq_centralizer_of_order_two z hz] at he
  have hc := congrArg (Subgroup.comap q) he
  rw [comap_top,comap_map_eq,QuotientGroup.ker_mk'] at hc
  exact (sup_comm _ _).trans hc.symm
end Subgroup
