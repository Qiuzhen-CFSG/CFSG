module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedEndpointConstruction

/-!
# Involution purity of each actual natural endpoint

The paired radical join is a Sylow two-subgroup of an endpoint of order960.
An involution in that join lies in one of its two original pure radicals:
write it as ab and use the exact rank-two centralizer C_A(b)=W. Sylow
conjugacy then transfers the original marked involution class to every
involution of the endpoint. No native affine enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem join_involution_mem
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWB : W ≤ B) (hWA : W ≤ A) (hBA : B ≤ normalizer (A : Set G))
    (hfixed : ∀ b ∈ B, b ∉ W → A ⊓ centralizer ({b} : Set G) = W)
    (x : G) (hx : x ∈ A ⊔ B) (hx2 : x ^ 2 = 1) : x ∈ A ∨ x ∈ B := by
  have hm : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hBA]
    exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hm
  by_cases hbW : b ∈ W
  · exact Or.inl (A.mul_mem ha (hWA hbW))
  · have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
    have hb2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
    have hc : a*b=b*a := by
      have hh := congrArg (fun y => a*y*b) hx2
      simpa only [pow_two, mul_assoc, ←mul_assoc a a, ←pow_two a, ha2,
        one_mul, ←mul_assoc b b, ←pow_two b, hb2, mul_one] using hh.symm
    have haW : a ∈ W := by
      rw [← hfixed b hb hbW]
      exact ⟨ha, mem_centralizer_singleton_iff.mpr hc⟩
    exact Or.inr (B.mul_mem (hWB haW) hb)

private theorem endpoint_involution_conjugate_sylow
    (S P : Subgroup G) (hSP : S ≤ P) (hS : Nat.card S = 64) (hP : Nat.card P = 960)
    (x : G) (hx : x ∈ P) (hx2 : orderOf x = 2) :
    ∃ g : P, g.val*x*g.val⁻¹ ∈ S := by
  let N := S.subgroupOf P
  have hN : Nat.card N = 64 := (Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv).trans hS
  have hNtwo : IsPGroup 2 N := IsPGroup.of_card (hN.trans (by decide : 64 = 2^6))
  have hindex : N.index = 15 := by
    have hh := N.card_mul_index
    rw [hN,hP] at hh
    omega
  let T : Sylow 2 P := hNtwo.toSylow (by rw [hindex]; decide)
  let y : P := ⟨x,hx⟩
  have hy : orderOf y = 2 := (orderOf_coe y).symm.trans hx2
  have hytwo : IsPGroup 2 (zpowers y) := IsPGroup.of_card (by rw [Nat.card_zpowers,hy]; rfl : Nat.card (zpowers y) = 2^1)
  obtain ⟨R,hR⟩ := hytwo.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P R T
  have hym : g*y*g⁻¹ ∈ T := by
    rw [←hg]
    change g*y*g⁻¹ ∈ (↑(g • R) : Set P)
    rw [Sylow.coe_smul]
    exact ⟨y,hR (mem_zpowers y),rfl⟩
  exact ⟨g,hym⟩

/-- Every involution of an actual endpoint over the original radical pair
lies in the original marked seed class. -/
theorem TypeAt.paired_endpoint_involutions (h : TypeAt z V)
    (W A B P : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hWA : W ≤ A) (hWB : W ≤ B)
    (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (hB : B = A.map (MulAut.conj p).toMonoidHom)
    (hBA : B ≤ normalizer (A : Set G))
    (hSP : A ⊔ B ≤ P) (hS : Nat.card (A ⊔ B : Subgroup G) = 64)
    (hP : Nat.card P = 960)
    (hpureA : ∀ a ∈ A, a ≠ 1 → IsConj a z)
    (hpureB : ∀ b ∈ B, b ≠ 1 → IsConj b z) :
    ∀ x ∈ P, orderOf x = 2 → IsConj x z := by
  have hfixed : ∀ b ∈ B, b ∉ W → A ⊓ centralizer ({b} : Set G) = W := by
    intro b hb hbW
    exact h.paired_plane_radical_centralizer W A hWV hW4 hWA hAC hAP p hp hpW
      b (hB ▸ hb) hbW
  intro x hx hx2
  obtain ⟨g,hg⟩ := endpoint_involution_conjugate_sylow (A ⊔ B) P hSP hS hP x hx hx2
  let a := MulAut.conj (g : G)
  have ha2 : orderOf (a x) = 2 := (a.orderOf_eq x).trans hx2
  have hane : a x ≠ 1 := by intro he; rw [he,orderOf_one] at ha2; omega
  have hapow : (a x)^2 = 1 := ha2 ▸ pow_orderOf_eq_one (a x)
  have ha : IsConj (a x) z := by
    rcases join_involution_mem W A B hWB hWA hBA hfixed (a x) hg hapow with hA | hB
    · exact hpureA _ hA hane
    · exact hpureB _ hB hane
  have hconj : IsConj x (a x) := isConj_iff.mpr ⟨(g : G),rfl⟩
  exact hconj.trans ha

end CFSG.Quasithin.HigmanSims
