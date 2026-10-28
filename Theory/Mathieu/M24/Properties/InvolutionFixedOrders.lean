module
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders.OrbitCertificate
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Defs
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Prime.Pow
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient
import all Theory.Mathieu.M24.Properties.InvolutionFixedOrders.OrbitCertificate
import all Theory.Mathieu.M24.Properties.Sylow3
import all Theory.Mathieu.M24.Block
/-!
# Odd three-parts of involutory M₂₄ fixed subgroups

An order-nine subgroup of the actual 27-element Sylow subgroup is normal.
Its noncentral element forces the central cubic into it, identifying one of
four explicit planes. The checked orbit certificate rules out a fixed-point-
free commuting involution. Thus the original marked 2B centralizer has order
not divisible by nine. Full automorphism coverage and the established 2A
order transfer this to every involutory fixed subgroup.

Internal imports reuse the certified original Sylow and Golay data. No
centralizer shape, sextet placement or alternative group carrier is assumed.
Source: Aschbacher–Smith 16.1.5(7), E.6.18 and E.6.23, printed pp.1171,252–253.
-/
open Subgroup

namespace Sporadic.Mathieu.M24InvolutionFixedOrders
open scoped Pointwise
private theorem fixes_same_orbit {i : Fin 4} {x : Fin 24} (s : Equiv.Perm (Fin 24)) (hs : s ^ 2 = 1)
    (hcomm : ∀ a b, Commute s (orbitWord i a b))
    (hx : ∃ a b, orbitWord i a b x = s x) : s x = x := by
  obtain ⟨a,b,hab⟩ := hx
  have hsq : s (s x) = x := Equiv.congr_fun hs x
  have hc := Equiv.congr_fun (hcomm a b).eq x
  change s (orbitWord i a b x) = orbitWord i a b (s x) at hc
  have htwo : orbitWord i a b (orbitWord i a b x) = x := by
    rw [hab, ← hc,hab,hsq]
  have hthree : orbitWord i a b (orbitWord i a b (orbitWord i a b x)) = x :=
    Equiv.congr_fun (orbitWord_cube i a b) x
  rw [htwo] at hthree
  exact hab.symm.trans hthree

private theorem sameStabilizer_image {i : Fin 4} (s : Equiv.Perm (Fin 24))
    (hcomm : ∀ a b, Commute s (orbitWord i a b)) (x : Fin 24) :
    sameStabilizer i x (s x) := by
  intro a b
  have he := Equiv.congr_fun (hcomm a b).eq x
  change s (orbitWord i a b x) = orbitWord i a b (s x) at he
  rw [← he]
  exact s.injective.eq_iff.symm

private theorem candidate_eq {k : Fin 2} {a : Fin 9} {b : Fin 3} (s : Equiv.Perm (Fin 24)) (hs : s ^ 2 = 1)
    (hcomm : ∀ c d, Commute s (orbitWord (smallPlane k) c d))
    (ha : s 0 = otherNine a) (hb : s 1 = otherThree b) :
    ∀ x, s x = candidate k a b x := by
  have hsq (x) : s (s x) = x := Equiv.congr_fun hs x
  have ha' : s (otherNine a) = 0 := ha ▸ hsq 0
  have hb' : s (otherThree b) = 1 := hb ▸ hsq 1
  intro x
  obtain ⟨c,d,hc⟩ := candidate_coordinates k a b x
  have he (y) : s (orbitWord (smallPlane k) c d y) = orbitWord (smallPlane k) c d (s y) :=
    Equiv.congr_fun (hcomm c d).eq y
  rcases hc with h | h | h | h
  · rw [← h.1,he,ha,h.2,h.1]
  · rw [← h.1,he,ha',h.2,h.1]
  · rw [← h.1,he,hb,h.2,h.1]
  · rw [← h.1,he,hb',h.2,h.1]

private theorem not_fixedPointFree_commuting_plane
    (s : M24) (hs : (s.val : Equiv.Perm (Fin 24)) ^ 2 = 1)
    (hfree : ∀ x, s.val x ≠ x) (i : Fin 4)
    (hw : Commute s.val (plane i)) (hz : Commute s.val rankZPerm) : False := by
  have hcomm (a b : Fin 3) : Commute s.val (orbitWord i a b) :=
    (hw.pow_right a.val).mul_right (hz.pow_right b.val)
  by_cases hi : i.val < 2
  · let j : Fin 2 := ⟨i.val,hi⟩
    have hj : (⟨j.val,by omega⟩ : Fin 4) = i := rfl
    have ho := first_orbit_unique j (s.val (if j=0 then 2 else 0))
    rw [hj] at ho
    exact hfree _ (fixes_same_orbit s.val hs hcomm (ho (sameStabilizer_image s.val hcomm _)))
  · let k : Fin 2 := ⟨i.val-2,by omega⟩
    have hk : smallPlane k = i := Fin.ext (by dsimp [smallPlane,k]; omega)
    have options := second_orbit_options k
    rw [hk] at options
    have ha := (options (s.val 0)).1 (sameStabilizer_image s.val hcomm 0)
    have hb := (options (s.val 1)).2 (sameStabilizer_image s.val hcomm 1)
    obtain ⟨a,ha⟩ := ha.resolve_left (fun h => hfree _ (fixes_same_orbit s.val hs hcomm h))
    obtain ⟨b,hb⟩ := hb.resolve_left (fun h => hfree _ (fixes_same_orbit s.val hs hcomm h))
    have he : ∀ x, s.val x = candidate k a b x :=
      candidate_eq s.val hs (hk.symm ▸ hcomm) ha.symm hb.symm
    have hB : m24GolayWord (witness k a b) ∈ m24Blocks :=
      m24GolayWord_mem_blocks_of_card_eq_eight _ (witness_card k a b)
    have hB' : s.val • m24GolayWord (witness k a b) ∈ m24Blocks := by
      have hm : s.val • m24GolayWord (witness k a b) ∈
          s.val • (m24Blocks : Set (Finset (Fin 24))) := Set.smul_mem_smul_set hB
      rwa [(mem_M24_iff s.val).mp s.property] at hm
    have himg : s.val • m24GolayWord (witness k a b) =
        (m24GolayWord (witness k a b)).image (candidate k a b) := by
      change (m24GolayWord (witness k a b)).image s.val = _
      exact congrArg (fun f => (m24GolayWord (witness k a b)).image f) (funext he)
    rw [himg] at hB'
    exact candidate_bad_parity k a b (block_parity _ hB' _)
end Sporadic.Mathieu.M24InvolutionFixedOrders

namespace Sporadic.Mathieu.M24InvolutionFixedOrders
private theorem plane_generated : ∀ q : Coordinates,
    q.1 ≠ 0 ∨ q.2.1 ≠ 0 → ∃ (i : Fin 4) (r t : Fin 3),
      plane i = (evaluate q).val ^ r.val * rankZPerm ^ t.val := by
  decide +kernel
private theorem z_as_commutator : ∀ q : Coordinates,
    q.1 ≠ 0 ∨ q.2.1 ≠ 0 → ∃ (i : Fin 2) (r : Fin 3),
      rankZ = ((![rankX,rankY] i) * evaluate q * (![rankX,rankY] i)⁻¹ *
        (evaluate q)⁻¹) ^ r.val := by
  have h : ∀ q : Coordinates,
      q.1 ≠ 0 ∨ q.2.1 ≠ 0 → ∃ (i : Fin 2) (r : Fin 3),
        rankZ.val = ((![rankX,rankY] i).val * (evaluate q).val * (![rankX,rankY] i).val⁻¹ *
          (evaluate q).val⁻¹) ^ r.val := by
    decide +kernel
  intro q hq
  obtain ⟨i,r,hr⟩ := h q hq
  exact ⟨i,r,Subtype.ext hr⟩
private theorem sylow_card : Nat.card m24Sylow3Subgroup = 27 := m24Sylow3Subgroup_card
private theorem rankZ_order : orderOf rankZ = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    change rankZPerm ^ 3 = 1
    decide +kernel
  · intro h
    have he := congrArg (fun a : M24 => a.val 0) h
    have hn : rankZPerm 0 ≠ 0 := by decide +kernel
    exact hn he
private theorem no_fixedPointFree_nine
    (s : M24) (hs : s.val ^ 2 = 1) (hfree : ∀ x, s.val x ≠ x)
    (H : Subgroup M24) (hH : Nat.card H = 9) (hHS : H ≤ m24Sylow3Subgroup)
    (hfix : ∀ x ∈ H, Commute s x) : False := by
  let S := m24Sylow3Subgroup
  let HS := H.subgroupOf S
  have hcard : Nat.card HS = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hHS).toEquiv).trans hH
  have hind : HS.index = 3 := by
    have hi := HS.card_mul_index
    rw [hcard,show Nat.card S = 27 from sylow_card] at hi
    omega
  let : HS.Normal := HS.normal_of_index_eq_minFac_card (by rw [hind,sylow_card,show (27 : ℕ) = 3^3 from rfl,Nat.pow_minFac (by decide),Nat.prime_three.minFac_eq])
  have hnot : ¬ H ≤ zpowers rankZ := by
    intro hle
    have hc := card_le_of_le hle
    rw [hH,Nat.card_zpowers,rankZ_order] at hc
    omega
  obtain ⟨x,hx,hxz⟩ := Set.not_subset.mp hnot
  obtain ⟨q,rfl⟩ := hHS hx
  have hq : q.1 ≠ 0 ∨ q.2.1 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hxz
    have he : evaluate q = rankZ ^ q.2.2.val := by
      simp only [evaluate,hn.1,hn.2,Fin.val_zero,pow_zero,one_mul]
    rw [he]
    exact pow_mem (mem_zpowers rankZ) _
  obtain ⟨j,r,hz⟩ := z_as_commutator q hq
  have hj : ![rankX,rankY] j ∈ S := by
    fin_cases j
    · exact ⟨(1,0,0), by simp [evaluate]⟩
    · exact ⟨(0,1,0), by simp [evaluate]⟩
  have hzH : rankZ ∈ H := by
    rw [hz]
    apply H.pow_mem
    let y : S := ⟨evaluate q,hHS hx⟩
    let z : S := ⟨![rankX,rankY] j,hj⟩
    have hy : y ∈ HS := hx
    have he := HS.mul_mem ((inferInstance : HS.Normal).conj_mem y hy z) (HS.inv_mem hy)
    exact he
  have hsz : Commute s.val rankZPerm := by
    exact congrArg Subtype.val (hfix _ hzH).eq
  have hsq : Commute s.val (evaluate q).val := by
    exact congrArg Subtype.val (hfix _ hx).eq
  obtain ⟨i,a,b,hp⟩ := plane_generated q hq
  exact not_fixedPointFree_commuting_plane s hs hfree i
    (hp ▸ (hsq.pow_right a.val).mul_right (hsz.pow_right b.val)) hsz
end Sporadic.Mathieu.M24InvolutionFixedOrders

namespace Sporadic.Mathieu.M24InvolutionFixedOrders
open M24InvolutionCentralizers
private theorem subtype_square {X : Type*} [Group X] (H : Subgroup X) (x : H)
    (h : x ^ 2 = 1) : (x : X) ^ 2 = 1 := congrArg H.subtype h
private theorem conjugate_twoB_square (g : M24) :
    ((MulAut.conj g involution2B : M24) : Equiv.Perm (Fin 24)) ^ 2 = 1 := by
  apply subtype_square M24
  rw [← map_pow,(orderOf_eq_prime_iff.mp involution2B_order).1,map_one]
public theorem centralizer_twoB_not_nine : ¬ 9 ∣ Nat.card centralizer2B := by
  intro hd
  obtain ⟨D,hD⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) hd
  let H : Subgroup M24 := D.map centralizer2B.subtype
  have hH : Nat.card H = 3 ^ 2 :=
    (card_map_of_injective centralizer2B.subtype_injective).trans hD
  obtain ⟨P,hP⟩ := (IsPGroup.of_card hH).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 P m24Sylow3
  let c : MulAut M24 := MulAut.conj g
  let t : M24 := c involution2B
  let K := H.map c.toMonoidHom
  have hK : Nat.card K = 9 := (card_map_of_injective c.injective).trans hH
  have hKS : K ≤ m24Sylow3Subgroup := by
    rw [← m24Sylow3_coe,← hg]
    exact map_mono hP
  have ht : t.val ^ 2 = 1 := conjugate_twoB_square g
  have hfree : ∀ x, t.val x ≠ x := by
    intro x hx
    have he := congrArg g.val.symm hx
    change g.val.symm (g.val (involution2B.val (g.val.symm x))) = g.val.symm x at he
    rw [g.val.symm_apply_apply] at he
    have hf : ∀ y : Fin 24, m24Involution2B y ≠ y := by decide +kernel
    exact hf _ he
  apply no_fixedPointFree_nine t ht hfree K hK hKS
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨z,hz,rfl⟩ := hy
  have hc : Commute involution2B (z : M24) :=
    (Subgroup.mem_centralizer_singleton_iff.mp z.property).symm
  exact hc.map c.toMonoidHom
end Sporadic.Mathieu.M24InvolutionFixedOrders

namespace Sporadic.Mathieu
/-- No involution in the full automorphism group fixes a subgroup of order nine. -/
public theorem m24_involution_not_nine_dvd_fixed_card (r : MulAut M24)
    (hr : orderOf r = 2) : ¬ 9 ∣ Nat.card r.fixedSubgroup := by
  rcases (M24InvolutionCentralizers.fixedSubgroup_alternative r hr).2 with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,M24InvolutionCentralizers.TwoA.centralizer_card]
    decide
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    exact M24InvolutionFixedOrders.centralizer_twoB_not_nine

/-- The alternating-six order is excluded in the actual involutory fixed group. -/
public theorem m24_involution_not_360_dvd_fixed_card (r : MulAut M24)
    (hr : orderOf r = 2) : ¬ 360 ∣ Nat.card r.fixedSubgroup :=
  fun h => m24_involution_not_nine_dvd_fixed_card r hr ((by decide : 9 ∣ 360).trans h)

/-- The alternating-seven order is excluded in the actual involutory fixed group. -/
public theorem m24_involution_not_2520_dvd_fixed_card (r : MulAut M24)
    (hr : orderOf r = 2) : ¬ 2520 ∣ Nat.card r.fixedSubgroup :=
  fun h => m24_involution_not_nine_dvd_fixed_card r hr ((by decide : 9 ∣ 2520).trans h)
end Sporadic.Mathieu
