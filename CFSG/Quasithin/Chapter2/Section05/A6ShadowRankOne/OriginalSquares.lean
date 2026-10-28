module
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.ExceptionalElimination
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Basic

/-!
# Squares in the exceptional dihedral A₆ shadow

An order-four square has central image in the actual Sylow subgroup of
Aut(A₆): its image lies in the inner subgroup, whose noncentral involutions
cannot be squares. Lift this central image through the faithful inner action.
The resulting factor in S_C centralizes the cyclic four and is an involution;
in D₈ it is therefore 1 or t. Together with z = t z_K this gives the exact
square membership used by the exceptional TI-fusion argument.

The dihedral hypothesis belongs to the exceptional branch and is retained
explicitly; it is constructed by the A₈ reduction before this lemma is used.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 2.5.26, p.569.
-/

public section
open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne
open A6Shadow.Frattini A6Shadow.Frattini.ElementaryCore
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

private theorem square_factors (d : EarlierSetup κ G) (a : G) (ha : a ∈ d.S)
    (ho : orderOf a = 4) :
    ∃ c ∈ d.SC, ∃ k ∈ zpowers d.zK, c * k = a ^ 2 := by
  let as : d.S := ⟨a, ha⟩
  let q := d.toImageSylow as
  have hq2 : (q ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    change d.toImageSylow as ^ 4 = 1
    rw [← map_pow]
    have ha4 : as ^ 4 = 1 := Subtype.ext (ho ▸ pow_orderOf_eq_one a)
    rw [ha4, map_one]
  have hqI : q ^ 2 ∈ sylowInner d.imageSylow := by
    let : Fact (IsPGroup 2 d.imageSylow) := ⟨d.imageSylow.isPGroup'⟩
    apply SylowGeometry.cyclicFour_le_inner d.imageSylow
    rw [← SylowGeometry.frattini_eq]
    exact pth_power_mem_frattini_of_isPGroup (p := 2) q
  have hqZ : q ^ 2 ∈ center d.imageSylow := by
    by_contra hnot
    exact SylowGeometry.inner_involution_not_square d.imageSylow (q ^ 2)
      hqI hnot hq2 q rfl
  obtain ⟨k, hk⟩ := innerAction_surjective d (⟨q ^ 2, hqI⟩ : sylowInner d.imageSylow)
  have hkmap : d.toImageSylow ⟨(k : G), k.property.1⟩ = q ^ 2 :=
    congrArg (fun z : sylowInner d.imageSylow => (z : d.imageSylow)) hk
  have hkcenter : (k : G) ∈ centerIn (d.S ⊓ d.K : Subgroup G) := by
    refine ⟨k.property, ?_⟩
    intro c hc
    let cs : (d.S ⊓ d.K : Subgroup G) := ⟨c, hc⟩
    have he : innerAction d k * innerAction d cs =
        innerAction d cs * innerAction d k := by
      apply Subtype.ext
      change d.toImageSylow ⟨k, k.property.1⟩ * d.toImageSylow ⟨c, hc.1⟩ =
        d.toImageSylow ⟨c, hc.1⟩ * d.toImageSylow ⟨k, k.property.1⟩
      rw [hkmap]
      exact (mem_center_iff.mp hqZ _).symm
    have hei : k * cs = cs * k := innerAction_injective d (by simpa only [map_mul] using he)
    exact (congrArg (fun z : (d.S ⊓ d.K : Subgroup G) => (z : G)) hei).symm
  have hkz : (k : G) ∈ zpowers d.zK := d.center_sk ▸ hkcenter
  let c : d.S := as ^ 2 * (⟨(k : G), k.property.1⟩ : d.S)⁻¹
  have hc : c ∈ d.toImageSylow.ker := by
    rw [MonoidHom.mem_ker]
    change d.toImageSylow (as ^ 2 * (⟨(k : G), k.property.1⟩ : d.S)⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hkmap]
    exact mul_inv_cancel _
  rw [d.toImageSylow_kernel] at hc
  exact ⟨c, hc, k, hkz, by simp [c, as, mul_assoc]⟩

omit [Finite G] in
private theorem dihedral_centralizing_involution (D : Subgroup G)
    (e : D ≃* DihedralGroup 4) (v c : G) (hv : v ∈ D) (hc : c ∈ D)
    (hv4 : v ^ 4 = 1) (hv2 : v ^ 2 ≠ 1) (hc2 : c ^ 2 = 1)
    (hcomm : c * v = v * c) : c = 1 ∨ c = v ^ 2 := by
  have table : ∀ v c : DihedralGroup 4, v ^ 4 = 1 → v ^ 2 ≠ 1 →
      c ^ 2 = 1 → c * v = v * c → c = 1 ∨ c = v ^ 2 := by decide +kernel
  let vd : D := ⟨v, hv⟩
  let cd : D := ⟨c, hc⟩
  have hv4' : (e vd) ^ 4 = 1 := by
    rw [← map_pow, show vd ^ 4 = 1 from Subtype.ext hv4, map_one]
  have hv2' : (e vd) ^ 2 ≠ 1 := by
    intro hh
    have hh' : vd ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using hh)
    exact hv2 (congrArg Subtype.val hh')
  have hc2' : (e cd) ^ 2 = 1 := by
    rw [← map_pow, show cd ^ 2 = 1 from Subtype.ext hc2, map_one]
  have hc' : e cd * e vd = e vd * e cd := by
    simpa only [map_mul] using congrArg e (show cd * vd = vd * cd from Subtype.ext hcomm)
  rcases table (e vd) (e cd) hv4' hv2' hc2' hc' with h | h
  · exact Or.inl (congrArg Subtype.val (e.injective (h.trans e.map_one.symm)))
  · exact Or.inr (congrArg Subtype.val (e.injective (h.trans (map_pow e vd 2).symm)))

/-- Source 2.5.26 square calculation, in its actual exceptional dihedral branch. -/
theorem original_squares_of_dihedral (d : EarlierSetup κ G)
    (e : d.SC ≃* DihedralGroup 4) (hz : d.z = d.t * d.zK)
    (V : Subgroup G) (v : G) (hV : V ≤ d.SC) (hgen : V = zpowers v)
    (hv : orderOf v = 4) (hvt : v ^ 2 = d.t)
    (a : G) (ha : a ∈ d.S) (haV : a ∈ centralizer (V : Set G))
    (hao : orderOf a = 4) : a ^ 2 ∈ zpowers d.t ⊔ zpowers d.z := by
  obtain ⟨c, hc, k, hk, hprod⟩ := square_factors d a ha hao
  have hkZ : k ∈ centerIn d.S := by
    rw [d.center_s]
    exact (show zpowers d.zK ≤ zpowers d.t ⊔ zpowers d.zK from le_sup_right) hk
  have hk2 : k ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (d.zK_order ▸ orderOf_dvd_of_mem_zpowers hk)
  have hck : Commute c k := hkZ.2 c (d.sc_le_s hc)
  have hcpow : c ^ 2 = 1 := by
    have hh : (c * k) ^ 2 = 1 := by
      rw [hprod, ← pow_mul]
      simpa only [hao] using pow_orderOf_eq_one a
    rw [hck.mul_pow, hk2, mul_one] at hh
    exact hh
  have hvV : v ∈ V := hgen ▸ mem_zpowers v
  have hvS : v ∈ d.S := d.sc_le_s (hV hvV)
  have hkv : Commute k v := (hkZ.2 v hvS).symm
  have hav : Commute a v := (haV v hvV).symm
  have hcv : c * v = v * c := by
    have hp : Commute (c * k) v := hprod ▸ hav.pow_left 2
    apply mul_right_cancel (b := k)
    calc
      (c * v) * k = (c * k) * v := by rw [mul_assoc, ← hkv.eq, ← mul_assoc]
      _ = v * (c * k) := hp.eq
      _ = (v * c) * k := (mul_assoc _ _ _).symm
  have hv4 : v ^ 4 = 1 := hv ▸ pow_orderOf_eq_one v
  have hv2 : v ^ 2 ≠ 1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hv] at hd
    norm_num at hd
  have hct : c ∈ zpowers d.t := by
    rcases dihedral_centralizing_involution d.SC e v c (hV hvV) hc hv4 hv2 hcpow hcv with h | h
    · exact h ▸ (zpowers d.t).one_mem
    · exact h ▸ hvt ▸ mem_zpowers d.t
  have hzK : d.zK ∈ zpowers d.t ⊔ zpowers d.z := by
    have he : d.zK = d.t⁻¹ * d.z := by rw [hz]; simp
    rw [he]
    exact mul_mem_sup ((zpowers d.t).inv_mem (mem_zpowers d.t)) (mem_zpowers d.z)
  rw [← hprod]
  exact (zpowers d.t ⊔ zpowers d.z).mul_mem ((show zpowers d.t ≤ zpowers d.t ⊔ zpowers d.z from le_sup_left) hct) ((zpowers_le.mpr hzK) hk)
end CFSG.Quasithin.Chapter2.A6ShadowRankOne
