module
public import Theory.Mathieu.M22.Properties.ConjugateGeneration
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Theory.GroupTheory.AutomorphismTowerSimple
/-!
# Three conjugates in a cubic Mathieu cover

The three-conjugate theorem in the actual M₂₂ quotient lifts through the
cubic center. An involution survives the odd kernel, and perfectness removes
the central supplement. The result retains the literal lifted conjugators.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1;
application to Aschbacher–Smith 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22TripleCover
variable {B : Type*} [Group B] [IsQuasisimple B]

/-- Every involution generates the full perfect cubic cover with two conjugates. -/
theorem three_conjugates_generate (e : (B ⧸ center B) ≃* M22)
    (hc : Nat.card (center B) = 3) (t : B) (ht : orderOf t = 2) :
    ∃ g : Fin 3 → B, closure (Set.range fun i => g i * t * (g i)⁻¹) = ⊤ := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have htq : orderOf (q t) = 2 := by
    apply orderOf_eq_prime
    · rw [←map_pow,←ht,pow_orderOf_eq_one,map_one]
    · intro hh
      have htc : t ∈ center B := hk ▸ hh
      have hd := orderOf_dvd_natCard (⟨t,htc⟩ : center B)
      rw [←Subgroup.orderOf_coe,ht,hc] at hd
      norm_num at hd
  obtain ⟨c,hcgen⟩ := m22_three_conjugates_generate (q t) htq
  choose g hg using fun i => hq (c i)
  refine ⟨g,top_unique ?_⟩
  apply le_of_map_le_of_perfect q hk.le ⊤
  rw [M22ConjugateGeneration.map_conjugate_closure]
  simp only [hg,hcgen,le_top]
end Sporadic.Mathieu.M22TripleCover

namespace Sporadic.Mathieu.M22TripleCover
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] (B : Subgroup G) [B.Normal] [IsQuasisimple B]

/-- Three conjugates of the original inner involution generate its entire
join with the component, including any central involution discrepancy. -/
theorem three_inner_conjugates_generate
    (e : (B ⧸ center B) ≃* M22) (hc : Nat.card (center B) = 3)
    (t : G) (ht : t ^ 2 = 1) (hgen : B ⊔ zpowers t = ⊤)
    (hi : ∃ b : B, MulAut.conjNormal (H := B) t = MulAut.conj b)
    (hn : MulAut.conjNormal (H := B) t ≠ 1) :
    ∃ g : Fin 3 → G, closure (Set.range fun i => g i * t * (g i)⁻¹) = ⊤ := by
  obtain ⟨k,hk⟩ := hi
  have hk2 : k ^ 2 ∈ center B := by
    rw [←DoubleCoverCentralizer.conj_kernel,MonoidHom.mem_ker,map_pow,←hk,←map_pow,ht,map_one]
  have hk6 : (k ^ 3) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨k^2,hk2⟩ : center B))
    rw [hc] at hh
    simpa only [coe_pow,coe_one,←pow_mul] using congrArg Subtype.val hh
  let b : B := k ^ 3
  have hb : MulAut.conjNormal (H := B) t = MulAut.conj b := by
    change _ = MulAut.conj (k^3)
    rw [map_pow,←hk,←map_pow,pow_succ,ht,one_mul]
  have hb1 : b ≠ 1 := by intro hh; apply hn; rw [hb,hh,map_one]
  have htb : Commute t (b : G) := by
    have he := congrArg (fun f : MulAut B => (f b : G)) hb
    change t*b*t⁻¹ = b*b*(b : G)⁻¹ at he
    rw [mul_inv_cancel_right] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  let d := t * (b : G)⁻¹
  let q : G →* MulAut B := MulAut.conjNormal
  have hdK : d ∈ centralizer (B : Set G) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    change MulAut.conjNormal (H := B) (t*(b : G)⁻¹) = 1
    rw [map_mul,map_inv,MulAut.conjNormal_val,hb,mul_inv_cancel]
  have hdZ : d ∈ center G := by
    have hall : (⊤ : Subgroup G) ≤ centralizer ({d} : Set G) := by
      rw [←hgen]
      refine sup_le ?_ (zpowers_le.mpr ?_)
      · intro x hx
        exact mem_centralizer_singleton_iff.mpr (hdK x hx)
      · exact mem_centralizer_singleton_iff.mpr ((Commute.refl t).mul_right htb.inv_right).eq
    exact mem_center_iff.mpr fun x => mem_centralizer_singleton_iff.mp (hall (mem_top x))
  have hqker : q.ker ≤ center G := by
    intro x hx
    have hxB : x ∈ centralizer (B : Set G) := by
      rwa [←MulAut.conjNormal_ker_eq_centralizer]
    have hxt : Commute x t := by
      have hxD : Commute x d := mem_center_iff.mp hdZ x
      have hxB' : Commute x (b : G) := (hxB b b.property).symm
      simpa only [d,inv_mul_cancel_right] using hxD.mul_right hxB'
    have hall : (⊤ : Subgroup G) ≤ centralizer ({x} : Set G) := by
      rw [←hgen]
      exact sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hxB y hy))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxt.eq.symm))
    exact mem_center_iff.mpr fun y => mem_centralizer_singleton_iff.mp (hall (mem_top y))
  obtain ⟨g,hg⟩ := three_conjugates_generate e hc b (orderOf_eq_prime hk6 hb1)
  let J := closure (Set.range fun i => (g i : G) * t * (g i : G)⁻¹)
  have hBJ : B ≤ J := by
    apply le_of_map_le_of_perfect q hqker
    have hmap := congrArg (Subgroup.map ((q.comp B.subtype))) hg
    rw [M22ConjugateGeneration.map_conjugate_closure,←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype] at hmap
    rw [←hmap,M22ConjugateGeneration.map_conjugate_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨i,rfl⟩
    refine ⟨i,?_⟩
    change q (g i) * q t * (q (g i))⁻¹ = q (g i) * q b * (q (g i))⁻¹
    rw [show q t = q b from by
      change MulAut.conjNormal t = MulAut.conjNormal (b : G)
      rw [MulAut.conjNormal_val]
      exact hb]
  have htJ : t ∈ J := by
    have hh := Subgroup.subset_closure (k := Set.range fun i => (g i : G)*t*(g i : G)⁻¹) ⟨0,rfl⟩
    have hgg := hBJ (g 0).property
    have he := J.mul_mem (J.mul_mem (J.inv_mem hgg) hh) hgg
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he
  exact ⟨fun i => (g i : G),top_unique (hgen ▸ sup_le hBJ (zpowers_le.mpr htJ))⟩
end Sporadic.Mathieu.M22TripleCover
