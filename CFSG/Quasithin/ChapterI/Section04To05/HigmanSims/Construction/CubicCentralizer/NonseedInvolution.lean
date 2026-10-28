module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedOppositeClass
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.Reflection
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.Reflection
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.FixedCore

/-!
# An actual nonseed involution in the cubic centralizer

Use the original pure sixteen fixed by a conjugate of the specified cubic.
Its cubic-norm reflection remains in that same sixteen. The opposite
reflection, obtained by multiplying by the original central cyclic-four
generator, centralizes the cubic and is outside the original marked class
by the point-core incidence obstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Every original point-centralizer cubic centralizes an actual involution
outside the original marked involution class. -/
theorem TypeAt.exists_nonseed_cubic_involution (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t=3) :
    ∃ x:G, orderOf x=2 ∧ Commute x t ∧ ¬ IsConj x z := by
  obtain ⟨u, c, a, E, huV, hu1, huT, hEn, _, _, hc4, hc2, hcZ,
    ha2, _, _, hac, _, hAe, hA16, hBe, hB16, _, _, _, hCA, _, _, _, _, hpure, _, hpoints, _⟩ :=
    h.exists_all_point_core_eights
  let A := E.val ⊔ zpowers a
  let := hAe
  let B := E.val ⊔ zpowers (c*a)
  let := hBe
  have huA : u ∈ A := (show E.val ≤ A from le_sup_left) E.property.2.1
  have haA : a ∈ A := (show zpowers a ≤ A from le_sup_right) (mem_zpowers a)
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  obtain ⟨m, hm⟩ := h.seed_transitive (⟨u, huV⟩ : V) ⟨z, h.involution_mem_seed⟩
    (fun he => hu1 (congrArg Subtype.val he)) (fun he => hz1 (congrArg Subtype.val he))
  have hmu : (m : G) * u * (m : G)⁻¹ = z := congrArg Subtype.val hm
  let t0 := (MulAut.conj (m : G)).symm t
  have ht0 : t0 ∈ involutionCentralizer u := by
    apply mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj (m : G)).injective
    simp only [map_mul]
    rw [show (MulAut.conj (m : G)) t0 = t from (MulAut.conj (m : G)).apply_symm_apply t]
    change t * ((m : G) * u * (m : G)⁻¹) = ((m : G) * u * (m : G)⁻¹) * t
    rw [hmu]
    exact mem_centralizer_singleton_iff.mp ht
  have ht03 : orderOf t0 = 3 := ((MulAut.conj (m : G)).symm.orderOf_eq t).trans ht3
  let H := involutionCentralizer u
  let N := (normalizer (A : Set G)).subgroupOf H
  have hN : Nat.card N = 768 := by
    rw [← card_subtype H N, subgroupOf_map_subtype]
    exact h.sixteen_normalizer_point_card A hA16 hCA hpure hpoints u huA hu1
  have hi : N.index = 10 := by
    have hh := N.card_mul_index
    rw [hN, show Nat.card H = 7680 from huT.centralizer_card] at hh
    omega
  obtain ⟨g, hg⟩ := Theory.GroupAction.exists_conjugate_mem_of_prime_order N
    (x := (⟨t0, ht0⟩ : H)) (by decide : Nat.Prime 3)
    ((orderOf_coe _).symm.trans ht03) (by rw [hi]; decide)
  let s : G := (g : G)⁻¹ * t0 * (g : G)
  have hsA : s ∈ normalizer (A : Set G) := hg
  have hsH : s ∈ H := H.mul_mem (H.mul_mem (H.inv_mem g.property) ht0) g.property
  have hs3 : orderOf s = 3 := by
    simpa only [s, MulAut.conj_apply, inv_inv] using
      ((MulAut.conj (g : G)⁻¹).orderOf_eq t0).trans ht03
  have hcs : Commute c s := cubic_central_four huT s c hsH hs3 hc4 hcZ
  obtain ⟨b, hbA, hb2, hbs, hbc⟩ := norm_reflection A s c a hsA
    (hs3 ▸ pow_orderOf_eq_one s) hcs haA hac
  let e := MulAut.conj ((m : G) * (g : G))
  have heu : e u = z := by
    have hgu : (g : G) * u * (g : G)⁻¹ = u := by
      rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
    change ((m : G) * (g : G)) * u * ((m : G) * (g : G))⁻¹ = z
    calc
      _ = (m : G) * ((g : G) * u * (g : G)⁻¹) * (m : G)⁻¹ := by group
      _ = z := by rw [hgu, hmu]
  have hes : e s = t := by
    change ((m : G) * (g : G)) * ((g : G)⁻¹ *
      ((m : G)⁻¹ * t * (m : G)) * (g : G)) * ((m : G) * (g : G))⁻¹ = t
    group
  have hcE (y:G) (hy:y∈E.val) : Commute y c := by
    obtain ⟨q,hq,he⟩ := hcZ
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp hq ⟨y,E.property.1 hy⟩)
  have hbE : b∉E.val := by
    intro hb
    have he : c=c⁻¹ := by simpa only [(hcE b hb).eq,mul_inv_cancel_right] using hbc
    have hc22 : c^2=1 := by
      calc
        c^2 = c⁻¹*c := by rw [pow_two]; exact congrArg (· * c) he
        _ = 1 := inv_mul_cancel c
    have hd := orderOf_dvd_of_pow_eq_one hc22
    rw [hc4] at hd
    norm_num at hd
  have haE : a∉E.val := by
    intro ha
    have he : c=c⁻¹ := by simpa only [(hcE a ha).eq,mul_inv_cancel_right] using hac
    have hc22 : c^2=1 := by
      calc
        c^2 = c⁻¹*c := by rw [pow_two]; exact congrArg (· * c) he
        _ = 1 := inv_mul_cancel c
    have hd := orderOf_dvd_of_pow_eq_one hc22
    rw [hc4] at hd
    norm_num at hd
  have hi : (E.val.subgroupOf A).index=2 := by
    have hh := (E.val.subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show E.val≤A from le_sup_left)).toEquiv,
      E.property.2.2.2,hA16] at hh
    omega
  have hbaE : b*a∈E.val :=
    (mul_mem_iff_of_index_two hi (a:= (⟨b,hbA⟩:A)) (b:= (⟨a,haA⟩:A))).mpr
      (iff_of_false hbE haE)
  have hcba : c*b=(b*a)*(c*a) := by
    calc
      c*b = c*((b*a)*a) := by simp only [mul_assoc,←pow_two,ha2,mul_one]
      _ = (b*a)*(c*a) := by rw [←mul_assoc,(hcE (b*a) hbaE).eq.symm,mul_assoc]
  have hcbB : c*b∈B := by
    rw [hcba]
    exact B.mul_mem (mem_sup_left hbaE) (mem_sup_right (mem_zpowers (c*a)))
  have hcbE : c*b∉E.val := by
    intro hh
    have hcC := hcE (c*b) hh
    have hbcC : Commute b c := by
      have he := hcC.eq
      have he' := congrArg (fun x:G => c⁻¹*x) he
      change b*c=c*b
      simpa only [mul_assoc,inv_mul_cancel_left] using he'
    have he : c=c⁻¹ := by simpa only [hbcC.eq,mul_inv_cancel_right] using hbc
    have hc22 : c^2=1 := by
      calc
        c^2 = c⁻¹*c := by rw [pow_two]; exact congrArg (· * c) he
        _ = 1 := inv_mul_cancel c
    have hd := orderOf_dvd_of_pow_eq_one hc22
    rw [hc4] at hd
    norm_num at hd
  have huz : IsConj u z := hpure u huA hu1
  have hpureu : ∀x∈A,x≠1→IsConj x u := fun x hx hx1 => (hpure x hx hx1).trans huz.symm
  have hnot := huT.opposite_nonseed_reflection_not_isConj E hEn A B hA16 hB16
    le_sup_left le_sup_left c b hc2 hcZ hbA hbE hcbB hcbE hbc hpureu
  have hcb2 : orderOf (c*b)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) (c*b) hcbB)
    (fun he => hcbE (he ▸ E.val.one_mem))
  have hcbs : Commute (c*b) s := hcs.mul_left hbs
  refine ⟨e (c*b),(e.orderOf_eq _).trans hcb2,?_,?_⟩
  · have hh := hcbs.map e.toMonoidHom
    change Commute (e (c*b)) (e s) at hh
    rwa [hes] at hh
  · intro hh
    exact hnot (((isConj_iff.mpr ⟨(m:G)*(g:G),rfl⟩ : IsConj (c*b) (e (c*b))).trans hh).trans huz.symm)

end CFSG.Quasithin.HigmanSims
