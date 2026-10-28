module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.Reflection
public import Theory.GroupTheory.NormalizingInvolutionCard
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.Reflection
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.FixedCore

/-!
# A pure original four-group in the cubic centralizer

The cubic norm reflection lies in the same pure sixteen as the marked
point. Retaining that actual witness through conjugation makes their
four-group pure. This conclusion is not inferred from an arbitrary
reflection in a dihedral subgroup.

The same-package import-all edges reuse the original cubic norm and
central-core transport calculations while the frozen producer is unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The actual cubic centralizer contains an elementary four through the
original marked point, all of whose nonidentity elements are conjugate to
that point. Its reflection and original central cyclic four are retained. -/
theorem TypeAt.exists_pure_cubic_four (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3) :
    ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ centralizer ({t} : Set G) ∧ z ∈ F ∧
      (∀ x ∈ F, x ≠ 1 → IsConj x z) ∧
      ∃ c b : G, orderOf c = 4 ∧ c ^ 2 = z ∧
        c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
          ((involutionCentralizer z).pCoreIn 2).subtype ∧ Commute c t ∧
        orderOf b = 2 ∧ b ∈ F ∧ b ∉ zpowers z ∧ b * c * b⁻¹ = c⁻¹ ∧
        F = zpowers z ⊔ zpowers b := by
  obtain ⟨u, c, a, E, huV, hu1, huT, _, _, _, hc4, hc2, hcZ,
    _, _, _, hac, _, hAe, hA16, _, _, _, _, _, hCA, _, _, _, _, hpure, _, hpoints, _⟩ :=
    h.exists_all_point_core_eights
  let A := E.val ⊔ zpowers a
  let := hAe
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
  have heZ : e c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype := by
    have hh := center_transport u e c hcZ (pointCore_conjugate u ((m : G) * (g : G)))
    rwa [heu] at hh
  have hec4 : orderOf (e c) = 4 := (e.orderOf_eq c).trans hc4
  have hebc : e b * e c * (e b)⁻¹ = (e c)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg e hbc
  have hec2 : (e c) ^ 2 = z := by rw [← map_pow, hc2, heu]
  have hebH : e b ∈ involutionCentralizer z := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← heu, ← map_mul, ← map_mul]
    exact congrArg e (congrArg Subtype.val
      (mul_comm' (⟨b, hbA⟩ : A) ⟨u, huA⟩))
  have hnc : ¬ Commute (e b) (e c) := by
    intro hh
    have he : e c = (e c)⁻¹ := by
      simpa only [hh.eq, mul_inv_cancel_right] using hebc
    have hc : (e c) ^ 2 = 1 := by
      calc
        (e c) ^ 2 = e c * (e c)⁻¹ := by rw [pow_two]; exact congrArg (e c * ·) he
        _ = 1 := mul_inv_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hc
    rw [hec4] at hd
    norm_num at hd
  have heb2 : orderOf (e b) = 2 := orderOf_eq_prime (by rw [← map_pow, hb2, map_one])
    (fun he => hnc (he ▸ Commute.one_left _))
  have hect : Commute (e c) t := by
    have hh : Commute (e c) (e s) := hcs.map e.toMonoidHom
    rwa [hes] at hh
  have hebt : Commute (e b) t := by
    have hh : Commute (e b) (e s) := hbs.map e.toMonoidHom
    rwa [hes] at hh
  have hebQ : e b ∉ (involutionCentralizer z).pCoreIn 2 := by
    intro hbQ
    obtain ⟨cQ, hcQ, heq⟩ := heZ
    apply hnc
    rw [← heq]
    exact congrArg Subtype.val (mem_center_iff.mp hcQ ⟨e b, hbQ⟩)
  have hecQ : e c ∈ (involutionCentralizer z).pCoreIn 2 := by
    obtain ⟨cQ, _, heq⟩ := heZ
    exact heq ▸ cQ.property
  have hzQ : z ∈ (involutionCentralizer z).pCoreIn 2 := hec2 ▸ pow_mem hecQ 2
  have hebout : e b ∉ zpowers z := fun hb => hebQ (zpowers_le.mpr hzQ hb)
  let D := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.toMonoidHom
  have hzD : z ∈ D := ⟨u, huA, heu⟩
  have hebD : e b ∈ D := mem_map_of_mem e.toMonoidHom hbA
  have hDpure : ∀ x ∈ D, x ≠ 1 → IsConj x z := by
    rintro x ⟨y, hy, rfl⟩ hx1
    have hy1 : y ≠ 1 := fun he => hx1 (by rw [he, map_one])
    exact (isConj_iff.mpr ⟨(m : G) * (g : G), rfl⟩).symm.trans (hpure y hy hy1)
  let F := zpowers z ⊔ zpowers (e b)
  have hFD : F ≤ D := sup_le (zpowers_le.mpr hzD) (zpowers_le.mpr hebD)
  have hFE : IsElementaryAbelian 2 F := IsElementaryAbelian.of_injective
    (inclusion hFD) (inclusion_injective hFD)
  have hebN : e b ∈ normalizer (zpowers z : Set G) := by
    apply centralizer_le_normalizer
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((show Commute z (e b) from
      (mem_centralizer_singleton_iff.mp hebH).symm).zpow_left n).eq
  have hF4 : Nat.card F = 4 := by
    rw [show F = zpowers z ⊔ zpowers (e b) from rfl,
      card_sup_zpowers_of_normalizing_involution _ _
        (heb2 ▸ pow_orderOf_eq_one (e b)) hebout hebN,
      Nat.card_zpowers, h.involution]
  have hFC : F ≤ centralizer ({t} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp ht).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hebt.eq))
  exact ⟨F, hFE, hF4, hFC, mem_sup_left (mem_zpowers z),
    fun x hx hx1 => hDpure x (hFD hx) hx1,
    e c, e b, hec4, hec2, heZ, hect, heb2, mem_sup_right (mem_zpowers (e b)),
    hebout, hebc, rfl⟩

end CFSG.Quasithin.HigmanSims
