module

public import Theory.GroupTheory.Hall.TwoClosedNormal
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# Hall-normalizing actors in permutable products

A Sylow element factors through a normal two-closed overlap and the Hall
normalizer. Retaining the overlap factor preserves the induced outer action.
If A is contained in the Hall subgroup and AS = SA, each Sylow element
normalizing the Hall subgroup also normalizes A, by (AS) ∩ Y = A.

Source: Aschbacher–Smith, 4.4.13(1), printed pp.623–624.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]
/-- Retain the factor in the normal overlap in the two-closed Frattini argument. -/
theorem factor_through_overlap (B : Subgroup G) [B.Normal]
    (h : TwoClosedAbelianQuotient B)
    (S : Sylow 2 G) (Y : Subgroup G) (hYB : Y ≤ B)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf B)) (s : G) (hs : s ∈ S) :
    ∃ q ∈ B, ∃ t ∈ S, t ∈ normalizer (Y : Set G) ∧ q * t = s := by
  let Q := (pCore 2 B).map B.subtype
  have hNQ : normalizer (Q : Set G) = ⊤ := by
    apply top_unique
    rw [← normalizer_eq_top B]
    exact normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  let : Q.Normal := normalizer_eq_top_iff.mp hNQ
  have hQS : Q ≤ (S : Subgroup G) :=
    (pCore_isPGroup.map B.subtype).le_sylow_of_normal S
  let a : MulAut B := MulAut.conjNormal s
  have hcomp := OddHall.sylow_complement_of_hall
    ((pCore_isPGroup (p := 2) (G := B)).toSylow
      (Nat.not_even_iff_odd.mpr h.odd_index ∘ even_iff_two_dvd.mpr)) hHall
  obtain ⟨b, hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable h.solvable
    hHall (hHall.map_mulAut a)
  obtain ⟨⟨q, y⟩, hqy⟩ := hcomp.2 b
  have hmap : Y.map (MulAut.conj s).toMonoidHom =
      Y.map (MulAut.conj b.val).toMonoidHom := by
    have he := congrArg (Subgroup.map B.subtype) hb
    rw [map_map, map_map] at he
    have hleft : B.subtype.comp a.toMonoidHom =
        (MulAut.conj s).toMonoidHom.comp B.subtype := rfl
    have hright : B.subtype.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj b.val).toMonoidHom.comp B.subtype := rfl
    rw [hleft, hright, ← map_map, ← map_map,
      map_subgroupOf_eq_of_le hYB] at he
    exact he
  have hn : b.val⁻¹ * s ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change Y.map (MulAut.conj (b.val⁻¹ * s)).toMonoidHom = Y
    have he := congrArg (Subgroup.map (MulAut.conj b.val⁻¹).toMonoidHom) hmap
    simp only [map_map] at he
    have hleft : (MulAut.conj b.val⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (b.val⁻¹ * s)).toMonoidHom := by ext; simp [mul_assoc]
    have hright : (MulAut.conj b.val⁻¹).toMonoidHom.comp (MulAut.conj b.val).toMonoidHom =
        MonoidHom.id G := by ext; simp [mul_assoc]
    simpa only [hleft, hright, map_id] using he
  have hqn : q.val.val⁻¹ * s ∈ normalizer (Y : Set G) := by
    have he : b.val = q.val.val * y.val.val := congrArg Subtype.val hqy.symm
    have hn' := (normalizer (Y : Set G)).mul_mem (Y.le_normalizer y.property) hn
    change y.val.val * (b.val⁻¹ * s) ∈ normalizer (Y : Set G) at hn'
    have he' : y.val.val * (b.val⁻¹ * s) = q.val.val⁻¹ * s := by rw [he]; group
    rwa [he'] at hn'
  exact ⟨q.val.val, q.val.property, q.val.val⁻¹ * s,
    S.mul_mem (S.inv_mem (hQS ⟨q.val, q.property, rfl⟩)) hs, hqn,
    mul_inv_cancel_left _ _⟩
end Subgroup.OddHall
namespace Subgroup
variable {G : Type*} [Group G]
/-- Hall-normalizing elements of a permutable complement preserve its subgroup. -/
theorem normalizer_permutable_subgroup (A S Y : Subgroup G) (hAY : A ≤ Y)
    (hd : Disjoint S Y)
    (hperm : (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G)) :
    S ⊓ normalizer (Y : Set G) ≤ normalizer (A : Set G) := by
  have hi : (A ⊔ S) ⊓ Y = A := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (A : Set G) * (S : Set G) :=
        coe_sup_of_set_mul_comm A S hperm ▸ hx.1
      obtain ⟨a, ha, s, hs, rfl⟩ := hx'
      have hsY : s ∈ Y := by
        have hh := Y.mul_mem (Y.inv_mem (hAY ha)) hx.2
        simpa only [inv_mul_cancel_left] using hh
      have hs1 : s = 1 := mem_bot.mp (hd.eq_bot ▸ (show s ∈ S ⊓ Y from ⟨hs, hsY⟩))
      change a * s ∈ A
      rw [hs1, mul_one]
      exact ha
    · exact le_inf le_sup_left hAY
  rw [← hi]
  apply le_normalizer_iff.mpr
  intro t ht x hx
  refine ⟨?_, ?_⟩
  · exact (A ⊔ S).mul_mem ((A ⊔ S).mul_mem (mem_sup_right ht.1) hx.1)
      ((A ⊔ S).inv_mem (mem_sup_right ht.1))
  · exact (mem_normalizer_iff.mp ht.2 x).mp hx.2
end Subgroup
