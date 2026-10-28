module
public import Theory.GroupTheory.SolvableSylowOvergroups.CubicSections
/-!
# Cubic control of odd actors on a normal section

Assume a normal centerless section has a two-group outer automorphism group,
and that odd subgroups of solvable full-Sylow overgroups containing a cubic
have order dividing three. If the given odd actor contains a cubic inside
the marked residual, its inner image equals that cubic image. Its remaining
kernel centralizes the section, so the whole actor normalizes the residual.
The HS and Rudvalis consumers prove the stated order bound with their actual
local quotient maps. Source: Aschbacher--Smith 5.1.13, printed pp.636--637.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- A marked cubic controls the entire odd actor under the full-Sylow order bound. -/
theorem odd_normalizes_of_cubic_sylow_overgroups
    (C R J E B : Subgroup G) [C.Normal] [Group.IsSolvable J]
    (hz : center C = ⊥) (houter : IsPGroup 2 (MulAut.Outer C))
    (hbound : ∀ (P : Sylow 2 C) (M N : Subgroup C), (P : Subgroup C) ≤ M →
      Group.IsSolvable M → 3 ∣ Nat.card M → N ≤ M → Odd (Nat.card N) → Nat.card N ∣ 3)
    (hRC : R ≤ C)
    (S : Sylow 2 G) (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J)
    (hBE : B ≤ E) (hBR : B ≤ R) (hB : Nat.card B = 3)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer (R : Set G) := by
  let f : G →* MulAut C := MulAut.conjNormal
  let i : C →* MulAut C := MulAut.conj
  have hi : Function.Injective i := conj_injective_of_center_eq_bot hz
  have hfi (x : C) : f x = i x := by ext y; rfl
  have hEin : E.map f ≤ i.range := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup C)
    have hod : Odd (Nat.card ((E.map f).map q)) :=
      hodd.of_dvd_nat ((card_map_dvd _ q).trans (card_map_dvd _ f))
    obtain ⟨k,hk⟩ := (houter.to_subgroup ((E.map f).map q)).exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      exact hod.not_two_dvd_nat (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hb : (E.map f).map q = ⊥ := card_eq_one.mp (by rw [hk,hk0,pow_zero])
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
  let M := (J.map f).comap i
  let N := (E.map f).comap i
  have hNmap : N.map i = E.map f := map_comap_eq_self hEin
  have hNc : Nat.card N = Nat.card (E.map f) := by
    rw [←hNmap,card_map_of_injective hi]
  have hNM : N ≤ M := comap_mono (map_mono hEJ)
  let : Group.IsSolvable (J.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap (J.map f)) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  have hPM : (P : Subgroup C) ≤ M := by
    intro x hx
    change i x ∈ J.map f
    rw [←hfi]
    have hx' : x ∈ (S : Subgroup G).subgroupOf C := hP ▸ hx
    exact mem_map_of_mem f (hSJ hx')
  have hfB : Function.Injective (f.comp B.subtype) := by
    intro x y hh
    have he (b : B) : f (b : G) = i (inclusion (hBR.trans hRC) b) :=
      hfi (inclusion (hBR.trans hRC) b)
    change f (x : G) = f (y : G) at hh
    rw [he x,he y] at hh
    exact inclusion_injective (hBR.trans hRC) (hi hh)
  have hBc : Nat.card (B.map f) = 3 := by
    rw [←range_subtype B,←MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hfB).toEquiv).symm.trans hB
  have h3M : 3 ∣ Nat.card M := by
    have hd := card_dvd_of_le (map_mono (f := f) hBE)
    rw [hBc,←hNc] at hd
    exact hd.trans (card_dvd_of_le hNM)
  have hsmall : Nat.card (E.map f) ≤ 3 := by
    have hoN : Odd (Nat.card N) := by rw [hNc]; exact hodd.of_dvd_nat (card_map_dvd _ f)
    have hd := hbound P M N hPM inferInstance h3M hNM hoN
    rw [hNc] at hd
    exact Nat.le_of_dvd (by decide) hd
  have he : B.map f = E.map f := eq_of_le_of_card_ge (map_mono hBE) (by rw [hBc]; exact hsmall)
  intro x hx
  obtain ⟨b,hb,hbx⟩ := mem_map.mp (he.symm ▸ mem_map_of_mem f hx)
  have hker : x * b⁻¹ ∈ f.ker := by
    change f (x * b⁻¹) = 1
    rw [map_mul,map_inv,hbx,mul_inv_cancel]
  have hc : x * b⁻¹ ∈ centralizer (C : Set G) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact hker
  have hn := (centralizer_le hRC).trans (centralizer_le_normalizer (R : Set G)) hc
  simpa only [inv_mul_cancel_right] using
    (normalizer (R : Set G)).mul_mem hn (R.le_normalizer (hBR hb))


end Theory.GroupTheory
