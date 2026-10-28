module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Local
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Centralizers inside the J₁ local configuration

The concrete group `A₅ × C₂` has 31 involutions; the centralizer of any
involution outside its center has order eight. Transporting these finite
calculations through the source centralizer isomorphism determines the
common centralizer of `z` and a commuting involution outside `⟨z⟩`.
Choosing such an involution in the distinguished Sylow subgroup proves
that this Sylow subgroup is self-centralizing.

These are local inputs for the recognition theorem cited in I.4.9 and
the counting argument in Bender, *Finite groups with large subgroups* (1974), §4.
They do not require simplicity or assert the global recognition theorem.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

private abbrev A := alternatingGroup (Fin 5)
private abbrev M := A × Multiplicative (ZMod 2)

private theorem model_involution_count :
    Fintype.card {x : M // x ^ 2 = 1 ∧ x ≠ 1} = 31 := by
  decide +kernel

private theorem model_noncentral_involution_centralizer_card :
    ∀ x : M, x.1 ≠ 1 → x ^ 2 = 1 →
      Fintype.card {y : M // y * x = x * y} = 8 := by
  decide +kernel

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- There are exactly 31 involutions in the distinguished involution centralizer. -/
public theorem centralizer_involution_count : Nat.card {x : Subgroup.centralizer ({h.z} : Set G) // orderOf x = 2} = 31 := by
  let e := h.alternatingCentralizerEquiv
  let ei := e.toEquiv.subtypeEquiv (p := fun x => orderOf x = 2)
    (q := fun x => x ^ 2 = 1 ∧ x ≠ 1) (fun x => by
      rw [← orderOf_eq_prime_iff]
      exact iff_of_eq (congrArg (· = 2) (e.orderOf_eq x)).symm)
  rw [Nat.card_congr ei, Nat.card_eq_fintype_card]
  exact model_involution_count


/-- A commuting involution outside `⟨z⟩` has common centralizer of order eight with `z`. -/
public theorem common_centralizer_card (x : G)
    (hxC : x ∈ Subgroup.centralizer ({h.z} : Set G))
    (hx2 : x ^ 2 = 1) (hxz : x ∉ Subgroup.zpowers h.z) :
    Nat.card (Subgroup.centralizer ({h.z} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) : Subgroup G) = 8 := by
  let C := Subgroup.centralizer ({h.z} : Set G)
  let xC : C := ⟨x, hxC⟩
  let e := h.alternatingCentralizerEquiv
  have hfirst : (e xC).1 ≠ 1 := by
    intro heq
    have hecenter : e xC ∈ Subgroup.center M := by
      rw [Subgroup.center_prod]
      exact ⟨by simp [heq], by simp [Subgroup.center_eq_top]⟩
    have hxcenter : xC ∈ Subgroup.center C := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      apply e.injective
      simpa only [map_mul] using (Subgroup.mem_center_iff.mp hecenter) (e y)
    apply hxz
    rw [← h.center_image_eq_zpowers]
    exact Subgroup.mem_map_of_mem C.subtype hxcenter
  have hsquare : (e xC) ^ 2 = 1 := by
    rw [← map_pow, show xC ^ 2 = 1 from Subtype.ext hx2, map_one]
  let ec : Subgroup.centralizer ({xC} : Set C) ≃
      {y : M // y * e xC = e xC * y} :=
    e.toEquiv.subtypeEquiv (fun y => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      change y * xC = xC * y ↔ e y * e xC = e xC * e y
      rw [← map_mul, ← map_mul, e.injective.eq_iff])
  rw [← Subgroup.map_subtype_centralizer_singleton C xC,
    Subgroup.card_map_of_injective Subtype.val_injective,
    Nat.card_congr ec, Nat.card_eq_fintype_card]
  exact model_noncentral_involution_centralizer_card _ hfirst hsquare

/-- The distinguished Sylow two-subgroup is self-centralizing in the ambient group. -/
public theorem sylow_centralizer_eq :
    Subgroup.centralizer (h.sylow : Set G) = (h.sylow : Subgroup G) := by
  have hnot : ¬ (h.sylow : Subgroup G) ≤ Subgroup.zpowers h.z := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [h.sylow_card, Nat.card_zpowers, h.involution] at hc
    omega
  obtain ⟨x, hxS, hxz⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx2 : x ^ 2 = 1 :=
    congrArg Subtype.val (h.sylow_square ⟨x, hxS⟩)
  have hpair : (h.sylow : Subgroup G) =
      Subgroup.centralizer ({h.z} : Set G) ⊓
        Subgroup.centralizer ({x} : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge
    · refine le_inf h.sylow_le_centralizer ?_
      intro y hy
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (Commute.of_orderOf_dvd_two
        (fun a => orderOf_dvd_of_pow_eq_one (h.sylow_square a))
        (⟨y, hy⟩ : h.sylow) ⟨x, hxS⟩).eq
    · rw [h.common_centralizer_card x (h.sylow_le_centralizer hxS) hx2 hxz,
        h.sylow_card]
  apply le_antisymm
  · rw [hpair]
    exact le_inf
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.z_mem))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxS))
  · let := h.sylow_elementaryAbelian
    exact Subgroup.le_centralizer _

end CFSG.Quasithin.Janko1CentralizerData
