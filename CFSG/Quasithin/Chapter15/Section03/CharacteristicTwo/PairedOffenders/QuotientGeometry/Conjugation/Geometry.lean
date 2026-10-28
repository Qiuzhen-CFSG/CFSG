module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Positions
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Comparing the two four-group markings in D8

The elementary four-subgroups of D8 are the two reflection-parity subgroups.
They intersect in the center and cover the involutions. Transporting these
facts through an actual multiplicative equivalence excludes all simultaneous
source positions except regular/transposition, its reverse, and even/even.
An inner conjugation fixes every subgroup of order four, by its index two.

Source: Aschbacher–Smith, proof of 15.3.25, printed pp.1133–1134.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

variable {G H : Type*} [Group G] [Group H]

theorem map_center (e : G ≃* H) : (center G).map e.toMonoidHom = center H := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (mem_center_iff.mp hz w)
  · intro hx
    refine ⟨e.symm x, mem_center_iff.mpr ?_, e.apply_symm_apply x⟩
    intro y
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hx (e y)

theorem position_map {c : EightCase} {E A : Subgroup G}
    (h : Position c E A) (e : G ≃* H) :
    Position c (E.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  cases c with
  | regular =>
    refine ⟨(card_map_of_injective e.injective).trans h.1, ?_, ?_⟩
    · rw [← map_center e]
      exact disjoint_map e.injective h.2.1
    · rw [← map_center e, ← Subgroup.map_sup, h.2.2]
  | transposition =>
    exact ⟨(card_map_of_injective e.injective).trans h.1,
      fun hle => h.2 ((map_le_map_iff_of_injective e.injective).mp hle)⟩
  | disjoint =>
    let : IsElementaryAbelian 2 A := h.2.1
    exact ⟨(card_map_of_injective e.injective).trans h.1,
      IsElementaryAbelian.map e.toMonoidHom, fun he => h.2.2 (map_injective e.injective he)⟩
  | even =>
    change A = center G at h
    change A.map e.toMonoidHom = center H
    rw [h, map_center]

private def fourMem (i : Fin 2) : DihedralGroup 4 → Prop
  | .r a => a.val % 2 = 0
  | .sr a => a.val % 2 = i.val

private instance (i : Fin 2) (x : DihedralGroup 4) : Decidable (fourMem i x) := by
  cases x <;> unfold fourMem <;> infer_instance

private def four (i : Fin 2) : Subgroup (DihedralGroup 4) where
  carrier := {x | fourMem i x}
  one_mem' := by rfl
  mul_mem' := by
    intro x y hx hy
    exact (show ∀ i x y, fourMem i x → fourMem i y → fourMem i (x*y) by decide) i x y hx hy
  inv_mem' := by
    intro x hx
    exact (show ∀ i x, fourMem i x → fourMem i x⁻¹ by decide) i x hx

private instance (i : Fin 2) : DecidablePred (· ∈ four i) := fun x => inferInstanceAs (Decidable (fourMem i x))

private theorem card_four (i : Fin 2) : Nat.card (four i) = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact (show ∀ i, Fintype.card (four i) = 4 by decide) i

private theorem card_center_D8 : Nat.card (center (DihedralGroup 4)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem four_classify (E : Subgroup (DihedralGroup 4))
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) : E = four 0 ∨ E = four 1 := by
  have hn : ¬ E ≤ center (DihedralGroup 4) := by
    intro h
    have := card_le_of_le h
    rw [hE, card_center_D8] at this
    omega
  obtain ⟨x, hx, hxZ⟩ := SetLike.not_le_iff_exists.mp hn
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have ht : ∀ x : DihedralGroup 4, x ^ 2 = 1 →
      ¬ (∀ y, y*x=x*y) →
      (∀ y, y*x=x*y → fourMem 0 y) ∨ (∀ y, y*x=x*y → fourMem 1 y) := by decide
  have hle (i : Fin 2) (hi : ∀ y, y*x=x*y → fourMem i y) : E ≤ four i := by
    intro y hy
    exact hi y (setLike_mul_comm hy hx)
  rcases ht x hx2 (fun hh => hxZ (mem_center_iff.mpr hh)) with h | h
  · exact Or.inl (eq_of_le_of_card_ge (hle 0 h) (by rw [card_four, hE]))
  · exact Or.inr (eq_of_le_of_card_ge (hle 1 h) (by rw [card_four, hE]))

private theorem four_ne : four 0 ≠ four 1 := by
  intro h
  have : DihedralGroup.sr 0 ∈ four 1 := h ▸ (show DihedralGroup.sr 0 ∈ four 0 by decide)
  exact (by decide : DihedralGroup.sr 0 ∉ four 1) this

private theorem four_inf : four 0 ⊓ four 1 = center (DihedralGroup 4) := by
  ext x
  rw [mem_center_iff]
  exact (show ∀ x : DihedralGroup 4, (fourMem 0 x ∧ fourMem 1 x) ↔ (∀ y, y*x=x*y) by decide) x

/-- In D8 the two elementary four-groups meet in the center, exhaust the
four-groups, and cover every element whose square is one. -/
theorem dihedral_four_geometry (e : G ≃* DihedralGroup 4)
    (E F : Subgroup G) [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    E ⊓ F = center G ∧
    (∀ K : Subgroup G, IsElementaryAbelian 2 K → Nat.card K = 4 → K = E ∨ K = F) ∧
    (∀ x : G, x ^ 2 = 1 → x ∈ E ∨ x ∈ F) := by
  let E' := E.map e.toMonoidHom
  let F' := F.map e.toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map e.toMonoidHom
  let : IsElementaryAbelian 2 F' := IsElementaryAbelian.map e.toMonoidHom
  have hE' : Nat.card E' = 4 := (card_map_of_injective e.injective).trans hE
  have hF' : Nat.card F' = 4 := (card_map_of_injective e.injective).trans hF
  have hn : E' ≠ F' := fun h => hne (map_injective e.injective h)
  have hi : E' ⊓ F' = center (DihedralGroup 4) := by
    rcases four_classify E' hE' with h | h <;>
      rcases four_classify F' hF' with k | k <;> rw [h, k] at hn ⊢
    · exact (hn rfl).elim
    · exact four_inf
    · rw [inf_comm]; exact four_inf
    · exact (hn rfl).elim
  have hc : ∀ K : Subgroup G, IsElementaryAbelian 2 K → Nat.card K = 4 → K = E ∨ K = F := by
    intro K hK hk
    let := hK
    let K' := K.map e.toMonoidHom
    let : IsElementaryAbelian 2 K' := IsElementaryAbelian.map e.toMonoidHom
    have hk' : Nat.card K' = 4 := (card_map_of_injective e.injective).trans hk
    have : K' = E' ∨ K' = F' := by
      rcases four_classify E' hE' with h | h <;>
        rcases four_classify F' hF' with k | k <;>
        rcases four_classify K' hk' with l | l <;> simp_all
    exact this.imp (fun h => map_injective e.injective h) (fun h => map_injective e.injective h)
  refine ⟨?_, hc, ?_⟩
  · apply map_injective (f := e.toMonoidHom) e.injective
    rwa [map_inf _ _ _ e.injective, map_center]
  · intro x hx
    have ht : ∀ x : DihedralGroup 4, x ^ 2 = 1 → fourMem 0 x ∨ fourMem 1 x := by decide
    have ht' := ht (e x) (by rw [← map_pow, hx, map_one])
    have : e x ∈ E' ∨ e x ∈ F' := by
      rcases four_classify E' hE' with h | h <;>
        rcases four_classify F' hF' with k | k <;> rw [h, k] at hn ⊢
      · exact (hn rfl).elim
      · exact ht'
      · exact ht'.symm
      · exact (hn rfl).elim
    simpa only [E', F', mem_map_equiv, e.symm_apply_apply] using this

/-- Every four-subgroup of D8 is normal, so an inner conjugation fixes it. -/
theorem dihedral_four_conj (e : G ≃* DihedralGroup 4)
    (E : Subgroup G) (hE : Nat.card E = 4) (x : G) :
    E.map (MulAut.conj x).toMonoidHom = E := by
  have hc : Nat.card G = 8 := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hi := E.card_mul_index
  rw [hc, hE] at hi
  let : E.Normal := normal_of_index_eq_two (by omega)
  exact Subgroup.Normal.map_conj_eq E x

/-- A common offender image with two different four-group markings has exactly
one of the pairings used on printed p.1134. -/
theorem positions_of_distinct_four (e : G ≃* DihedralGroup 4)
    {E F A : Subgroup G} [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F)
    {c d : EightCase} (hc : Position c E A) (hd : Position d F A) :
    (c = .regular ∧ d = .transposition) ∨
    (c = .transposition ∧ d = .regular) ∨ (c = .even ∧ d = .even) := by
  let : Finite G := Finite.of_equiv _ e.toEquiv.symm
  obtain ⟨hinf, hfour, hinv⟩ := dihedral_four_geometry e E F hE hF hne
  have hZ : Nat.card (center G) = 2 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans card_center_D8
  have hZE : center G ≤ E := hinf ▸ inf_le_left
  have hZF : center G ≤ F := hinf ▸ inf_le_right
  have hcard := hc.card hZ
  have hcard' := hd.card hZ
  have hr {B : Subgroup G} (h : Position .regular B A) : A ≠ center G := by
    intro he
    have hb : A = ⊥ := disjoint_self.mp (he ▸ h.2.1)
    have := h.1
    rw [hb, card_bot] at this
    omega
  have htt (h : Nat.card A = 2) : A ≤ E ∨ A ≤ F := by
    apply SubgroupClass.subset_union.mp
    intro x hx
    apply hinv x
    have hp := pow_card_eq_one' (x := (⟨x, hx⟩ : A))
    rw [h] at hp
    exact congrArg Subtype.val hp
  cases c <;> cases d <;> simp only [quotientRank, pow_one, Nat.reducePow] at hcard hcard'
  all_goals try omega
  all_goals try simp only [true_and, or_true, true_or, and_self, and_true]
  all_goals simp only [Position] at hc hd
  · have hAZ : A ≤ center G := hinf ▸ le_inf (hc.2.2 ▸ le_sup_left) (hd.2.2 ▸ le_sup_left)
    have hb : A = ⊥ := (disjoint_iff.mp hc.2.1) ▸ inf_eq_left.mpr hAZ |>.symm
    have := hc.1
    rw [hb, card_bot] at this
    omega
  · exact (hr hc hd).elim
  · exact (htt hc.1).elim (fun h => (hc.2 h).elim) (fun h => (hd.2 h).elim)
  · exact (hc.2 (hd ▸ hZE)).elim
  · exact (hfour A hc.2.1 hc.1).elim (fun h => (hc.2.2 h).elim) (fun h => (hd.2.2 h).elim)
  · exact (hr hd hc).elim
  · exact (hd.2 (hc ▸ hZF)).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

end
