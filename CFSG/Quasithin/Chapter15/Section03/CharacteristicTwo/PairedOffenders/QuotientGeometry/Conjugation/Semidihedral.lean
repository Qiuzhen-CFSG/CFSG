module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Conjugation.Geometry
public import Theory.GroupTheory.SemidihedralStandardModel

/-!
# Outside conjugation in the standard SD16

The explicit semidirect product has a unique dihedral subgroup of order eight.
Indeed, all involutions lie in its even-rotation subgroup, and involutions
 generate D8. Its two elementary four-groups are given by the two even
 reflection classes; an odd rotation coordinate interchanges them.
The finite coordinate identities are kernel checked and transported through
 multiplicative equivalences and explicit conjugation diagrams.

Source: Aschbacher–Smith, proof of 15.3.25, printed pp.1133–1134;
 the standard semidihedral presentation is in `SemidihedralStandardModel`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

abbrev SD16 := Semidihedral.StandardModel 4 (by decide)
private instance : Fintype SD16 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

-- Computable coordinate operations derived from the public action equations.
private def sdAction (g : Multiplicative (ZMod 2)) (x : Multiplicative (ZMod 8)) :=
  if g = 1 then x else x ^ 3

private theorem sdAction_spec (g : Multiplicative (ZMod 2))
    (x : Multiplicative (ZMod 8)) : Semidihedral.standardAction 4 (by decide) g x = sdAction g x := by
  rcases (show ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = .ofAdd 1 by decide) g with rfl | rfl
  · simp [sdAction]
  · rw [Semidihedral.standardAction_generator, Semidihedral.standardTwist_apply]
    rfl

private def sdMul (x y : SD16) : SD16 :=
  ⟨x.left * sdAction x.right y.left, x.right * y.right⟩

private theorem sd_mul_eq (x y : SD16) : x * y = sdMul x y := by
  apply SemidirectProduct.ext
  · exact congrArg (x.left * ·) (sdAction_spec x.right y.left)
  · rfl

private def sdInv (x : SD16) : SD16 := ⟨sdAction x.right⁻¹ x.left⁻¹, x.right⁻¹⟩

private theorem sd_inv_eq (x : SD16) : x⁻¹ = sdInv x := by
  apply SemidirectProduct.ext
  · exact sdAction_spec x.right⁻¹ x.left⁻¹
  · rfl

private def sdDihedral : Subgroup SD16 where
  carrier := {x | x.left.toAdd.val % 2 = 0}
  one_mem' := by rfl
  mul_mem' := by
    intro x y hx hy
    exact (show ∀ x y : SD16, x.left.toAdd.val % 2 = 0 → y.left.toAdd.val % 2 = 0 →
      (x*y).left.toAdd.val % 2 = 0 by simp only [sd_mul_eq]; decide +kernel) x y hx hy
  inv_mem' := by
    intro x hx
    exact (show ∀ x : SD16, x.left.toAdd.val % 2 = 0 → x⁻¹.left.toAdd.val % 2 = 0 by simp only [sd_inv_eq]; decide +kernel) x hx

private instance : DecidablePred (· ∈ sdDihedral) := fun x =>
  inferInstanceAs (Decidable (x.left.toAdd.val % 2 = 0))

private def sdFourMem (i : Fin 2) (x : SD16) : Prop :=
  x.left.toAdd.val % 4 = 2 * i.val * x.right.toAdd.val

private instance (i : Fin 2) (x : SD16) : Decidable (sdFourMem i x) :=
  inferInstanceAs (Decidable (_ = _))

private def sdFour (i : Fin 2) : Subgroup SD16 where
  carrier := {x | sdFourMem i x}
  one_mem' := by simp [sdFourMem]
  mul_mem' := by
    intro x y hx hy
    exact (show ∀ i x y, sdFourMem i x → sdFourMem i y → sdFourMem i (x*y) by simp only [sd_mul_eq]; decide +kernel) i x y hx hy
  inv_mem' := by
    intro x hx
    exact (show ∀ i x, sdFourMem i x → sdFourMem i x⁻¹ by simp only [sd_inv_eq]; decide +kernel) i x hx

private instance (i : Fin 2) : DecidablePred (· ∈ sdFour i) := fun x =>
  inferInstanceAs (Decidable (sdFourMem i x))

private theorem card_sdFour (i : Fin 2) : Nat.card (sdFour i) = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact (show ∀ i, Fintype.card (sdFour i) = 4 by decide +kernel) i

private theorem card_sdDihedral : Nat.card sdDihedral = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem involutions_mem_sdDihedral (x : SD16) (hx : x ^ 2 = 1) : x ∈ sdDihedral :=
  (show ∀ x : SD16, x ^ 2 = 1 → x.left.toAdd.val % 2 = 0 by simp only [pow_two, sd_mul_eq]; decide +kernel) x hx

private theorem sd_dihedral_unique (S : Subgroup SD16) (e : S ≃* DihedralGroup 4) :
    S = sdDihedral := by
  have hle : S ≤ sdDihedral := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (show ∀ x : DihedralGroup 4, ∃ a b, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a*b=x by decide) (e ⟨x,hx⟩)
    have hpow (y : DihedralGroup 4) (hy : y ^ 2 = 1) : ((e.symm y : S) : SD16) ^ 2 = 1 := by
      have hh : (e.symm y) ^ 2 = 1 := by rw [← map_pow, hy, map_one]
      exact congrArg Subtype.val hh
    have hp : ((e.symm a : S) : SD16) * ((e.symm b : S) : SD16) = x := by
      change ((e.symm a * e.symm b : S) : SD16) = x
      rw [← map_mul, hab, e.symm_apply_apply]
    rw [← hp]
    exact sdDihedral.mul_mem (involutions_mem_sdDihedral _ (hpow a ha))
      (involutions_mem_sdDihedral _ (hpow b hb))
  apply eq_of_le_of_card_ge hle
  rw [card_sdDihedral, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

private def sdAxis : Subgroup SD16 := sdFour 0 ⊓ sdFour 1

private instance : DecidablePred (· ∈ sdAxis) := fun x =>
  inferInstanceAs (Decidable (x ∈ sdFour 0 ∧ x ∈ sdFour 1))

private theorem card_sdAxis : Nat.card sdAxis = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem sd_four_classify (E : Subgroup SD16) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : E = sdFour 0 ∨ E = sdFour 1 := by
  have hn : ¬ E ≤ sdAxis := by
    intro h
    have := card_le_of_le h
    rw [hE, card_sdAxis] at this
    omega
  obtain ⟨x, hx, hxZ⟩ := SetLike.not_le_iff_exists.mp hn
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have ht : ∀ x : SD16, x ^ 2 = 1 → ¬ (sdFourMem 0 x ∧ sdFourMem 1 x) →
      (∀ y, y*x=x*y → sdFourMem 0 y) ∨ (∀ y, y*x=x*y → sdFourMem 1 y) := by simp only [pow_two, sd_mul_eq]; decide +kernel
  have hle (i : Fin 2) (hi : ∀ y, y*x=x*y → sdFourMem i y) : E ≤ sdFour i := by
    intro y hy
    exact hi y (setLike_mul_comm hy hx)
  rcases ht x hx2 hxZ with h | h
  · exact Or.inl (eq_of_le_of_card_ge (hle 0 h) (by rw [card_sdFour, hE]))
  · exact Or.inr (eq_of_le_of_card_ge (hle 1 h) (by rw [card_sdFour, hE]))

private theorem sd_four_ne : sdFour 0 ≠ sdFour 1 := by
  intro h
  let x : SD16 := ⟨.ofAdd 0, .ofAdd 1⟩
  have : x ∈ sdFour 1 := h ▸ (show x ∈ sdFour 0 by decide +kernel)
  exact (by decide +kernel : x ∉ sdFour 1) this

private theorem sd_four_conj (t : SD16) (ht : t ∉ sdDihedral) (i : Fin 2) :
    (sdFour i).map (MulAut.conj t).toMonoidHom = sdFour (1-i) := by
  have hle : (sdFour i).map (MulAut.conj t).toMonoidHom ≤ sdFour (1-i) := by
    rintro y ⟨x, hx, rfl⟩
    exact (show ∀ t : SD16, t.left.toAdd.val % 2 ≠ 0 → ∀ i x,
      sdFourMem i x → sdFourMem (1-i) (t*x*t⁻¹) by simp only [sd_mul_eq, sd_inv_eq]; decide +kernel) t ht i x hx
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj t).injective,
    card_sdFour, card_sdFour])

/-- In the standard SD16, conjugation outside any D8 subgroup exchanges its
 two elementary four-subgroups. No interchange hypothesis is supplied. -/
theorem standard_semidihedral_interchange (S E : Subgroup SD16)
    (e : S ≃* DihedralGroup 4) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (t : SD16) (ht : t ∉ S) :
    E ≤ S ∧ E.map (MulAut.conj t).toMonoidHom ≤ S ∧
      E.map (MulAut.conj t).toMonoidHom ≠ E := by
  rw [sd_dihedral_unique S e] at ht ⊢
  have hle : ∀ i, sdFour i ≤ sdDihedral := by
    intro i x hx
    exact (show ∀ i x, sdFourMem i x → x.left.toAdd.val % 2 = 0 by decide +kernel) i x hx
  rcases sd_four_classify E hE with rfl | rfl
  · rw [sd_four_conj t ht 0]
    exact ⟨hle 0, hle 1, Ne.symm sd_four_ne⟩
  · rw [sd_four_conj t ht 1]
    exact ⟨hle 1, hle 0, sd_four_ne⟩

variable {G H : Type*} [Group G] [Group H]

/-- Images commute with inner conjugation under any group homomorphism. -/
theorem map_conjugate (f : G →* H) (E : Subgroup G) (t : G) :
    (E.map (MulAut.conj t).toMonoidHom).map f =
      (E.map f).map (MulAut.conj (f t)).toMonoidHom := by
  rw [map_map, map_map]
  apply congrArg (fun h => E.map h)
  ext x
  simp [MulAut.conj_apply]

/-- The SD16 interchange transported through an actual model equivalence. -/
theorem semidihedral_interchange (v : G ≃* SD16) (S E : Subgroup G)
    (e : S ≃* DihedralGroup 4) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (t : G) (ht : t ∉ S) :
    E ≤ S ∧ E.map (MulAut.conj t).toMonoidHom ≤ S ∧
      E.map (MulAut.conj t).toMonoidHom ≠ E := by
  let E' := E.map v.toMonoidHom
  let S' := S.map v.toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map v.toMonoidHom
  have he : S' ≃* DihedralGroup 4 := (v.subgroupMap S).symm.trans e
  have ht' : v t ∉ S' := by simpa only [S', mem_map_equiv, v.symm_apply_apply] using ht
  obtain ⟨h1, h2, h3⟩ := standard_semidihedral_interchange S' E' he
    ((card_map_of_injective v.injective).trans hE) (v t) ht'
  change (E.map v.toMonoidHom).map (MulAut.conj (v.toMonoidHom t)).toMonoidHom ≤ S.map v.toMonoidHom at h2
  change (E.map v.toMonoidHom).map (MulAut.conj (v.toMonoidHom t)).toMonoidHom ≠ E.map v.toMonoidHom at h3
  rw [← map_conjugate] at h2 h3
  exact ⟨(map_le_map_iff_of_injective v.injective).mp h1,
    (map_le_map_iff_of_injective v.injective).mp h2,
    fun h => h3 (congrArg (Subgroup.map v.toMonoidHom) h)⟩

/-- An explicit conjugation diagram induces the nontrivial permutation of the
 two four-groups. The actor need only exist on the D8 group. -/
theorem marked_four_ne_of_semidihedral
    (u : G ≃* DihedralGroup 4) (v : H ≃* SD16)
    (j : G →* H) (hj : Function.Injective j) (t : H) (ht : t ∉ j.range)
    (α : MulAut G) (hα : ∀ x, j (α x) = t * j x * t⁻¹)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    E.map α.toMonoidHom ≠ E := by
  let : IsElementaryAbelian 2 (E.map j) := IsElementaryAbelian.map j
  have he : j.range ≃* DihedralGroup 4 := (MonoidHom.ofInjective hj).symm.trans u
  have hn := (semidihedral_interchange v j.range (E.map j) he
    ((card_map_of_injective hj).trans hE) t ht).2.2
  have hm : (E.map α.toMonoidHom).map j =
      (E.map j).map (MulAut.conj t).toMonoidHom := by
    rw [map_map, map_map]
    apply congrArg (fun h => E.map h)
    exact MonoidHom.ext hα
  intro h
  apply hn
  rw [← hm, h]

/-- The source pairings follow from an SD16 conjugation diagram and the two
 positions, without assuming either the interchange or a pairing alternative. -/
theorem positions_of_semidihedral_conjugation
    (u : G ≃* DihedralGroup 4) (v : H ≃* SD16)
    (j : G →* H) (hj : Function.Injective j) (t : H) (ht : t ∉ j.range)
    (α : MulAut G) (hα : ∀ x, j (α x) = t * j x * t⁻¹)
    {E A : Subgroup G} [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    {c d : EightCase} (hc : Position c E A)
    (hd : Position d (E.map α.toMonoidHom) A) :
    (c = .regular ∧ d = .transposition) ∨
    (c = .transposition ∧ d = .regular) ∨ (c = .even ∧ d = .even) := by
  let : IsElementaryAbelian 2 (E.map α.toMonoidHom) := IsElementaryAbelian.map α.toMonoidHom
  exact positions_of_distinct_four u hE ((card_map_of_injective α.injective).trans hE)
    (Ne.symm (marked_four_ne_of_semidihedral u v j hj t ht α hα E hE)) hc hd

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

end
