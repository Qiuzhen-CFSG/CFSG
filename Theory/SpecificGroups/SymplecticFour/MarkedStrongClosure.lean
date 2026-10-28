module

public import Theory.GroupTheory.MarkedInnerStrongClosure.ReturningProducts
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus

/-!
# Two-stage returning conjugates in even symplectic four-space

Only the original central Sylow marker is normalized. Its two root
coordinates reduce it to a long root, a short root or their mixed product.
The mixed product has a noncommuting returning pair. Each root marker has
two commuting returning conjugates whose product lies in that mixed class.
All conjugacies are explicit root words; no global involution classification
is used.

Source: Aschbacher--Smith 1.1.5(3)(a), printed pp.501--503, and the component
inspection in Proposition 2.2.2, pp.519--520 (1 March 2004 manuscript).
-/

public section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
open Theory.GroupTheory.MarkedInnerStrongClosure
namespace Theory.SpecificGroups.SymplecticFour.MarkedStrongClosure
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2]

private def r (i : Fin 8) : Sp F := rootElement i 1

private theorem r_square (i : Fin 8) : (r (F := F) i) ^ 2 = 1 := by
  rw [r, pow_two, RootSubgroup.element_add, CharTwo.add_self_eq_zero,
    RootSubgroup.element_zero]

private theorem r_inv (i : Fin 8) : (r (F := F) i)⁻¹ = r i :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using r_square (F := F) i)

/-- These are right-conjugation identities, matching the strong-closure convention. -/
private theorem root_identities :
    (r (F := F) 6 * r 7 * r 6)⁻¹ * r 0 * (r 6 * r 7 * r 6) = r 2 ∧
    (r (F := F) 2 * r 3 * r 2)⁻¹ * r 4 * (r 2 * r 3 * r 2) = r 6 ∧
    (r (F := F) 7)⁻¹ * (r 0 * r 4) * r 7 = r 0 * r 2 ∧
    (r (F := F) 6 * r 3)⁻¹ * (r 0 * r 4) * (r 6 * r 3) = r 4 * r 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [_root_.mul_assoc]
    apply inv_mul_eq_iff_eq_mul.mpr
    apply Subtype.ext
    simp [r, rootElement, rootMatrix, Matrix.fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single,
        CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem root_products_noncommute :
    ¬Commute (r (F := F) 0 * r 2) (r 4 * r 6) := by
  intro hc
  have he := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 1)) hc.eq
  simp [r, rootElement, rootMatrix, Matrix.fromBlocks_multiply,
    Matrix.mul_apply, Matrix.single, CharTwo.add_self_eq_zero] at he

private theorem canonical_obstructions :
    ReturningProductObstruction (unipotent (F := F)) (r 0) ∧
    ReturningProductObstruction (unipotent (F := F)) (r 4) ∧
    ReturningProductObstruction (unipotent (F := F)) (r 0 * r 4) := by
  let a : unipotent (F := F) := ⟨r 0, positive_root_mem_unipotent 0 1 (by simp)⟩
  let b : unipotent (F := F) := ⟨r 2, positive_root_mem_unipotent 2 1 (by simp)⟩
  let c : unipotent (F := F) := ⟨r 4, positive_root_mem_unipotent 4 1 (by simp)⟩
  let d : unipotent (F := F) := ⟨r 6, positive_root_mem_unipotent 6 1 (by simp)⟩
  let x := a * b
  let y := c * d
  obtain ⟨hB, hA, hmB, hmA⟩ := root_identities (F := F)
  have hB' : IsConj (r (F := F) 0) (r 2) :=
    isConj_iff.mpr ⟨(r 6 * r 7 * r 6)⁻¹, by simpa only [inv_inv] using hB⟩
  have hA' : IsConj (r (F := F) 4) (r 6) :=
    isConj_iff.mpr ⟨(r 2 * r 3 * r 2)⁻¹, by simpa only [inv_inv] using hA⟩
  have hmB' : IsConj (r (F := F) 0 * r 4) (r 0 * r 2) :=
    isConj_iff.mpr ⟨(r 7)⁻¹, by simpa only [inv_inv] using hmB⟩
  have hmA' : IsConj (r (F := F) 0 * r 4) (r 4 * r 6) :=
    isConj_iff.mpr ⟨(r 6 * r 3)⁻¹, by simpa only [inv_inv] using hmA⟩
  have hxy : ¬Commute x y := fun h =>
    root_products_noncommute (h.map (unipotent (F := F)).subtype)
  refine ⟨Or.inr ⟨a, b, x, y, IsConj.refl _, hB', ?_, ?_, hxy⟩,
    Or.inr ⟨c, d, x, y, IsConj.refl _, hA', ?_, ?_, hxy⟩,
    Or.inl ⟨x, y, hmB', hmA', hxy⟩⟩
  · change IsConj (r 0 * (r (F := F) 2)⁻¹) (r 0 * r 2)
    rw [r_inv]
    exact IsConj.refl _
  · change IsConj (r 0 * (r (F := F) 2)⁻¹) (r 4 * r 6)
    rw [r_inv]
    exact hmB'.symm.trans hmA'
  · change IsConj (r 4 * (r (F := F) 6)⁻¹) (r 0 * r 2)
    rw [r_inv]
    exact hmA'.symm.trans hmB'
  · change IsConj (r 4 * (r (F := F) 6)⁻¹) (r 4 * r 6)
    rw [r_inv]
    exact IsConj.refl _

variable [Finite F]

private theorem scale_isConj (s t : F) (c d : Fˣ) :
    IsConj (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t))
      (parameter (Multiplicative.ofAdd ((c : F) * s),
        Multiplicative.ofAdd ((d : F) * t))) := by
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) (c : F)
  have ha0 : a ≠ 0 := by
    intro he
    exact c.ne_zero (by simpa only [he, zero_pow (by decide : 2 ≠ 0)] using ha.symm)
  let au : Fˣ := Units.mk0 a ha0
  let bu : Fˣ := d / au
  have hw : (au : F) * (bu : F) = d := by
    simp only [bu, Units.val_div_eq_div_val]
    exact mul_div_cancel₀ _ au.ne_zero
  apply isConj_iff.mpr
  refine ⟨diagonalTorusHom (au, bu), ?_⟩
  simpa only [show (au : F)^2 = (c : F) from ha, hw] using
    diagonalTorus_weights (au, bu) s t

private theorem theta_obstruction (s t : F)
    (hne : (theta s t : Sp F) ≠ 1) :
    ReturningProductObstruction (unipotent (F := F)) (theta s t : Sp F) := by
  obtain ⟨hB, hA, hm⟩ := canonical_obstructions (F := F)
  by_cases hs : s = 0
  · subst s
    have ht : t ≠ 0 := by
      intro he
      subst t
      exact hne (congrArg Subtype.val (element_zero (F := F)))
    apply hA.of_isConj
    have hc := scale_isConj (F := F) 0 t 1 (Units.mk0 t ht)⁻¹
    simpa [parameter_apply, theta_val, r, RootSubgroup.element_zero, ht] using hc
  · by_cases ht : t = 0
    · subst t
      apply hB.of_isConj
      have hc := scale_isConj (F := F) s 0 (Units.mk0 s hs)⁻¹ 1
      simpa [parameter_apply, theta_val, r, RootSubgroup.element_zero, hs] using hc
    · apply hm.of_isConj
      have hc := scale_isConj (F := F) s t (Units.mk0 s hs)⁻¹ (Units.mk0 t ht)⁻¹
      simpa [parameter_apply, theta_val, r, hs, ht] using hc

private theorem standard_central_obstruction (t : unipotent (F := F))
    (hc : t ∈ center (unipotent (F := F))) (hne : (t : Sp F) ≠ 1) :
    ReturningProductObstruction (unipotent (F := F)) (t : Sp F) := by
  obtain ⟨⟨b, u, w, v⟩, rfl⟩ := element_surjective t
  obtain ⟨rfl, rfl⟩ := (mem_center_iff_coordinates b u w v).mp hc
  exact theta_obstruction u w hne

/-- Every central involution of the supplied Sylow has either a direct
noncommuting returning pair or such a pair after one returning ratio. -/
theorem sylow_returning_product_obstruction {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (P : Sylow 2 (Sp F)) (t : Sp F) (ht : t ∈ P) (ho : orderOf t = 2)
    (hc : ∀ x ∈ P, Commute t x) : ReturningProductObstruction (P : Subgroup (Sp F)) t := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) (unipotentSylow hF hn) P
  let e := MulAut.conj g
  have hmap : unipotent.map e.toMonoidHom = (P : Subgroup (Sp F)) :=
    congrArg Sylow.toSubgroup hg
  have ht0 : e.symm t ∈ unipotent (F := F) := by
    obtain ⟨x, hx, hxt⟩ := hmap.ge ht
    have he : e.symm t = x := by rw [← hxt]; exact e.symm_apply_apply x
    exact he.symm ▸ hx
  let t0 : unipotent (F := F) := ⟨e.symm t, ht0⟩
  have hc0 : t0 ∈ center (unipotent (F := F)) := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    apply e.injective
    change e ((x : Sp F) * e.symm t) = e (e.symm t * (x : Sp F))
    simp only [map_mul, e.apply_symm_apply]
    exact (hc (e (x : Sp F)) (hmap.le (mem_map_of_mem e.toMonoidHom x.property))).symm.eq
  have hne0 : (t0 : Sp F) ≠ 1 := by
    intro he
    change e.symm t = 1 at he
    have ht1 : t = 1 := by simpa only [map_one, e.apply_symm_apply] using congrArg e he
    simp only [ht1, orderOf_one] at ho
    contradiction
  have hh := (standard_central_obstruction t0 hc0 hne0).map e
  change ReturningProductObstruction (unipotent.map e.toMonoidHom) (e (e.symm t)) at hh
  simpa only [hmap, e.apply_symm_apply] using hh

end Theory.SpecificGroups.SymplecticFour.MarkedStrongClosure
