module

public import Theory.SpecificGroups.SymplecticFour.PRegularClasses.Charpoly
public import Theory.SpecificGroups.SymplecticFour.PRegularClasses.GLIntertwiner
public import Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Counting the odd-order conjugacy classes of the derived Sp₄ carrier

Choosing a representative of each actual odd-order conjugacy class and taking
the two free characteristic-polynomial coefficients gives a map to `F × F`.
In characteristic two, equal characteristic polynomials give a general-linear
intertwiner, and the form-correction theorem turns it into a conjugator in the
symplectic group. Thus the coefficient map is injective, giving at most `q²`
odd-order classes. When `q > 2`, the genuine derived-to-full group equivalence
transports the actual `ConjClasses.mk` image and preserves element orders.

Both conjugacy inputs allow repeated factors and the eigenvalue-one space.
The unconditional bounds require no representation-classification premise.
Source context: GLS III, 2.8.2, 2.8.6(a), Examples
2.8.10(d), `refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith,
`refs/quasithin.pdf`, proof of G.9.3, printed pp.356--357.
-/

namespace Theory.SpecificGroups.SymplecticFour.PRegularClasses

private theorem card_regular_le_of_separates
    {G I : Type*} [Group G] [Finite I] (p : ℕ) (f : G → I)
    (hf : ∀ g h : G, ¬ p ∣ orderOf g → ¬ p ∣ orderOf h → f g = f h → IsConj g h) :
    Nat.card (ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}) ≤ Nat.card I := by
  classical
  let P := ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}
  have hrep (c : P) : ∃ g : G, ¬ p ∣ orderOf g ∧ ConjClasses.mk g = c.val := c.property
  let r : P → G := fun c => (hrep c).choose
  have hrp (c : P) : ¬ p ∣ orderOf (r c) := (hrep c).choose_spec.1
  have hrc (c : P) : ConjClasses.mk (r c) = c.val := (hrep c).choose_spec.2
  let code : P → I := fun c => f (r c)
  have hinj : Function.Injective code := by
    intro c d h
    apply Subtype.ext
    rw [← hrc c, ← hrc d]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hf (r c) (r d) (hrp c) (hrp d) h)
  exact Nat.card_le_card_of_injective code hinj

private noncomputable def pRegularClassEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (p : ℕ) :
    (ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}) ≃
      (ConjClasses.mk '' {h : H | ¬ p ∣ orderOf h}) where
  toFun c := ⟨ConjClasses.map e.toMonoidHom c.val, by
    obtain ⟨g, hg, hc⟩ := c.property
    refine ⟨e g, by simpa only [Set.mem_ofPred_eq, e.orderOf_eq] using hg, ?_⟩
    rw [← hc]
    rfl⟩
  invFun c := ⟨ConjClasses.map e.symm.toMonoidHom c.val, by
    obtain ⟨h, hh, hc⟩ := c.property
    refine ⟨e.symm h, by simpa only [Set.mem_ofPred_eq, e.symm.orderOf_eq] using hh, ?_⟩
    rw [← hc]
    rfl⟩
  left_inv c := by
    apply Subtype.ext
    obtain ⟨g, hg, hc⟩ := c.property
    change ConjClasses.map e.symm.toMonoidHom (ConjClasses.map e.toMonoidHom c.val) = c.val
    rw [← hc]
    change ConjClasses.mk (e.symm (e g)) = ConjClasses.mk g
    rw [e.symm_apply_apply]
  right_inv c := by
    apply Subtype.ext
    obtain ⟨h, hh, hc⟩ := c.property
    change ConjClasses.map e.toMonoidHom (ConjClasses.map e.symm.toMonoidHom c.val) = c.val
    rw [← hc]
    change ConjClasses.mk (e (e.symm h)) = ConjClasses.mk h
    rw [e.apply_symm_apply]

variable {F : Type*} [Field F] [Finite F]

/-- The full-group bound follows from conjugacy inside the symplectic group,
with no characteristic-polynomial realization hypothesis. -/
public theorem card_pRegularConjClasses_le_of_charpoly_conjugacy
    (hconj : ∀ g h : Matrix.symplecticGroup (Fin 2) F,
      ¬ 2 ∣ orderOf g → ¬ 2 ∣ orderOf h →
      g.val.charpoly = h.val.charpoly → IsConj g h) :
    Nat.card (ConjClasses.mk ''
      {g : Matrix.symplecticGroup (Fin 2) F | ¬ 2 ∣ orderOf g}) ≤ (Nat.card F) ^ 2 := by
  have hb := card_regular_le_of_separates 2
    (fun g : Matrix.symplecticGroup (Fin 2) F =>
      (g.val.charpoly.coeff 3, g.val.charpoly.coeff 2)) (by
        intro g h hg hh he
        exact hconj g h hg hh (charpoly_eq_of_coefficients_eq g h
          (congrArg Prod.fst he) (congrArg Prod.snd he)))
  simpa only [Nat.card_prod, pow_two] using hb

/-- Inclusion identifies the actual odd-order class images of the derived
and full matrix groups when the field has more than two elements. -/
public theorem card_derived_pRegularConjClasses_eq_full [CharP F 2] (hq : 2 < Nat.card F) :
    Nat.card (ConjClasses.mk ''
      {g : commutator (Matrix.symplecticGroup (Fin 2) F) | ¬ 2 ∣ orderOf g}) =
    Nat.card (ConjClasses.mk ''
      {g : Matrix.symplecticGroup (Fin 2) F | ¬ 2 ∣ orderOf g}) :=
  Nat.card_congr (pRegularClassEquiv (derivedEquivFull_of_card_gt_two hq) 2)

/-- Conditional counting assembly on the literal derived matrix carrier.
The characteristic-polynomial conjugacy input is supplied explicitly. -/
public theorem card_derived_pRegularConjClasses_le_of_charpoly_conjugacy
    [CharP F 2] (hq : 2 < Nat.card F)
    (hconj : ∀ g h : Matrix.symplecticGroup (Fin 2) F,
      ¬ 2 ∣ orderOf g → ¬ 2 ∣ orderOf h →
      g.val.charpoly = h.val.charpoly → IsConj g h) :
    Nat.card (ConjClasses.mk ''
      {g : commutator (Matrix.symplecticGroup (Fin 2) F) | ¬ 2 ∣ orderOf g}) ≤
      (Nat.card F) ^ 2 := by
  rw [card_derived_pRegularConjClasses_eq_full hq]
  exact card_pRegularConjClasses_le_of_charpoly_conjugacy hconj

variable [CharP F 2]

/-- Odd-order elements with equal characteristic polynomials are conjugate
inside the actual symplectic group, including when polynomial factors repeat. -/
public theorem isConj_of_charpoly_eq (g h : Matrix.symplecticGroup (Fin 2) F)
    (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hpoly : g.val.charpoly = h.val.charpoly) : IsConj g h := by
  obtain ⟨D, hD, hinter⟩ := exists_unit_intertwiner_of_charpoly_eq g h hg hh hpoly
  exact isConj_of_unit_intertwiner g h hg hh D hD hinter

/-- The full symplectic four-space group has at most `q²` odd-order conjugacy
classes over a finite field of characteristic two. -/
public theorem card_pRegularConjClasses_le :
    Nat.card (ConjClasses.mk ''
      {g : Matrix.symplecticGroup (Fin 2) F | ¬ 2 ∣ orderOf g}) ≤ (Nat.card F) ^ 2 :=
  card_pRegularConjClasses_le_of_charpoly_conjugacy isConj_of_charpoly_eq

/-- The literal derived symplectic matrix group has at most `q²` odd-order
conjugacy classes when the characteristic-two field has more than two elements. -/
public theorem card_derived_pRegularConjClasses_le (hq : 2 < Nat.card F) :
    Nat.card (ConjClasses.mk ''
      {g : commutator (Matrix.symplecticGroup (Fin 2) F) | ¬ 2 ∣ orderOf g}) ≤
      (Nat.card F) ^ 2 := by
  rw [card_derived_pRegularConjClasses_eq_full hq]
  exact card_pRegularConjClasses_le

end Theory.SpecificGroups.SymplecticFour.PRegularClasses
