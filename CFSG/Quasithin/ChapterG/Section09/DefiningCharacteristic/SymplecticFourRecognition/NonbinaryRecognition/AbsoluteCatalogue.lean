module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily
public import Theory.Representation.PRegularSimpleCount
public import Theory.SpecificGroups.SymplecticFour.PRegularClasses

/-!
# Absolute classification by the concrete symplectic tensor family

There are q² subsets of the 2n graph-twist positions when q = 2ⁿ. If their
actual tensor representations are irreducible and pairwise inequivalent,
and the derived symplectic group has at most q² odd-order conjugacy classes,
then every irreducible representation is equivalent to one of these tensors.
Indeed, an omitted irreducible would give q² + 1 inequivalent simples,
contradicting the modular simple-family bound. A coordinate basis gives the
same conclusion for representation spaces in an arbitrary universe.

For n ≥ 2, `TensorFamily` proves irreducibility and inequivalence for every
subset of the natural and exceptional graph factors, including the empty
subset. `PRegularClasses` proves the bound for the literal derived matrix
group using symplectic conjugacy of odd-order elements. The final assembly
discharges all three premises and proves `AbsoluteTensorCatalogue`, with
genuine representation equivalences throughout.

Sources: GLS3, 2.8.2, 2.8.6(a), Examples 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, G.9.3 proof,
printed pp.356--357 of `refs/quasithin.pdf`. The finite-family argument follows
the independently proved SL₂ exhaustion in
`Theory.Representation.SL2.SteinbergParameters`.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

open Representation

universe u v

/-- The tensor parameter set has the source cardinality q². -/
theorem tensor_parameter_card {F : Type*} {n : ℕ} (hF : Nat.card F = 2^n) :
    Nat.card (Finset (Fin (2*n))) = Nat.card F ^ 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin, hF,
    ← pow_mul, Nat.mul_comm n 2]

variable {F : Type u} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {E : Type v} [Field E] [IsAlgClosed E] {n : ℕ}

private theorem exists_tensorModel_equiv_sameUniverse (e : F →+* E)
    (hirr : ∀ S : Finset (Fin (2*n)), IsIrreducible (tensorModel e S))
    (hdist : ∀ S T : Finset (Fin (2*n)),
      Nonempty ((tensorModel e S).Equiv (tensorModel e T)) → S = T)
    (hbound : Nat.card (ConjClasses.mk '' {g : Derived F | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (Finset (Fin (2*n))))
    (W : Type v) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (ρ : Representation E (Derived F) W) (hρ : IsIrreducible ρ) :
    ∃ S : Finset (Fin (2*n)), Nonempty (ρ.Equiv (tensorModel e S)) := by
  classical
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : CharP E 2 := charP_of_injective_ringHom e.injective 2
  by_contra! hnone
  let M : Option (Finset (Fin (2*n))) → Type v := fun i =>
    match i with
    | none => W
    | some S => (S → Coordinate) → E
  let addM : ∀ i, AddCommGroup (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module E (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation E (Derived F) (M i) := fun i =>
    match i with
    | none => ρ
    | some S => tensorModel e S
  have finM : ∀ i, FiniteDimensional E (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact hρ
    | some S => exact hirr S
  have hne : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro φ
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some S => exact (hnone S).false φ
    | some S =>
      cases j with
      | none => exact (hnone S).false φ.symm
      | some T => exact hij (congrArg some (hdist S T ⟨φ⟩))
  have hc := Representation.irreducible_family_card_le_pRegularConjClasses M rep 2 hne
  have hh := hc.trans hbound
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hh
  omega

/-- Saturating the modular simple-family bound gives a genuine intertwining
equivalence for every irreducible, including carriers in larger universes. -/
theorem exists_tensorModel_equiv_of_pRegular_bound (e : F →+* E)
    (hF : Nat.card F = 2^n)
    (hirr : ∀ S : Finset (Fin (2*n)), IsIrreducible (tensorModel e S))
    (hdist : ∀ S T : Finset (Fin (2*n)),
      Nonempty ((tensorModel e S).Equiv (tensorModel e T)) → S = T)
    (hbound : Nat.card (ConjClasses.mk '' {g : Derived F | ¬ 2 ∣ orderOf g}) ≤
      Nat.card F ^ 2)
    {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (ρ : Representation E (Derived F) W) (hρ : IsIrreducible ρ) :
    ∃ S : Finset (Fin (2*n)), Nonempty (ρ.Equiv (tensorModel e S)) := by
  classical
  let b := (Module.finBasis E W).equivFun
  let σ : Representation E (Derived F) (Fin (Module.finrank E W) → E) :=
    b.conjRingEquiv.toMonoidHom.comp ρ
  let φ : ρ.Equiv σ := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [σ, LinearEquiv.conjRingEquiv])
  have hirrσ : IsIrreducible σ := by
    let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap
    have hf : Function.Bijective f := φ.toLinearEquiv.bijective
    let ef := LinearEquiv.ofBijective f hf
    rw [irreducible_iff_isSimpleModule_asModule]
    exact ef.isSimpleModule_iff.mp ((irreducible_iff_isSimpleModule_asModule ρ).mp hρ)
  obtain ⟨S, ⟨ψ⟩⟩ := exists_tensorModel_equiv_sameUniverse e hirr hdist
    (by simpa only [tensor_parameter_card hF] using hbound) _ σ hirrσ
  exact ⟨S, ⟨φ.trans ψ⟩⟩

/-- Conditional catalogue assembly: exhaustion is proved from a numerical class
bound, while concrete simplicity and inequivalence are still required. -/
theorem absoluteTensorCatalogue_of_pRegular_bound (e : F →+* E)
    (hF : Nat.card F = 2^n)
    (hirr : ∀ S : Finset (Fin (2*n)), IsIrreducible (tensorModel e S))
    (hdist : ∀ S T : Finset (Fin (2*n)),
      Nonempty ((tensorModel e S).Equiv (tensorModel e T)) → S = T)
    (hbound : Nat.card (ConjClasses.mk '' {g : Derived F | ¬ 2 ∣ orderOf g}) ≤
      Nat.card F ^ 2) : AbsoluteTensorCatalogue F E e n where
  irreducible := hirr
  distinguish := hdist
  exhaustive _ _ _ _ ρ hρ :=
    exists_tensorModel_equiv_of_pRegular_bound e hF hirr hdist hbound ρ hρ

/-- Every finite-dimensional irreducible over an algebraically closed coefficient
field is genuinely equivalent to a concrete symplectic tensor. The module carrier
may lie in an arbitrary universe. -/
theorem exists_tensorModel_equiv (e : F →+* E)
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n)
    {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (ρ : Representation E (Derived F) W) (hρ : IsIrreducible ρ) :
    ∃ S : Finset (Fin (2*n)), Nonempty (ρ.Equiv (tensorModel e S)) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hq : 2 < Nat.card F := by
    rw [hF]
    calc
      2 < 2^2 := by decide
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  exact exists_tensorModel_equiv_of_pRegular_bound e hF
    (tensorModel_irreducible e hF hn) (tensorModel_equiv_imp_eq e hF hn)
    (Theory.SpecificGroups.SymplecticFour.PRegularClasses.card_derived_pRegularConjClasses_le hq)
    ρ hρ

/-- The absolute tensor classification for the actual derived Sp₄(F) group,
with both four-dimensional basic factors and no representation-theoretic premises. -/
theorem absoluteTensorCatalogue (e : F →+* E)
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n) : AbsoluteTensorCatalogue F E e n where
  irreducible := tensorModel_irreducible e hF hn
  distinguish := tensorModel_equiv_imp_eq e hF hn
  exhaustive _ _ _ _ ρ hρ := exists_tensorModel_equiv e hF hn ρ hρ

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
