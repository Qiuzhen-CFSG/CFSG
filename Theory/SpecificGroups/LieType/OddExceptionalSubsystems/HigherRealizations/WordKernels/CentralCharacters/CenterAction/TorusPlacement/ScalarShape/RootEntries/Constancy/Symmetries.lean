module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.RootEntries.Transport
public import Theory.AlgebraicGroup.RootSystems.GeckDiagramEquivariance

/-!
# Root symmetries of the actual E6 word action

A root-pairing automorphism fixing one simple root preserves that root's
integral Geck operator. Reindex only the root coordinates and leave every
Cartan coordinate fixed: the mixed blocks are supported at the fixed root
and its opposite, and the root block is determined by root strings.
This proves invariance of every divided power and every evaluated word.
It does not require preservation of the entire ambient simple base.

In E8, reflection in the eighth simple root and in the lowest root gives two
explicit symmetries fixing all six E6 nodes. Their word-matrix identities
compare repeated constituents using actual word membership, with no
semisimplicity hypothesis and no exclusion of characteristic three.
`SubsystemRootOrbit` is the purely geometric reachability relation consumed
by the conditional residue assembly. Exhaustive coverage is a separate input.

Sources: GLS3 §§1.12.5–6 and 2.6.2, the common Chevalley lattice argument
used for Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section

noncomputable section
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape

section Generic
variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private theorem fixedRoot_eMatrix (d : P.Equiv P) (i : b.support)
    (hi : d.indexEquiv i = (i : ι)) :
    diagramMatrixEquiv d (Equiv.refl b.support) ℤ (eMatrix i) = eMatrix i := by
  let _ := P.indexNeg
  have hn : d.indexEquiv (-i) = -(i : ι) := by rw [diagram_neg, hi]
  have he (r : ι) : d.indexEquiv r = (i : ι) ↔ r = i := by
    simpa only [hi] using (d.indexEquiv.injective.eq_iff (a := r) (b := (i : ι)))
  have hen (r : ι) : d.indexEquiv r = -(i : ι) ↔ r = -(i : ι) := by
    simpa only [hn] using (d.indexEquiv.injective.eq_iff (a := r) (b := -(i : ι)))
  have ha (r s : ι) : P.root (d.indexEquiv r) =
      P.root i + P.root (d.indexEquiv s) ↔ P.root r = P.root i + P.root s := by
    simpa only [hi] using diagram_root_add_iff d r i s
  have hc (s : ι) : P.chainBotCoeff i (d.indexEquiv s) = P.chainBotCoeff i s := by
    simpa only [hi] using diagram_chainBotCoeff d i s
  apply (diagramMatrixEquiv_eq_iff d (Equiv.refl b.support) ℤ _ _).mpr
  rintro (r | r) (s | s) <;>
    simp [diagramIndexEquiv, eMatrix, he, hc]
  · change (if r = i ∧ s = -(i : ι) then 1 else 0) =
      (if r = i ∧ d.indexEquiv s = -(i : ι) then 1 else 0)
    simp only [hen]
  · rw [ha]

private theorem fixedRoot_eDividedPower (d : P.Equiv P) (i : b.support)
    (hi : d.indexEquiv i = (i : ι)) (n : ℕ) :
    diagramMatrixEquiv d (Equiv.refl b.support) ℤ (eDividedPower i n) =
      eDividedPower i n := by
  cases n with
  | zero => exact map_one _
  | succ n =>
    cases n with
    | zero => exact fixedRoot_eMatrix d i hi
    | succ n =>
      have ha (r s : ι) : P.root (d.indexEquiv r) =
          P.root (d.indexEquiv s) + (n + 2) • P.root i ↔
          P.root r = P.root s + (n + 2) • P.root i := by
        simpa only [hi] using diagram_root_add_nsmul_iff d r s i (n + 2)
      have hc (s : ι) : P.chainBotCoeff i (d.indexEquiv s) = P.chainBotCoeff i s := by
        simpa only [hi] using diagram_chainBotCoeff d i s
      apply (diagramMatrixEquiv_eq_iff d (Equiv.refl b.support) ℤ _ _).mpr
      rintro (r | r) (s | s) <;>
        simp [diagramIndexEquiv, eDividedPower, hc]
      rw [ha]

private theorem fixedRoot_fDividedPower (d : P.Equiv P) (i : b.support)
    (hi : d.indexEquiv i = (i : ι)) (n : ℕ) :
    diagramMatrixEquiv d (Equiv.refl b.support) ℤ (fDividedPower i n) =
      fDividedPower i n := by
  simp only [fDividedPower, map_mul, diagram_omegaMatrix, fixedRoot_eDividedPower d i hi]

private theorem fixedRoot_curve {F : Type*} [CommRing F] (d : P.Equiv P) (i : b.support)
    (hi : d.indexEquiv i = (i : ι)) (s : Bool) (t : F) :
    diagramMatrixEquiv d (Equiv.refl b.support) F ((simpleFamily (b := b)).curve (s, i) t) =
      (simpleFamily (b := b)).curve (s, i) t := by
  have hc (n : ℕ) : diagramMatrixEquiv d (Equiv.refl b.support) F
      ((simpleFamily (b := b)).coefficient (s, i) n) =
      (simpleFamily (b := b)).coefficient (S := F) (s, i) n := by
    cases s <;> simp only [IntegralCubicFamily.coefficient, simpleFamily,
      diagramMatrixEquiv_map, fixedRoot_eDividedPower d i hi, fixedRoot_fDividedPower d i hi]
  have hs (t : F) (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) F) :
      diagramMatrixEquiv d (Equiv.refl b.support) F (t • A) =
        t • diagramMatrixEquiv d (Equiv.refl b.support) F A := rfl
  simp only [IntegralCubicFamily.curve, map_add, map_one, hs, hc]

/-- A selected reflection word followed by a root symmetry fixing the selected roots. -/
def SubsystemRootOrbit (j : Fin 6 → b.support) (r t : ι) : Prop :=
  ∃ (l : List (Fin 6)) (d : P.Equiv P),
    (∀ i, d.indexEquiv (j i) = (j i : ι)) ∧
      d.indexEquiv (reflectionWord (l.map j) r) = t

end Generic

section Words
variable {α G : Type*} [Group G]

private theorem hom_fixed_eval (f : G →* G) (v : FreeGroup α →* G)
    (h : ∀ x, f (v (FreeGroup.of x)) = v (FreeGroup.of x)) (w : FreeGroup α) :
    f (v w) = v w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of x => exact h x
  | inv_of x hx => simpa only [map_inv] using congrArg Inv.inv hx
  | mul x y hx hy => simp only [map_mul, hx, hy]

end Words

attribute [local instance] Classical.decEq
local instance constancySymmetriesE7Fintype : Fintype typeE7Roots := Fintype.ofFinite _
local instance constancySymmetriesE8Fintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- Every E7 word is invariant under root reindexing fixing the six selected simple roots. -/
theorem e7Six_fixedRootSymmetry (F : Type*) [Field F] (w : SixNodeWord F)
    (d : typeE7RootPairing.Equiv typeE7RootPairing)
    (hd : ∀ i, d.indexEquiv (e7Node i) = (e7Node i : typeE7Roots))
    (r t : typeE7Roots) :
    (e7Six F w).val.val (Sum.inr (d.indexEquiv r)) (Sum.inr (d.indexEquiv t)) =
      (e7Six F w).val.val (Sum.inr r) (Sum.inr t) := by
  let v := (ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F)
  let db := Equiv.refl typeE7RootPairing_base.support
  have hv : diagramUnitsEquiv d db F (v w) = v w := by
    apply hom_fixed_eval (diagramUnitsEquiv d db F).toMonoidHom v
    rintro ⟨s, i, x⟩
    apply Units.ext
    change diagramMatrixEquiv d db F (e7Six F (FreeGroup.of (s, i, x))).val.val =
      (e7Six F (FreeGroup.of (s, i, x))).val.val
    simp only [e7Six_of, e7Simple, signedSimple_val, IntegralCubicFamily.unit_val]
    exact fixedRoot_curve d (e7Node i) (hd i) s x
  have hv' := congrArg Units.val hv
  have he := diagramMatrixEquiv_apply d db F (v w).val (Sum.inr r) (Sum.inr t)
  rw [← diagramUnitsEquiv_val, hv'] at he
  exact he

/-- The same invariance holds on all E8 constituents, for the actual evaluated word. -/
theorem e8Six_fixedRootSymmetry (F : Type*) [Field F] (w : SixNodeWord F)
    (d : typeE8RootPairing.Equiv typeE8RootPairing)
    (hd : ∀ i, d.indexEquiv (e8Node i) = (e8Node i : typeE8Roots))
    (r t : typeE8Roots) :
    (e8Six F w).val.val (Sum.inr (d.indexEquiv r)) (Sum.inr (d.indexEquiv t)) =
      (e8Six F w).val.val (Sum.inr r) (Sum.inr t) := by
  let v := (ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F)
  let db := Equiv.refl typeE8RootPairing_base.support
  have hv : diagramUnitsEquiv d db F (v w) = v w := by
    apply hom_fixed_eval (diagramUnitsEquiv d db F).toMonoidHom v
    rintro ⟨s, i, x⟩
    apply Units.ext
    change diagramMatrixEquiv d db F (e8Six F (FreeGroup.of (s, i, x))).val.val =
      (e8Six F (FreeGroup.of (s, i, x))).val.val
    simp only [e8Six_of, e8Simple, signedSimple_val, IntegralCubicFamily.unit_val]
    exact fixedRoot_curve d (e8Node i) (hd i) s x
  have hv' := congrArg Units.val hv
  have he := diagramMatrixEquiv_apply d db F (v w).val (Sum.inr r) (Sum.inr t)
  rw [← diagramUnitsEquiv_val, hv'] at he
  exact he

/-- Selected reflection transport and a constructed root symmetry equate the E7 entries. -/
theorem e7Six_diagonal_root_subsystemOrbit (F : Type*) [Field F] (w : SixNodeWord F)
    (hc : ∀ z, Commute (e7Six F w) (e7Six F z)) (hd : (e7Six F w).val.val.IsDiag)
    (r t : typeE7Roots) (h : SubsystemRootOrbit e7Node r t) :
    (e7Six F w).val.val (Sum.inr t) (Sum.inr t) =
      (e7Six F w).val.val (Sum.inr r) (Sum.inr r) := by
  obtain ⟨l, d, hfix, rfl⟩ := h
  exact (e7Six_fixedRootSymmetry F w d hfix _ _).trans
    (e7Six_diagonal_root_reflectionWord F w hc hd l r)

/-- Selected reflection transport and a constructed root symmetry equate the E8 entries. -/
theorem e8Six_diagonal_root_subsystemOrbit (F : Type*) [Field F] (w : SixNodeWord F)
    (hc : ∀ z, Commute (e8Six F w) (e8Six F z)) (hd : (e8Six F w).val.val.IsDiag)
    (r t : typeE8Roots) (h : SubsystemRootOrbit e8Node r t) :
    (e8Six F w).val.val (Sum.inr t) (Sum.inr t) =
      (e8Six F w).val.val (Sum.inr r) (Sum.inr r) := by
  obtain ⟨l, d, hfix, rfl⟩ := h
  exact (e8Six_fixedRootSymmetry F w d hfix _ _).trans
    (e8Six_diagonal_root_reflectionWord F w hc hd l r)

/-- Two roots of the A2 complement to the selected E6 subsystem. -/
def e8ComplementRoot (k : Fin 2) : typeE8Roots :=
  if k = 0 then typeE8RootPairing_baseEquiv 7 else
    ⟨typeE8LowestRoot, typeE8LowestRoot_mem_typeE8Roots⟩

/-- Both displayed complementary roots are orthogonal to the selected E6 simple roots. -/
theorem e8ComplementRoot_orthogonal (k : Fin 2) (i : Fin 6) :
    typeE8RootPairing.pairing (e8ComplementRoot k) (e8Node i) = 0 := by
  rw [typeE8RootPairing_pairing]
  fin_cases k <;> fin_cases i <;>
    norm_num [e8ComplementRoot, e8Node, typeE8RootPairing_baseEquiv_val,
      typeE8SimpleRootIndex_val, typeE8SimpleRoot, typeE8LowestRoot, dot, Fin.sum_univ_succ, Fin.castLE]

/-- The complementary reflections fix each of the six selected simple roots. -/
theorem e8ComplementRoot_reflection_fixes (k : Fin 2) (i : Fin 6) :
    typeE8RootPairing.reflectionPerm (e8ComplementRoot k) (e8Node i) = e8Node i :=
  typeE8RootPairing.reflectionPerm_eq_of_pairing_eq_zero'
    (e8ComplementRoot_orthogonal k i)

/-- The two explicit complementary reflections preserve every evaluated word matrix. -/
theorem e8Six_complement_reflection (F : Type*) [Field F] (w : SixNodeWord F)
    (k : Fin 2) (r t : typeE8Roots) :
    (e8Six F w).val.val
        (Sum.inr (typeE8RootPairing.reflectionPerm (e8ComplementRoot k) r))
        (Sum.inr (typeE8RootPairing.reflectionPerm (e8ComplementRoot k) t)) =
      (e8Six F w).val.val (Sum.inr r) (Sum.inr t) :=
  e8Six_fixedRootSymmetry F w (RootPairing.Equiv.reflection _ (e8ComplementRoot k))
    (e8ComplementRoot_reflection_fixes k) r t

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
