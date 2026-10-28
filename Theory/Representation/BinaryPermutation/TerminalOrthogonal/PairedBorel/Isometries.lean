module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Summands

/-!
# Recognizing isometries of the paired orthogonal cores

An isometry of the five-point augmentation core permutes its five nonzero
singular vectors. These weight-four words span the core, so that permutation
recovers the entire linear map. The only finite checks below concern the five
coordinates and the 32 binary words, never the space of linear automorphisms.

For the orthogonal sum, restricting a map that preserves each summand gives
two factor isometries. A map exchanging the summands reduces to that case by
the literal swap. Thus every isometry preserving the unordered summand pair
is an element of the actual `(S₅ × S₅) ⋊ C₂` model. Uniqueness constructs a
homomorphism from any such group action, and a faithful action gives an
equivariant isomorphism onto its recovered model subgroup.

This supplies the full action marking used by `terminal_paired_residual_model`.
The source owner supplies the quadratic coordinates and summand preservation
for its faithful quotient action. Source: Aschbacher–Smith, combined manuscript
of 1 March 2004, G.11.2(12), printed p.364, and the Borel calculation in
12.8.13(7), printed p.856.
-/

@[expose] public section

namespace BinaryPermutation.TerminalOrthogonal.PairedBorel
open PairedFive

private def singularPoint (i : Fin 5) : Factor :=
  ⟨fun j => if j = i then 0 else 1, by
    have h : ∀ i : Fin 5, (∑ j : Fin 5, (if j = i then 0 else 1 : ZMod 2)) = 0 := by decide
    exact h i⟩

private lemma singularPoint_ne_zero (i : Fin 5) : singularPoint i ≠ 0 := by
  have h : ∀ i : Fin 5, (fun j : Fin 5 => if j = i then (0 : ZMod 2) else 1) ≠ 0 := by decide
  exact fun he => h i (congrArg Subtype.val he)

private lemma singularPoint_singular (i : Fin 5) : FiveGeometry.form (singularPoint i) = 0 := by
  apply (FiveGeometry.singular_iff _).mpr
  right
  have h : ∀ i : Fin 5,
      (Finset.univ.filter fun j : Fin 5 => (if j = i then (0 : ZMod 2) else 1) ≠ 0).card = 4 := by decide
  exact h i

private lemma singularPoint_injective : Function.Injective singularPoint := by
  intro i j h
  by_contra hij
  have he := congrArg (fun x : Factor => x.val i) h
  simp [singularPoint, hij] at he

private lemma exists_singularPoint (v : Factor) (hv : FiveGeometry.form v = 0) (hn : v ≠ 0) :
    ∃ i, v = singularPoint i := by
  have hw := ((FiveGeometry.singular_iff v).mp hv).resolve_left hn
  have h : ∀ x : Full (Fin 5),
      (Finset.univ.filter fun i => x i ≠ 0).card = 4 →
      ∃ i : Fin 5, x = fun j => if j = i then 0 else 1 := by decide
  obtain ⟨i, hi⟩ := h v.val hw
  exact ⟨i, Subtype.ext hi⟩

/-- The five singular words span the core using its own coordinates as coefficients. -/
private lemma sum_singularPoint (v : Factor) : ∑ i, v.val i • singularPoint i = v := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      ∀ j, (∑ i : Fin 5, x i * (if j = i then 0 else 1)) = x j := by decide
  apply Subtype.ext
  funext j
  simpa [singularPoint] using h v.val v.property j

private lemma factorAction_singularPoint (g : S5) (i : Fin 5) :
    factorAction g (singularPoint i) = singularPoint (g i) := by
  apply Subtype.ext
  funext j
  change (if g.symm j = i then (0 : ZMod 2) else 1) = (if j = g i then 0 else 1)
  simp only [g.symm_apply_eq]

/-- Every isometry of the five-point core is its actual coordinate permutation. -/
theorem exists_factorAction (f : Factor ≃ₗ[ZMod 2] Factor)
    (hf : ∀ v, FiveGeometry.form (f v) = FiveGeometry.form v) :
    ∃ g : S5, factorAction g = f := by
  have hs (i : Fin 5) : ∃ j, f (singularPoint i) = singularPoint j := by
    apply exists_singularPoint
    · rw [hf, singularPoint_singular]
    · exact fun h => singularPoint_ne_zero i (f.injective (h.trans f.map_zero.symm))
  choose p hp using hs
  have hinj : Function.Injective p := by
    intro i j hij
    apply singularPoint_injective
    apply f.injective
    rw [hp, hp, hij]
  let g : S5 := Equiv.ofBijective p ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨g, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [← sum_singularPoint v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [factorAction_singularPoint]
  exact congrArg (fun w : Factor => v.val i • w) (hp i).symm

private lemma exists_baseAction (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ v, PairedFive.form (f v) = PairedFive.form v)
    (hl : ∀ v : Factor, (f (v, 0)).2 = 0)
    (hr : ∀ v : Factor, (f (0, v)).1 = 0) :
    ∃ a b : S5, modelAction (base (a, b)) = f := by
  let a : Factor →ₗ[ZMod 2] Factor :=
    (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
  let b : Factor →ₗ[ZMod 2] Factor :=
    (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
  have ha : Function.Injective a := by
    intro u v huv
    have he : f (u, 0) = f (v, 0) := Prod.ext huv ((hl u).trans (hl v).symm)
    exact congrArg Prod.fst (f.injective he)
  have hb : Function.Injective b := by
    intro u v huv
    have he : f (0, u) = f (0, v) := Prod.ext ((hr u).trans (hr v).symm) huv
    exact congrArg Prod.snd (f.injective he)
  let ea : Factor ≃ₗ[ZMod 2] Factor :=
    LinearEquiv.ofBijective a ⟨ha, Finite.surjective_of_injective ha⟩
  let eb : Factor ≃ₗ[ZMod 2] Factor :=
    LinearEquiv.ofBijective b ⟨hb, Finite.surjective_of_injective hb⟩
  have hqa : ∀ v, FiveGeometry.form (ea v) = FiveGeometry.form v := by
    intro v
    change FiveGeometry.form (f (v, 0)).1 = FiveGeometry.form v
    have h := hf (v, 0)
    simpa only [PairedFive.form_apply, hl, map_zero, add_zero] using h
  have hqb : ∀ v, FiveGeometry.form (eb v) = FiveGeometry.form v := by
    intro v
    change FiveGeometry.form (f (0, v)).2 = FiveGeometry.form v
    have h := hf (0, v)
    simpa only [PairedFive.form_apply, hr, map_zero, zero_add] using h
  obtain ⟨p, hp⟩ := exists_factorAction ea hqa
  obtain ⟨q, hq⟩ := exists_factorAction eb hqb
  refine ⟨p, q, ?_⟩
  apply LinearEquiv.ext
  intro v
  have hs : f v = f (v.1, 0) + f (0, v.2) := by
    rw [← map_add]
    simp
  rw [modelAction_base, hs]
  apply Prod.ext
  · change factorAction p v.1 = (f (v.1, 0)).1 + (f (0, v.2)).1
    rw [hr, add_zero]
    exact LinearEquiv.congr_fun hp v.1
  · change factorAction q v.2 = (f (v.1, 0)).2 + (f (0, v.2)).2
    rw [hl, zero_add]
    exact LinearEquiv.congr_fun hq v.2

/-- The full group preserving the form and the unordered pair of summands is
precisely the concrete swapped coordinate-permutation model. -/
theorem exists_modelAction (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ v, PairedFive.form (f v) = PairedFive.form v)
    (hs : PreservesSummandPair f) : ∃ g : Model, modelAction g = f := by
  rcases hs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · obtain ⟨a, b, h⟩ := exists_baseAction f hf hl hr
    exact ⟨base (a, b), h⟩
  · have hf' : ∀ v, PairedFive.form ((f * PairedFive.swap) v) = PairedFive.form v := by
      intro v
      exact (hf (PairedFive.swap v)).trans (PairedFive.swap_form v)
    obtain ⟨a, b, h⟩ := exists_baseAction (f * PairedFive.swap) hf' hr hl
    refine ⟨base (a, b) * interchange, ?_⟩
    rw [map_mul, h]
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, modelAction_interchange, LinearEquiv.mul_apply]
    rfl

/-- The geometric recognition has a unique answer in the faithful concrete model. -/
theorem existsUnique_modelAction (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ v, PairedFive.form (f v) = PairedFive.form v)
    (hs : PreservesSummandPair f) : ∃! g : Model, modelAction g = f := by
  obtain ⟨g, hg⟩ := exists_modelAction f hf hs
  exact ⟨g, hg, fun h hh => modelAction_injective (hh.trans hg.symm)⟩

section Lift
variable {D : Type*} [Group D]
  (φ : D →* (Space ≃ₗ[ZMod 2] Space))
  (hq : ∀ d v, PairedFive.form (φ d v) = PairedFive.form v)
  (hs : ∀ d, PreservesSummandPair (φ d))

/-- Recover a genuine homomorphism into the concrete model from the geometric action. -/
noncomputable def liftModelAction : D →* Model where
  toFun d := (exists_modelAction (φ d) (hq d) (hs d)).choose
  map_one' := by
    apply modelAction_injective
    rw [(exists_modelAction (φ 1) (hq 1) (hs 1)).choose_spec, map_one, map_one]
  map_mul' d e := by
    apply modelAction_injective
    rw [(exists_modelAction (φ (d * e)) (hq (d * e)) (hs (d * e))).choose_spec,
      map_mul, map_mul, (exists_modelAction (φ d) (hq d) (hs d)).choose_spec,
      (exists_modelAction (φ e) (hq e) (hs e)).choose_spec]

@[simp] theorem modelAction_liftModelAction (d : D) :
    modelAction (liftModelAction φ hq hs d) = φ d :=
  (exists_modelAction (φ d) (hq d) (hs d)).choose_spec

theorem modelAction_comp_liftModelAction : modelAction.comp (liftModelAction φ hq hs) = φ := by
  apply MonoidHom.ext
  intro d
  exact modelAction_liftModelAction φ hq hs d

theorem liftModelAction_injective (hφ : Function.Injective φ) :
    Function.Injective (liftModelAction φ hq hs) := by
  intro d e h
  apply hφ
  simpa only [modelAction_liftModelAction] using congrArg modelAction h

theorem liftModelAction_unique (r : D →* Model) (hr : modelAction.comp r = φ) :
    r = liftModelAction φ hq hs := by
  apply MonoidHom.ext
  intro d
  apply modelAction_injective
  exact (congrArg (fun ψ : D →* (Space ≃ₗ[ZMod 2] Space) => ψ d) hr).trans (modelAction_liftModelAction φ hq hs d).symm

/-- The actual range marking supplied to a faithful-action consumer. -/
noncomputable def liftModelEquiv (hφ : Function.Injective φ) :
    D ≃* (liftModelAction φ hq hs).range :=
  MonoidHom.ofInjective (liftModelAction_injective φ hq hs hφ)

/-- The range marking intertwines the original action and the literal model action. -/
theorem liftModelEquiv_apply (hφ : Function.Injective φ) (d : D) (v : Space) :
    modelAction (liftModelEquiv φ hq hs hφ d).val v = φ d v :=
  LinearEquiv.congr_fun (modelAction_liftModelAction φ hq hs d) v

end Lift
end BinaryPermutation.TerminalOrthogonal.PairedBorel
