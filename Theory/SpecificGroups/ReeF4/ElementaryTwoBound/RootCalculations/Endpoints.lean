module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Curves
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords

/-!
# The two elementary endpoint groups in the Ree counting argument

The groups Y₁X₂ and X₆Y₇ are products of two commuting additive curves.
Their parameter maps are injective by the existing twelve-coordinate uniqueness
for the actual fixed matrix subgroup. This proves their orders, the order of
Y₁, and the trivial intersection Y₁ ∩ X₂ used in GLS3 Lemma 3.3.9.

Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/
@[expose] public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations
open Subgroup Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open MatrixRelations.LongCommutators
open Theory.AlgebraicGroup.StandardRootSystem

private def pairIndex : Bool → Fin 8 | false => 1 | true => 5
private def centralIndex : Bool → Fin 8 | false => 0 | true => 6
private theorem pair_odd (s : Bool) : (pairIndex s).val % 2 ≠ 0 := by cases s <;> decide
private theorem central_even (s : Bool) : (centralIndex s).val % 2 = 0 := by cases s <;> decide

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

private theorem commute_two_two {G : Type*} [Group G] (a b c d : G)
    (hac : Commute a c) (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d) :
    Commute (a * b) (c * d) := (hac.mul_right had).mul_left (hbc.mul_right hbd)

private theorem endpoint_commute (m : ℕ) (s : Bool) (a b : CoefficientField m) :
    Commute (mainElement m (pairIndex s) a) (centralElement m (centralIndex s) b) := by
  change _ * _ = _ * _
  apply toSplitGroup_injective m
  simp only [map_mul, mainElement_coe, centralElement_coe]
  change Commute (rootWord m (pairIndex s) a) (centralWord m (centralIndex s) b)
  cases s
  · change Commute (rootWord m 1 a) (centralWord m 0 b)
    have h : centralWord m 0 b =
        MatrixRelations.LongCommutators.X m 3 b *
          MatrixRelations.LongCommutators.X m 2 (halfFrobenius m b) := by
      simp only [centralWord, fieldEnd_half]; rfl
    rw [OuterElimination.word_1, h]
    apply commute_two_two
    all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]) _ _
  · change Commute (rootWord m 5 a) (centralWord m 6 b)
    have h₁ : rootWord m 5 a =
        MatrixRelations.LongCommutators.X m 16 a *
          MatrixRelations.LongCommutators.X m 17 (halfFrobenius m a) := by
      simp only [rootWord, fieldEnd_half]
      exact mul_one _
    have h₂ : centralWord m 6 b =
        MatrixRelations.LongCommutators.X m 21 b *
          MatrixRelations.LongCommutators.X m 20 (halfFrobenius m b) := by
      simp only [centralWord, fieldEnd_half]; rfl
    rw [h₁, h₂]
    apply commute_two_two
    all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]) _ _

private def productHom {A B G : Type*} [Group A] [Group B] [Group G]
    (f : A →* G) (g : B →* G) (hc : ∀ a b, Commute (f a) (g b)) : A × B →* G where
  toFun x := f x.1 * g x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    exact (hc y.1 x.2).mul_mul_mul_comm _ _

private theorem productHom_range {A B G : Type*} [Group A] [Group B] [Group G]
    (f : A →* G) (g : B →* G) (hc : ∀ a b, Commute (f a) (g b)) :
    (productHom f g hc).range = f.range ⊔ g.range := by
  apply le_antisymm
  · rintro _ ⟨⟨a,b⟩, rfl⟩
    exact mul_mem ((show f.range ≤ f.range ⊔ g.range from le_sup_left) (show f a ∈ f.range from ⟨a, rfl⟩))
      ((show g.range ≤ f.range ⊔ g.range from le_sup_right) (show g b ∈ g.range from ⟨b, rfl⟩))
  · apply sup_le
    · rintro _ ⟨a, rfl⟩
      exact ⟨(a, 1), by simp [productHom]⟩
    · rintro _ ⟨b, rfl⟩
      exact ⟨(1, b), by simp [productHom]⟩

/-- Embed either endpoint's pair and central parameters in the positive layout. -/
def endpointParameters (m : ℕ) (s : Bool) (a b : CoefficientField m) :
    PositiveParameters m where
  pair := if s then ![0, 0, a, 0] else ![0, a, 0, 0]
  main := fun _ => 0
  central := if s then ![0, 0, b, 0] else ![b, 0, 0, 0]

private theorem wordElement_endpoint (m : ℕ) (s : Bool) (a b : CoefficientField m) :
    wordElement m (endpointParameters m s a b) =
      mainElement m (pairIndex s) a * centralElement m (centralIndex s) b := by
  cases s <;> simp [wordElement, endpointParameters, pairIndex, centralIndex,
    positive_pair_indices, positive_quartet_indices, List.ofFn_succ,
    Parabolics.RadicalCoordinates.FixedCoordinates.pairCount,
    Parabolics.RadicalCoordinates.FixedCoordinates.quartetCount]

private def endpointHom (m : ℕ) (s : Bool) :
    Multiplicative (CoefficientField m) × Multiplicative (CoefficientField m) →* Model m :=
  productHom (pairHom m (pairIndex s) (pair_odd s))
    (centralHom m (centralIndex s) (central_even s))
    (fun a b => endpoint_commute m s a.toAdd b.toAdd)

private theorem endpointHom_injective (m : ℕ) (s : Bool) :
    Function.Injective (endpointHom m s) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hp : endpointParameters m s a.toAdd b.toAdd =
      endpointParameters m s c.toAdd d.toAdd := by
    apply wordElement_injective m
    rw [wordElement_endpoint, wordElement_endpoint]
    exact h
  apply Prod.ext
  · cases s
    · exact congrArg (fun p : PositiveParameters m => p.pair 1) hp
    · exact congrArg (fun p : PositiveParameters m => p.pair 2) hp
  · cases s
    · exact congrArg (fun p : PositiveParameters m => p.central 0) hp
    · exact congrArg (fun p : PositiveParameters m => p.central 2) hp

private theorem endpointHom_range (m : ℕ) (s : Bool) :
    (endpointHom m s).range = if s then right m else left m := by
  calc
    _ = (pairHom m (pairIndex s) (pair_odd s)).range ⊔
        (centralHom m (centralIndex s) (central_even s)).range :=
      productHom_range _ _ _
    _ = _ := by
      rw [← X_eq_range, ← Y_eq_range]
      cases s
      · exact sup_comm _ _
      · rfl

private theorem card_endpoint (m : ℕ) (s : Bool) :
    Nat.card (if s then right m else left m : Subgroup (Model m)) = (2 ^ (2 * m + 1)) ^ 2 := by
  rw [← endpointHom_range m s,
    ← Nat.card_congr (MonoidHom.ofInjective (endpointHom_injective m s)).toEquiv,
    Nat.card_prod]
  change Nat.card (CoefficientField m) * Nat.card (CoefficientField m) = _
  rw [field_card, pow_two]

theorem card_left (m : ℕ) : Nat.card (left m) = (2 ^ (2 * m + 1)) ^ 2 :=
  card_endpoint m false

theorem card_right (m : ℕ) : Nat.card (right m) = (2 ^ (2 * m + 1)) ^ 2 :=
  card_endpoint m true

theorem mem_left_iff (m : ℕ) (x : Model m) :
    x ∈ left m ↔ ∃ a b, mainElement m 1 a * centralElement m 0 b = x := by
  rw [← show (endpointHom m false).range = left m from endpointHom_range m false]
  change (∃ p : Multiplicative (CoefficientField m) × Multiplicative (CoefficientField m),
    mainElement m 1 p.1.toAdd * centralElement m 0 p.2.toAdd = x) ↔ _
  exact ⟨fun ⟨⟨a,b⟩, h⟩ => ⟨a.toAdd,b.toAdd,h⟩,
    fun ⟨a,b,h⟩ => ⟨(Multiplicative.ofAdd a, Multiplicative.ofAdd b),h⟩⟩

theorem mem_right_iff (m : ℕ) (x : Model m) :
    x ∈ right m ↔ ∃ a b, mainElement m 5 a * centralElement m 6 b = x := by
  rw [← show (endpointHom m true).range = right m from endpointHom_range m true]
  change (∃ p : Multiplicative (CoefficientField m) × Multiplicative (CoefficientField m),
    mainElement m 5 p.1.toAdd * centralElement m 6 p.2.toAdd = x) ↔ _
  exact ⟨fun ⟨⟨a,b⟩, h⟩ => ⟨a.toAdd,b.toAdd,h⟩,
    fun ⟨a,b,h⟩ => ⟨(Multiplicative.ofAdd a, Multiplicative.ofAdd b),h⟩⟩

theorem mainElement_second_injective (m : ℕ) : Function.Injective (mainElement m 1) := by
  intro a b h
  have hh : endpointHom m false (Multiplicative.ofAdd a, 1) =
      endpointHom m false (Multiplicative.ofAdd b, 1) := by
    simpa [endpointHom, productHom, pairHom, centralHom, pairIndex, centralIndex] using h
  exact congrArg (fun p => p.1.toAdd) (endpointHom_injective m false hh)

@[simp] theorem mainElement_second_eq_one_iff (m : ℕ) (a : CoefficientField m) :
    mainElement m 1 a = 1 ↔ a = 0 := by
  rw [← mainElement_zero m 1, (mainElement_second_injective m).eq_iff]

theorem centralElement_first_injective (m : ℕ) : Function.Injective (centralElement m 0) := by
  intro a b h
  have hh : endpointHom m false (1, Multiplicative.ofAdd a) =
      endpointHom m false (1, Multiplicative.ofAdd b) := by
    simpa [endpointHom, productHom, pairHom, centralHom, pairIndex, centralIndex] using h
  exact congrArg (fun p => p.2.toAdd) (endpointHom_injective m false hh)

theorem card_Y₁ (m : ℕ) : Nat.card (Y m 0) = 2 ^ (2 * m + 1) := by
  rw [Y_eq_range m 0 (by decide),
    ← Nat.card_congr (MonoidHom.ofInjective (f := centralHom m 0 (by decide)) (centralElement_first_injective m)).toEquiv]
  exact field_card m

/-- The two root factors meet only at the identity in the actual model. -/
theorem disjoint_Y₁_X₂ (m : ℕ) : Y m 0 ⊓ ElementaryTwoBound.X m 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨a, ha⟩ := (mem_Y_iff m 0 (by decide) x).mp hx.1
  obtain ⟨b, hb⟩ := (mem_X_iff m 1 (by decide) x).mp hx.2
  have hh : endpointHom m false (1, Multiplicative.ofAdd a) =
      endpointHom m false (Multiplicative.ofAdd b, 1) := by
    simpa [endpointHom, productHom, pairHom, centralHom, pairIndex, centralIndex]
      using ha.trans hb.symm
  have ha0 : a = 0 := congrArg (fun p => p.2.toAdd) (endpointHom_injective m false hh)
  rw [← ha, ha0, centralElement_zero]
  exact one_mem _

end ReeF4.ElementaryTwoBound.RootCalculations
