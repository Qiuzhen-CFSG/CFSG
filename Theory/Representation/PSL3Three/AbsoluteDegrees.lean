module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.Inputs
public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses

/-!
# The small absolute characteristic-two degrees of PSL₃(3)

Seven pairwise inequivalent simple modules saturate the odd-order conjugacy
class bound: the trivial module, degrees twelve and twenty-six, and four
modules of degree sixteen. Every simple is then equivalent to one of them.
Two explicit noncommuting elementary matrices exclude degree one for a faithful
representation, while the bound eighteen excludes degree twenty-six.

For a finite coefficient field, extension to its algebraic closure preserves
faithfulness and dimension; absolute irreducibility supplies simplicity there.
The resulting degree window feeds the existing binary scalar descent with
precisely its original action and hypotheses.

The geometric point and incidence-cycle models supply degrees twelve and
twenty-six. The checked native degree-sixteen actions supply the four remaining
nontrivial models, and the matrix conjugacy certificates supply the class bound.
`absoluteDegreeWindow` discharges all three premises of the conditional
assembly. Binary degree twelve still uses the separate field-of-definition
obstruction; no assertion about that obstruction is made here.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2,
manuscript pp.9--10, and the characteristic-two decomposition matrix of L₃(3).
-/

open scoped TensorProduct
namespace Representation.PSL3Three.AbsoluteDegrees
universe v

private theorem matrix_noncommutative :
    ∃ x y : Matrix.PSL3Three.PSL, x * y ≠ y * x := by
  let a : Matrix.PSL3Three.SL := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
  let b : Matrix.PSL3Three.SL := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩
  refine ⟨Matrix.PSL3Three.project a, Matrix.PSL3Three.project b, ?_⟩
  intro h
  have hab : a * b = b * a := Matrix.PSL3Three.project_injective (by
    simpa only [map_mul] using h)
  have hc := congrArg (fun g : Matrix.PSL3Three.SL => g.val 0 2) hab
  change (1 : ZMod 3) = 0 at hc
  exact one_ne_zero hc

/-- Faithfulness rules out degree one on the literal projective matrix group. -/
public theorem faithful_finrank_ne_one
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (σ : Representation F Matrix.PSL3Three.PSL W) (hf : Function.Injective σ) :
    Module.finrank F W ≠ 1 := by
  intro hd
  obtain ⟨x, y, hxy⟩ := matrix_noncommutative
  apply hxy
  apply hf
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (σ x)
  obtain ⟨b, hb, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (σ y)
  rw [map_mul, map_mul, ha, hb]
  simp [smul_smul, mul_comm]

private abbrev CandidateIndex := Option (Option (Option (Fin 4)))

/-- Exhaustion and the small-degree conclusion from actual simple models and
the independently supplied odd-order conjugacy-class bound. -/
public theorem small_degree_of_models
    {F W : Type v} [Field F] [IsAlgClosed F] [CharP F 2]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ₁₂ : Representation F Matrix.PSL3Three.PSL (Fin 12 → F))
    (ρ₂₆ : Representation F Matrix.PSL3Three.PSL (Fin 26 → F))
    (ρ₁₆ : Fin 4 → Representation F Matrix.PSL3Three.PSL (Fin 16 → F))
    [IsIrreducible ρ₁₂] [IsIrreducible ρ₂₆] [∀ i, IsIrreducible (ρ₁₆ i)]
    (hne : Pairwise fun i j => IsEmpty ((ρ₁₆ i).Equiv (ρ₁₆ j)))
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Matrix.PSL3Three.PSL | ¬ 2 ∣ orderOf g}) ≤ 7)
    (σ : Representation F Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank F W ≤ 18) :
    Module.finrank F W = 12 ∨ Module.finrank F W = 16 := by
  classical
  let V : CandidateIndex → Type v := fun i =>
    match i with
    | none => F
    | some none => Fin 12 → F
    | some (some none) => Fin 26 → F
    | some (some (some _)) => Fin 16 → F
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    rcases i with _ | (_ | (_ | i)) <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module F (V i) := fun i => by
    rcases i with _ | (_ | (_ | i)) <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation F Matrix.PSL3Three.PSL (V i) := fun i =>
    match i with
    | none => Representation.trivial F _ F
    | some none => ρ₁₂
    | some (some none) => ρ₂₆
    | some (some (some j)) => ρ₁₆ j
  have finV : ∀ i, FiniteDimensional F (V i) := by
    intro i
    rcases i with _ | (_ | (_ | i)) <;> dsimp [V] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    rcases i with _ | (_ | (_ | i))
    · change IsIrreducible (Representation.trivial F _ F)
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    all_goals dsimp [rep]; infer_instance
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    rcases i with _ | (_ | (_ | i)) <;> rcases j with _ | (_ | (_ | j))
    all_goals first
      | exact hij rfl
      | exact (hne (fun h => hij (by simp [h]))).false e
      | have he := e.toLinearEquiv.finrank_eq
        norm_num [V] at he
  have hc : Nat.card CandidateIndex = 7 := by
    simp [CandidateIndex, Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_pRegular_class_bound V rep 2 hdistinct
    (hc ▸ hclasses) σ
  have he := e.toLinearEquiv.finrank_eq
  rcases i with _ | (_ | (_ | i)) <;> simp only [V, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  · exact (faithful_finrank_ne_one σ hf he).elim
  · exact Or.inl he
  · omega
  · exact Or.inr he

/-- The exact native contract follows from the two module-construction
families and the class bound. All three calculations remain explicit. -/
public theorem absoluteDegreeWindow_of_constructions
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v})
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Matrix.PSL3Three.PSL | ¬ 2 ∣ orderOf g}) ≤ 7) :
    AbsoluteDegreeWindow.{v} := by
  intro K _ _ _ W _ _ _ σ hf ha hd
  let F := AlgebraicClosure K
  obtain ⟨ρ₁₂, ρ₂₆, h₁₂, h₂₆⟩ := hprincipal F
  obtain ⟨ρ₁₆, h₁₆, hne⟩ := hsixteen F
  let := h₁₂
  let := h₂₆
  let := h₁₆
  let := ha.irreducible_of_closure
  have hf' := (extendScalars_faithful_iff F σ).mp hf
  have hd' : Module.finrank F (F ⊗[K] W) ≤ 18 := by
    simpa only [Module.finrank_baseChange] using hd
  have h := small_degree_of_models ρ₁₂ ρ₂₆ ρ₁₆ hne hclasses
    (extendScalars F σ) hf' hd'
  simpa only [Module.finrank_baseChange] using h

/-- Every faithful absolutely irreducible characteristic-two representation of
the literal PSL₃(3) of degree at most eighteen has degree twelve or sixteen.
The concrete simple models and odd-order class bound are all discharged. -/
public theorem absoluteDegreeWindow : AbsoluteDegreeWindow.{v} :=
  absoluteDegreeWindow_of_constructions principalModelsExist SixteenModels.sixteenModelsExist
    Matrix.PSL3Three.odd_conjClasses_card_le_seven

/-- Application to the existing binary descent consumer. The independent field
obstruction is retained, as are the three construction/counting premises. -/
public theorem binary_degree_twelve_of_constructions
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v})
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Matrix.PSL3Three.PSL | ¬ 2 ∣ orderOf g}) ≤ 7)
    (hfield : DegreeSixteenFieldObstruction.{v})
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 18) :
    Module.finrank (ZMod 2) W = 12 :=
  binary_degree_twelve_of_absolute_calculations
    (absoluteDegreeWindow_of_constructions hprincipal hsixteen hclasses) hfield σ hf hd

/-- The proved absolute-degree window discharges the degree-calculation input
of binary scalar descent. Only the independently owned field obstruction remains. -/
public theorem binary_degree_twelve_of_field_obstruction
    (hfield : DegreeSixteenFieldObstruction.{v})
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 18) :
    Module.finrank (ZMod 2) W = 12 :=
  binary_degree_twelve_of_absolute_calculations absoluteDegreeWindow hfield σ hf hd

end Representation.PSL3Three.AbsoluteDegrees
