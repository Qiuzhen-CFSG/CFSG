module

public import Theory.AlgebraicGroup.RightTranslation.ExteriorRational
public import Theory.AlgebraicGroup.RightTranslation.Representation

/-! Faithful Chevalley representations. Adding the coordinate-translation
representation preserves the exact line stabilizer by placing the distinguished
line in the first summand. Source: Borel, *Linear Algebraic Groups*, §§5.1, 11.1. -/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

open scoped ExteriorAlgebra

universe u v w
variable {k : Type u} [Field k]

private theorem line_prod_bot {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (c : V) :
    (k ∙ c).prod (⊥ : Submodule k W) = k ∙ (c, (0 : W)) := by
  ext z
  rcases z with ⟨x, y⟩
  constructor
  · rintro ⟨hx, hy⟩
    have hy' : y = 0 := hy
    subst y
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact Submodule.mem_span_singleton.mpr ⟨a, by simp⟩
  · intro hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
    rw [← ha]
    exact ⟨Submodule.smul_mem _ a (Submodule.mem_span_singleton_self c), by simp⟩

private theorem directSum_faithful_line {G : Variety k} [AlgebraicGroup G]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (π : RationalRepresentation G V) (σ : RationalRepresentation G W)
    (ρ : RationalRepresentation G (V × W)) (hsum : IsDirectSumRepresentation π σ ρ)
    (hfaith : Function.Injective σ.action) (c : V) (B : Subgroup (Variety.Point G))
    (hline : ∀ g, (π.action g : Module.End k V) c ∈ k ∙ c ↔ g ∈ B) :
    Function.Injective ρ.action ∧ ∀ g : Variety.Point G,
      (∀ x ∈ (k ∙ c).prod (⊥ : Submodule k W),
        (ρ.action g : Module.End k (V × W)) x ∈ (k ∙ c).prod (⊥ : Submodule k W)) ↔
      g ∈ B := by
  have happly : ∀ g (v : V) (w : W),
      (ρ.action g : Module.End k (V × W)) (v, w) =
      ((π.action g : Module.End k V) v, (σ.action g : Module.End k W) w) := hsum
  constructor
  · intro g h hgh
    apply hfaith
    apply Units.ext
    apply LinearMap.ext
    intro w
    have heq := congrArg (fun a : LinearMap.GeneralLinearGroup k (V × W) =>
      ((a : Module.End k (V × W)) (0, w)).2) hgh
    rw [happly, happly] at heq
    exact heq
  · intro g
    constructor
    · intro hg
      have hcL : (c, (0 : W)) ∈ (k ∙ c).prod (⊥ : Submodule k W) :=
        ⟨Submodule.mem_span_singleton_self c, Submodule.zero_mem _⟩
      have hcimage := hg (c, 0) hcL
      rw [happly] at hcimage
      exact (hline g).mp hcimage.1
    · intro hg x hx
      rw [line_prod_bot] at hx ⊢
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      apply Submodule.smul_mem
      rw [happly, map_zero, ← line_prod_bot c]
      exact ⟨(hline g).mpr hg, Submodule.zero_mem _⟩

/-- Any closed subgroup is the exact line stabilizer in a faithful rational
representation. The line is literally the Chevalley line times zero in the
sum with the faithful coordinate representation. -/
public theorem exists_faithful_rationalRepresentation_exact_lineStabilizer
    [IsAlgClosed k] {G : Variety k} [AlgebraicGroup G] (B : ClosedSubgroup G) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : RationalRepresentation G V),
      IsRationalRepresentation ρ ∧ Function.Injective ρ.action ∧
      ∃ L : Submodule k V, Module.finrank k L = 1 ∧
        ∀ g : Variety.Point G,
          (∀ x ∈ L, (ρ.action g : Module.End k V) x ∈ L) ↔ g ∈ B.toSubgroup := by
  let E := ⋀[k]^B.rightTranslateVanishingTopWedgeData.degree B.rightTranslateVanishingSpan
  let W := coordinateTranslationSubmodule G
  let : Module.Finite k W := coordinateTranslationSubmodule_finite G
  let π := B.rightTranslateVanishingExteriorRationalRepresentation
  let σ := coordinateTranslationRationalRepresentation G
  obtain ⟨ρ, hsum, hrat⟩ := rationalRepresentation_directSum_exists π σ
    B.rightTranslateVanishingExteriorRationalRepresentation_isRational
    (coordinateTranslationRationalRepresentation_isRational G)
  let c : E := B.rightTranslateVanishingPluckerVector
  have hc : c ≠ 0 := B.rightTranslateVanishingPluckerVector_ne_zero
  let L : Submodule k (E × W) := (k ∙ c).prod ⊥
  have hL : Module.finrank k L = 1 := by
    rw [show L = k ∙ (c, (0 : W)) from line_prod_bot c]
    exact finrank_span_singleton (by intro h; exact hc (congrArg Prod.fst h))
  have hchev (g : Variety.Point G) :
      (π.action g : Module.End k E) c ∈ k ∙ c ↔ g ∈ B.toSubgroup := by
    rw [show (π.action g : Module.End k E) c =
      exteriorPower.map B.rightTranslateVanishingTopWedgeData.degree
        (B.rightTranslateVanishingSpanGeneralLinear g).toLinearEquiv.toLinearMap c from
      B.rightTranslateVanishingExteriorGeneralLinear_apply g c]
    exact B.chevalleyPluckerLine_stabilizer_iff g
  have hsumFacts := directSum_faithful_line π σ ρ hsum
    (coordinateTranslationRepresentation_injective G) c B.toSubgroup hchev
  exact ⟨E × W, inferInstance, inferInstance, inferInstance, ρ, hrat, hsumFacts.1,
    L, hL, hsumFacts.2⟩

end Theory.AlgebraicGroup.BorelGeometricConjugacy
