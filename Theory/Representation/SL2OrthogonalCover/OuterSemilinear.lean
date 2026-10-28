module
public import Theory.Representation.SL2OrthogonalCover.Universal
public import Theory.Representation.SL2NaturalOffenders.OuterSemilinear
public import Theory.Representation.SemilinearInvolutionFixedCard
import Mathlib.Tactic.FinCases

/-!
# Outer actors on the full orthogonal SL₂ cover

A binary automorphism intertwining the orthogonal action with an outer SL₂
actor induces a semilinear automorphism on the natural quotient. Its field
coefficient acts on the whole cover: the two maps obtained by composing with
scalar multiplication agree on the quotient, so uniqueness of lifts on the
commutator-generated cover makes them equal. The projection kernel is the
fixed space, which constructs the quotient actor from the original automorphism.

For an involution the nontrivial coefficient is involutive. Additive descent
then gives square-root fixed cardinality, including a transfer to the literal
fixed subgroup of any marked group actor.

Source: Aschbacher–Smith, Lemma 2.4.12(2), and the universal natural-cover
argument of Remark I.1.5 and Lemma I.1.6.
-/

public section
noncomputable section
namespace Representation.SL2OrthogonalCover
open Matrix Representation.OneCohomology Representation.OneCohomology.CentralCoverOriginalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
private theorem projection_eq_zero_iff_fixed (u : Space F) :
    projection u = 0 ↔ ∀ g, action g u = u := by
  change u ∈ (projection (F := F)).toLinearMap.ker ↔ u ∈ fixed (action (F := F))
  rw [projection_kernel, fixed_radical]

/-- The actual normalizing actor descends through the literal projection. -/
theorem intertwiner_descends
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ g u, E (action g u) = action (a g) (E u)) :
    ∃ e : Plane F ≃ₗ[ZMod 2] Plane F,
      (∀ g v, e (natural g v) = natural (a g) (e v)) ∧
      ∀ u, projection (E u) = e (projection u) := by
  let p := (binaryProjection (F := F)).toLinearMap
  have hker (u : Space F) : p (E u) = 0 ↔ p u = 0 := by
    change projection (E u) = 0 ↔ projection u = 0
    rw [projection_eq_zero_iff_fixed, projection_eq_zero_iff_fixed]
    constructor
    · intro hu g
      apply E.injective
      rw [hE, hu]
    · intro hu g
      obtain ⟨g, rfl⟩ := a.surjective g
      rw [← hE, hu]
  let i : Plane F →ₗ[ZMod 2] Space F :=
    { toFun v := ![0, v 0, v 1]
      map_add' := by intro v w; ext j; fin_cases j <;> simp
      map_smul' := by intro c v; ext j; fin_cases j <;> simp }
  have hi (v : Plane F) : p (i v) = v := by
    ext j; fin_cases j <;> rfl
  let e₀ : Plane F →ₗ[ZMod 2] Plane F := p.comp (E.toLinearMap.comp i)
  have hover (u : Space F) : p (E u) = e₀ (p u) := by
    have hz : p (u - i (p u)) = 0 := by rw [map_sub, hi, sub_self]
    have hz' := (hker _).mpr hz
    rw [map_sub, map_sub, sub_eq_zero] at hz'
    exact hz'
  have he₀ : Function.Injective e₀ := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    change e₀ v = 0 at hv
    have hp : p (i v) = 0 := (hker (i v)).mp hv
    simpa only [hi, Submodule.mem_bot] using hp
  let e : Plane F ≃ₗ[ZMod 2] Plane F := LinearEquiv.ofBijective e₀
    ⟨he₀, Finite.surjective_of_injective he₀⟩
  refine ⟨e, ?_, hover⟩
  intro g v
  obtain ⟨u, rfl⟩ := projection_surjective v
  change e₀ (natural g (projection u)) = natural (a g) (e₀ (projection u))
  have hover' (w : Space F) : projection (E w) = e₀ (projection w) := hover w
  rw [← projection.isIntertwining, ← hover', hE, projection.isIntertwining, hover']

/-- Uniqueness of a generated central cover lifts the quotient coefficient
field action to the actual full cover actor. -/
theorem intertwiner_semilinear_of_projection (hF : 2 < Nat.card F)
    (a : MulAut (SL F)) (e : Plane F ≃ₗ[ZMod 2] Plane F)
    (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ g u, E (action g u) = action (a g) (E u))
    (hover : ∀ u, projection (E u) = e (projection u))
    (σ : F ≃+* F) (hσ : ∀ c v, e (c • v) = σ c • e v) :
    ∀ c u, E (c • u) = σ c • E u := by
  intro c u
  let sc (d : F) : Space F →ₗ[ZMod 2] Space F :=
    ((d • LinearMap.id : Space F →ₗ[F] Space F).restrictScalars (ZMod 2))
  have hmodel := binaryProjection_isCover hF
  have heq : E.toLinearMap.comp (sc c) = (sc (σ c)).comp E.toLinearMap := by
    apply lift_unique (binaryAction (F := F))
      ((binaryAction (F := F)).comp a.toMonoidHom) hmodel.2.2
      (binaryProjection (F := F)).toLinearMap
      (fun v hv g => hmodel.2.1 hv (a g))
    · intro g v
      change E (c • action g v) = action (a g) (E (c • v))
      rw [← map_smul, hE]
    · intro g v
      change σ c • E (action g v) = action (a g) (σ c • E v)
      rw [hE, map_smul]
    · intro v
      change projection (E (c • v)) = projection (σ c • E v)
      rw [hover, map_smul, hσ, map_smul, hover]
  exact LinearMap.congr_fun heq u

theorem outer_intertwiner_semilinear (hF : 2 < Nat.card F)
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ g u, E (action g u) = action (a g) (E u))
    (houter : ¬ ∃ g, a = MulAut.conj g) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧
      ∀ c u, E (c • u) = σ c • E u := by
  obtain ⟨e, he, hover⟩ := intertwiner_descends a E hE
  obtain ⟨σ, hσne, hσ⟩ := SL2NaturalOffenders.outer_intertwiner_semilinear a e he houter
  exact ⟨σ, hσne, intertwiner_semilinear_of_projection hF a e E hE hover σ hσ⟩

omit [Finite F] [CharP F 2] in
theorem semilinear_coefficient_involutive
    (E : Space F ≃ₗ[ZMod 2] Space F) (hE : Function.Involutive E)
    (σ : F ≃+* F) (hσ : ∀ c u, E (c • u) = σ c • E u) :
    Function.Involutive σ := by
  intro c
  have hh := hE (c • (![1, 0, 0] : Space F))
  rw [hσ, hσ, hE] at hh
  have h0 := congrFun hh 0
  simpa using h0

/-- The actual outer involution on the full orthogonal cover has square-root
fixed cardinality. -/
theorem outer_involution_fixed_card_sq (hF : 2 < Nat.card F)
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ g u, E (action g u) = action (a g) (E u))
    (houter : ¬ ∃ g, a = MulAut.conj g) (hinv : Function.Involutive E) :
    Nat.card (E.toAddMonoidHom.eqLocus (AddMonoidHom.id (Space F))) ^ 2 =
      Nat.card (Space F) := by
  obtain ⟨σ, hσne, hσ⟩ := outer_intertwiner_semilinear hF a E hE houter
  exact SemilinearInvolution.fixed_card_sq σ
    (semilinear_coefficient_involutive E hinv σ hσ) hσne E.toAddMonoidHom hinv hσ

/-- The fixed count is transported to the original group actor using its
marked orthogonal coordinates, retaining the literal equalizer. -/
theorem outer_involution_fixed_card_sq_of_mulEquiv {A : Type*} [Group A]
    (hF : 2 < Nat.card F) (a : MulAut (SL F))
    (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ g u, E (action g u) = action (a g) (E u))
    (houter : ¬ ∃ g, a = MulAut.conj g)
    (α : A →* A) (hα : Function.Involutive α)
    (e : A ≃* Multiplicative (Space F))
    (he : ∀ x, (e (α x)).toAdd = E (e x).toAdd) :
    Nat.card (α.eqLocus (MonoidHom.id A)) ^ 2 = Nat.card A := by
  have hinv : Function.Involutive E := by
    intro u
    obtain ⟨x, hx⟩ := e.surjective (Multiplicative.ofAdd u)
    have hx' : (e x).toAdd = u := congrArg Multiplicative.toAdd hx
    rw [← hx', ← he, ← he, hα]
  obtain ⟨σ, hσne, hσ⟩ := outer_intertwiner_semilinear hF a E hE houter
  exact SemilinearInvolution.fixed_card_sq_of_mulEquiv σ
    (semilinear_coefficient_involutive E hinv σ hσ) hσne E.toAddMonoidHom hinv hσ α e he
end Representation.SL2OrthogonalCover
