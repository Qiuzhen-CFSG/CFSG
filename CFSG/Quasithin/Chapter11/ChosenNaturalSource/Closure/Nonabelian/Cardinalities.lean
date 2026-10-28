module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.ChosenIntersection
public import Mathlib.FieldTheory.Finiteness

/-!
# Cardinalities of the original natural flag in 11.5.3

The surviving action retains a full SL3 or Sp4 marking. Its invariant flag
is identified with the three subspaces named by Closure.Geometry. When
C_V(L) is trivial, the original quotient map is bijective, so field-space
cardinalities transfer to the actual ambient subgroups V, V1 and V2.
The resulting coranks are 2n,n for SL3 and 3n,2n for Sp4.

The intersection consumer discharges the cardinal inputs of ChosenIntersection.
Its point residual and point generation inputs remain genuine model obligations.
Source: Aschbacher--Smith, 11.5.3(1--2), printed pp.779--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} (c : Coordinates D F)

omit [Finite G] in
private theorem quotient_injective
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective D.toCentralQuotient := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hfixed]
  exact ⟨v.property, (quotient_eq_one_iff D v).mp hv⟩

private def modelMap : V → c.Space := fun v => c.linearEquiv (D.toCentralQuotient v).toAdd

private theorem modelMap_bijective
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : Function.Bijective (modelMap c) := by
  constructor
  · intro v w h
    apply quotient_injective hfixed
    exact c.linearEquiv.injective h
  · intro w
    obtain ⟨q, rfl⟩ := c.linearEquiv.surjective w
    obtain ⟨v, hv⟩ := D.toCentralQuotient_surjective (Multiplicative.ofAdd q)
    exact ⟨v, congrArg (fun q => c.linearEquiv q.toAdd) hv⟩

theorem card_preimage
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (U : Submodule F.Carrier c.Space) :
    Nat.card (c.preimage U) = (2 ^ F.degree) ^ Module.finrank F.Carrier U := by
  let f : c.preimage U → U := fun v =>
    ⟨modelMap c ⟨v.val, D.centralQuotientPreimage_le _ v.property⟩,
      (c.mem_preimage U _).mp v.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      have hh := (modelMap_bijective c hfixed).injective (congrArg Subtype.val h)
      exact congrArg (fun x : V => (x : G)) hh
    · intro w
      obtain ⟨v, hv⟩ := (modelMap_bijective c hfixed).surjective w.val
      have hvU : modelMap c v ∈ U := by rw [hv]; exact w.property
      refine ⟨⟨v.val, (c.mem_preimage U v).mpr hvU⟩, ?_⟩
      exact Subtype.ext hv
  let : Finite c.Space := Finite.of_surjective _ (modelMap_bijective c hfixed).surjective
  let : Module.Finite F.Carrier U := Module.Finite.of_finite
  rw [Nat.card_congr (Equiv.ofBijective f hf), Module.natCard_eq_pow_finrank (K := F.Carrier), F.card_eq]

open Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
/-- The surviving 11.5.1 alternatives, with both full action markings. -/
inductive RemainingAction (D : ChosenModule T L V) (F : BinaryField) where
  | sl3 (marking : ActionEquiv D.centralQuotientAction (linearNatural F 3))
  | sp4 (marking : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))

def RemainingAction.coordinates (a : RemainingAction D F) : Coordinates D F :=
  match a with
  | .sl3 h => .sl3 h
  | .sp4 h => .sp4 h

def RemainingAction.dimension (a : RemainingAction D F) : ℕ :=
  match a with
  | .sl3 _ => 3
  | .sp4 _ => 4

/-- Earlier flag data on the actual chosen quotient, not terminal conclusions.
Uniqueness, when needed, is the separate predicate `flag.IsUnique`. -/
structure MarkedFlag (E : Geometry D) where
  action : RemainingAction D E.input.field
  flag : InvariantFlag action.coordinates
  point_eq : E.point = action.coordinates.binarySubspace (flag.space 0)
  plane_eq : E.plane = action.coordinates.binarySubspace (flag.space 1)
  threeSpace_eq : E.threeSpace = action.coordinates.binarySubspace (flag.space 2)

variable {E : Geometry D} (F₀ : MarkedFlag E)

theorem card_original (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card V = 2 ^ (F₀.action.dimension * E.input.field.degree) := by
  have hc := Nat.card_congr
    (Equiv.ofBijective (modelMap F₀.action.coordinates)
      (modelMap_bijective F₀.action.coordinates hfixed))
  cases ha : F₀.action with
  | sl3 h =>
    simp only [ha, RemainingAction.coordinates, Coordinates.Space, Nat.card_fun,
      Nat.card_fin, E.input.field.card_eq, ← pow_mul] at hc
    simpa only [ha, RemainingAction.dimension, Nat.mul_comm] using hc
  | sp4 h =>
    simp only [ha, RemainingAction.coordinates, Coordinates.Space, Nat.card_fun,
      Nat.card_sum, Nat.card_fin, E.input.field.card_eq, ← pow_mul] at hc
    simpa only [ha, RemainingAction.dimension, Nat.mul_comm] using hc

include F₀ in
theorem card_line (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card E.V₁ = 2 ^ E.input.field.degree := by
  change Nat.card (D.centralQuotientPreimage E.point) = _
  rw [F₀.point_eq]
  change Nat.card (F₀.action.coordinates.preimage (F₀.flag.space _)) = _
  rw [card_preimage _ hfixed, F₀.flag.dimension]
  simp

include F₀ in
theorem card_plane (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card E.V₂ = 2 ^ (2 * E.input.field.degree) := by
  change Nat.card (D.centralQuotientPreimage E.plane) = _
  rw [F₀.plane_eq]
  change Nat.card (F₀.action.coordinates.preimage (F₀.flag.space _)) = _
  rw [card_preimage _ hfixed, F₀.flag.dimension]
  simp [← pow_mul, Nat.mul_comm]

open CFSG.Quasithin.ChapterE

theorem corank_line (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    subgroupCorank V E.V₁ = (F₀.action.dimension - 1) * E.input.field.degree := by
  apply E.line_corank_of_cardinalities _ (card_line F₀ hfixed)
  rw [card_original F₀ hfixed]
  congr 1
  cases F₀.action <;> simp only [RemainingAction.dimension] <;> omega

theorem corank_plane (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    subgroupCorank V E.V₂ = (F₀.action.dimension - 2) * E.input.field.degree := by
  let := D.elementary
  unfold subgroupCorank
  rw [← log_card_sub_log_card_eq_log_relIndex V E.V₂
    (D.centralQuotientPreimage_le E.plane), card_original F₀ hfixed,
    card_plane F₀ hfixed, Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two]
  cases F₀.action <;> simp only [RemainingAction.dimension] <;> omega

include F₀ in
theorem plane_corank_lt_line (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    subgroupCorank V E.V₂ < subgroupCorank V E.V₁ := by
  rw [corank_plane F₀ hfixed, corank_line F₀ hfixed]
  have hn := E.input.field.degree_pos
  cases F₀.action <;> simp only [RemainingAction.dimension] <;> omega

include F₀ in
theorem plane_centralizer_le
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ E.M)
    (hr : (subgroupCorank V E.V₁ : ℕ∞) ≤ globalR V) :
    centralizer (E.V₂ : Set G) ≤ E.M := by
  apply (centralizer_le_normalizer_of_corank_lt_globalR
    (D.centralQuotientPreimage_le E.plane) _).trans hNV
  apply lt_of_lt_of_le _ hr
  exact_mod_cast plane_corank_lt_line F₀ hfixed

include F₀ in
theorem intersection_and_rank
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hres : pointResidual L E.z = E.L₁) (hK : E.Kz = E.K)
    (hgen : PointGeneration L V E.V₁)
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hKL : E.K = E.L₁) :
    (∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g : G →* G) ≤
        E.V₁.map (MulAut.conj l : G →* G)) ∧
      (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V := by
  have h := E.intersection_and_corank hz hz1 htrans hres hK hgen hTI hKL
  rwa [corank_line F₀ hfixed] at h

include F₀ in
/-- The earlier local-module value 11.2.2(1) and the new intersection bound
supply the strict numerical hypothesis of E.3.19, including field degree two. -/
theorem one_lt_globalS
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : @localM _ _ V D.elementary = E.input.field.degree)
    (hr : (subgroupCorank V E.V₁ : ℕ∞) ≤ globalR V) :
    1 < @globalS _ _ V D.elementary := by
  let := D.elementary
  change 1 < min (globalR V) (localM V : ℕ∞)
  apply lt_min
  · apply lt_of_lt_of_le _ hr
    rw [corank_line F₀ hfixed]
    have hn := E.input.nonbinary
    have h : 1 < (F₀.action.dimension - 1) * E.input.field.degree := by
      cases F₀.action <;> simp only [RemainingAction.dimension] <;> omega
    exact_mod_cast h
  · rw [hm]
    exact_mod_cast E.input.nonbinary

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
