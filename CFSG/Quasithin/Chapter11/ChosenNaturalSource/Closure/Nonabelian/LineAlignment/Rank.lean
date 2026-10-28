module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Conditions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Rank.Counting

/-!
# The original elementary plane action and line alignment

The coordinate projection identifies the actual source plane V₂ with the
marked two-dimensional field subspace, using C_V(L)=1. Transporting its
literal induced automizer gives a faithful binary representation. Every actor
lifts to the Sylow subgroup, so the proved semilinearity theorem and the
semilinear counting bound give rank at most the field degree.

This discharges the normalization premise for Vᵍ∩T and the last model premise
of line alignment. The only remaining inputs to alignment are the preceding
intersection and global corank assertions, proved by the point-model branch.
The full SL₃ and Sp₄ markings, including q=4, are retained.
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

include F₀ in
theorem plane_action_rank_bound
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ normalizer (L : Set G)) :
    PlaneActionRankBound (E := E) := by
  intro A hAT hA
  let c := F₀.action.coordinates
  let P := F₀.flag.space 1
  have hp : c.preimage P = E.V₂ := by
    change D.centralQuotientPreimage _ = D.centralQuotientPreimage E.plane
    rw [F₀.plane_eq]
  let := D.elementary
  let : IsElementaryAbelian 2 E.V₂ :=
    IsElementaryAbelian.of_le (D.centralQuotientPreimage_le E.plane)
  let := hA
  have hAN := hAT.trans (sylow_normalizes_plane F₀)
  let I := inducedAutomizer E.V₂ A
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary E.V₂ A hAN
  let j : E.V₂ →* V := inclusion (D.centralQuotientPreimage_le E.plane)
  let f : Additive E.V₂ →+ P := {
    toFun v := ⟨(c.projection (j v.toMul)).toAdd,
      (c.mem_preimage P _).mp (hp.symm ▸ v.toMul.property)⟩
    map_zero' := by apply Subtype.ext; exact map_one c.projection
    map_add' u v := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (map_mul c.projection
        (inclusion (D.centralQuotientPreimage_le E.plane) u.toMul)
        (inclusion (D.centralQuotientPreimage_le E.plane) v.toMul)) }
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun v : V => (v : G)) (PointModels.projection_injective c hfixed
        (congrArg Subtype.val he))
    · intro x
      obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x.val)
      have hvP : v.val ∈ E.V₂ := by
        rw [← hp]
        exact (c.mem_preimage _ v).mpr (by change (c.projection v).toAdd ∈ P; rw [hv]; exact x.property)
      exact ⟨Additive.ofMul ⟨v, hvP⟩, Subtype.ext (congrArg Multiplicative.toAdd hv)⟩
  let e₀ : Additive E.V₂ ≃ₗ[ZMod 2] P := LinearEquiv.ofBijective (f.toZModLinearMap 2) hf
  let : Finite P := Finite.of_surjective f hf.surjective
  let e₁ : P ≃ₗ[E.input.field.Carrier] (Fin 2 → E.input.field.Carrier) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F₀.flag.dimension]; simp)
  let e := e₀.trans (e₁.restrictScalars (ZMod 2))
  let τ := (automizerRepresentation E.V₂).comp I.subtype
  let ρ : Representation (ZMod 2) I (Fin 2 → E.input.field.Carrier) :=
    e.conjRingEquiv.toMonoidHom.comp τ
  have hρ (i : I) (v : Additive E.V₂) : ρ i (e v) = e (τ i v) := by
    change e (τ i (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  have hfaith : Function.Injective ρ := by
    intro a b he
    apply Subtype.ext
    apply automizerRepresentation_injective E.V₂
    apply LinearMap.ext
    intro v
    apply e.injective
    exact (hρ a v).symm.trans ((LinearMap.congr_fun he (e v)).trans (hρ b v))
  have hsemi (i : I) : ∃ σ : E.input.field.Carrier ≃+* E.input.field.Carrier,
      ∀ t v, ρ i (t • v) = σ t • ρ i v := by
    obtain ⟨a, ha, hai⟩ := i.property
    have haA : (a : G) ∈ A := ha
    let aT : T := ⟨a, hAT haA⟩
    let μ := c.conjugationAction D.sylow_normalizes_component E.input.sylow_normalizes
    obtain ⟨σ, hσ⟩ := sylow_semilinear F₀ hNV aT
    have haP (v : P) : μ aT v ∈ P :=
      (c.normalizes_preimage_iff D.sylow_normalizes_component E.input.sylow_normalizes P).mp
        (F₀.flag.invariant 1) aT v v.property
    let μP : P → P := fun v => ⟨μ aT v, haP v⟩
    have hact (v : Additive E.V₂) : e₀ (τ i v) = μP (e₀ v) := by
      apply Subtype.ext
      change (c.projection (j (τ i v).toMul)).toAdd =
        c.conjugationAction D.sylow_normalizes_component E.input.sylow_normalizes aT
          (c.projection (j v.toMul)).toAdd
      rw [c.conjugationAction_projection]
      congr 2
      apply Subtype.ext
      change ((i.val.val) v.toMul).val = _
      rw [← hai]
      rfl
    have hcoords (x : P) : ρ i (e₁ x) = e₁ (μP x) := by
      obtain ⟨v, rfl⟩ := e₀.surjective x
      exact (hρ i v).trans (congrArg e₁ (hact v))
    refine ⟨σ, ?_⟩
    intro t v
    obtain ⟨x, rfl⟩ := e₁.surjective v
    rw [← e₁.map_smul, hcoords, hcoords, ← e₁.map_smul]
    apply congrArg e₁
    apply Subtype.ext
    exact hσ t x
  have hc := PlaneRank.elementary_semilinear_card_le ρ hfaith hsemi
    (⊤ : Subgroup I) (IsElementaryAbelian.of_injective (⊤ : Subgroup I).subtype Subtype.val_injective)
  rw [Subgroup.card_top, E.input.field.card_eq] at hc
  exact (Nat.log_mono_right (b := 2) hc).trans_eq (Nat.log_pow Nat.one_lt_two _)


/-- The literal corank-one intersection normalizes the original conjugate module;
the semilinear plane rank is supplied by the marked action itself. -/
theorem plane_normalizes_of_marking
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ normalizer (L : Set G)) (g : G)
    (hr : (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V)
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)) ≤ 1) :
    E.V₂ ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G) : Subgroup G) :=
    IsElementaryAbelian.of_le (show V.map (MulAut.conj g).toMonoidHom ⊓
      (T : Subgroup G) ≤ V.map (MulAut.conj g).toMonoidHom from inf_le_left)
  exact plane_normalizes F₀ g hr hcor
    (plane_action_rank_bound F₀ hfixed hNV _ inf_le_right inferInstance)

/-- Full source line alignment, retaining only the preceding intersection
and global corank conclusions of 11.5.3(1--2). -/
theorem source_lineAlignment
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (hr : (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V) :
    Nonabelian.LineAlignment E :=
  of_plane_rank F₀ hfixed hNV hintersection hr (plane_action_rank_bound F₀ hfixed hNV)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
