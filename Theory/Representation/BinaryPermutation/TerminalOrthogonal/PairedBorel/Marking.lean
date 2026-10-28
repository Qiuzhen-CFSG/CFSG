module

public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Isometries
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.ElementaryConjugacy

/-!
# Compatible paired action and elementary subgroup markings

A faithful action preserving the quadratic form and the two orthogonal summands
lifts to the concrete swapped permutation model. The marked A₅ product maps
onto its actual base subgroup. The source splitting clause for an elementary
subgroup of order eight then permits a single base conjugation which sends
that subgroup to the standard elementary group and its specified swapping
element to the literal interchange. The same conjugation changes the vector
coordinates and places the standard generators in the original Sylow image.

The reconstructed factor equivalence retains the inclusion into the full model;
its inverse transports the two diagonal Klein generators into that same Sylow.
This discharges the model and Sylow marking inputs of the terminal Borel consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.11.2(12),
printed p.364/PDF p.375, and 12.8.13(7), printed p.856/PDF p.873.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.PairedBorel
open PairedFive

/-- The concrete action, retaining its quadratic isometry. -/
noncomputable def modelIsometry (g : Model) : form.IsometryEquiv form where
  toLinearEquiv := modelAction g
  map_app' := modelAction_form g

private lemma modelAction_conj_apply (g h : Model) (v : Space) :
    modelAction (MulAut.conj g h) (modelAction g v) = modelAction g (modelAction h v) := by
  simp only [MulAut.conj_apply, map_mul, map_inv, LinearEquiv.mul_apply,
    LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

private lemma right_ne_one_of_exchanges (g : Model)
    (h : ∀ v : Factor, (modelAction g (v, 0)).1 = 0) : g.right ≠ 1 := by
  intro hg
  have hz : factorPoint = 0 := (factorAction g.left.1).injective (by
    rw [map_zero]
    exact (by simpa only [modelAction_apply, if_pos hg] using h factorPoint :
      coreRepresentation (Fin 5) g.left.1 factorPoint = 0))
  exact point_ne_zero (Prod.ext hz hz)

variable {D : Type*} [Group D]

/-- Recognize the entire faithful block action and put the specified elementary
subgroup and swapping element in standard coordinates. The source splitting
clause is retained; the subgroup and Sylow markings are constructed. -/
lemma exists_standard_marking
    (φ : D →* (Space ≃ₗ[ZMod 2] Space)) (hφ : Function.Injective φ)
    (hq : ∀ d v, form (φ d v) = form v)
    (hs : ∀ d, PreservesSummandPair (φ d))
    (L : Subgroup D) (e : L ≃* Actor)
    (he : ∀ (l : L) v, φ l v = action (e l) v)
    (X : Subgroup D) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 8) (x : D) (hx : x ∈ X)
    (hswap : ∀ v : Factor, (φ x (v, 0)).1 = 0)
    (hsplit : X ≤ L ⊔ Subgroup.zpowers x)
    (Q : Sylow 2 D) (hXQ : X ≤ Q) :
    ∃ (t : S5 × S5) (r : D →* Model), Function.Injective r ∧
      (∀ d v, modelAction (r d) (modelAction (base t) v) =
        modelAction (base t) (φ d v)) ∧
      L.map r = pairedInclusion.range ∧ X.map r = elementary ∧
      r x = interchange ∧ elementary ≤ (Q : Subgroup D).map r := by
  let f := liftModelAction φ hq hs
  have hf : Function.Injective f := liftModelAction_injective φ hq hs hφ
  have heq (l : L) : f l = pairedInclusion (e l) := by
    apply modelAction_injective
    apply LinearEquiv.ext
    intro v
    change modelAction (liftModelAction φ hq hs l) v = _
    rw [modelAction_liftModelAction, modelAction_paired, he]
  have hL : L.map f = pairedInclusion.range := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact ⟨e ⟨l, hl⟩, (heq ⟨l, hl⟩).symm⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨e.symm a, (e.symm a).property, by rw [heq, e.apply_symm_apply]⟩
  let Y := X.map f
  have : IsElementaryAbelian 2 Y := IsElementaryAbelian.map f
  have hYcard : Nat.card Y = 8 := by
    rw [Subgroup.card_map_of_injective hf]
    exact hcard
  have hYsplit : Y ≤ pairedInclusion.range ⊔ Subgroup.zpowers (f x) := by
    have hh := Subgroup.map_mono (f := f) hsplit
    rwa [Subgroup.map_sup, hL, MonoidHom.map_zpowers] at hh
  have hxswap : (f x).right ≠ 1 := right_ne_one_of_exchanges _ (by
    intro v
    change (modelAction (liftModelAction φ hq hs x) (v, 0)).1 = 0
    rw [modelAction_liftModelAction]
    exact hswap v)
  obtain ⟨t, ht, hxt, hQt⟩ := exists_elementary_sylow_placement Q f Y hYcard
    (f x) ⟨x, hx, rfl⟩ hxswap hYsplit (Subgroup.map_mono hXQ)
  let r := (MulAut.conj (base t)).toMonoidHom.comp f
  refine ⟨t, r, (MulAut.conj _).injective.comp hf, ?_, ?_, ?_, hxt, ?_⟩
  · intro d v
    change modelAction (MulAut.conj (base t) (f d)) (modelAction (base t) v) = _
    rw [modelAction_conj_apply, modelAction_liftModelAction]
  · rw [show r = (MulAut.conj (base t)).toMonoidHom.comp f from rfl,
      ← Subgroup.map_map, hL]
    exact Subgroup.Normal.map_conj_eq _ _
  · rw [show r = (MulAut.conj (base t)).toMonoidHom.comp f from rfl,
      ← Subgroup.map_map]
    exact ht
  · rw [show r = (MulAut.conj (base t)).toMonoidHom.comp f from rfl,
      ← Subgroup.map_map]
    exact hQt

/-- The factor marking induced by the actual image of the paired subgroup. -/
noncomputable def pairedSubgroupEquiv (L : Subgroup D) (r : D →* Model)
    (hr : Function.Injective r) (hL : L.map r = pairedInclusion.range) : L ≃* Actor :=
  ((L.equivMapOfInjective r hr).trans (MulEquiv.subgroupCongr hL)).trans
    (MonoidHom.ofInjective pairedInclusion_injective).symm

/-- Both factor maps agree with the specified inclusion into the full model. -/
lemma pairedSubgroupEquiv_apply (L : Subgroup D) (r : D →* Model)
    (hr : Function.Injective r) (hL : L.map r = pairedInclusion.range) (l : L) :
    pairedInclusion (pairedSubgroupEquiv L r hr hL l) = r l := by
  exact congrArg Subtype.val ((MonoidHom.ofInjective pairedInclusion_injective).apply_symm_apply
    ((MulEquiv.subgroupCongr hL) (L.equivMapOfInjective r hr l)))

/-- Pull a model generator back into the original subgroup through this marking. -/
lemma pairedSubgroupEquiv_symm_mem (L : Subgroup D) (r : D →* Model)
    (hr : Function.Injective r) (hL : L.map r = pairedInclusion.range)
    (Q : Subgroup D) (a : Actor) (ha : pairedInclusion a ∈ Q.map r) :
    ((pairedSubgroupEquiv L r hr hL).symm a : D) ∈ Q := by
  obtain ⟨y, hy, he⟩ := ha
  have hy' : y = ((pairedSubgroupEquiv L r hr hL).symm a : D) := by
    apply hr
    rw [← pairedSubgroupEquiv_apply L r hr hL, MulEquiv.apply_symm_apply]
    exact he
  exact hy' ▸ hy

end BinaryPermutation.TerminalOrthogonal.PairedBorel
