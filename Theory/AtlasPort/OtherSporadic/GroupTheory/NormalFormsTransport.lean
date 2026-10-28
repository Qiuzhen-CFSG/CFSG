/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/NormalFormsTransport.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# NormalFormsTransport

Normal-subgroup and small-action obstructions transport through group equivalences.
The proofs use subgroup transport and preservation of finite cardinality.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/NormalFormsTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H]

theorem normal_forms_transport (e : G ≃* H) (V : Subgroup H)
    (forms : ∀ W : Subgroup H, W.Normal → W = ⊥ ∨ W = V ∨ W = ⊤)
    (W : Subgroup G) (hW : W.Normal) :
    W = ⊥ ∨ W = V.comap e.toMonoidHom ∨ W = ⊤ := by
  have hnormal := hW.map e.toMonoidHom e.surjective
  rcases forms (W.map e.toMonoidHom) hnormal with hb | hv | ht
  · left
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using hb
  · right; left
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
    exact hv
  · right; right
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using ht

theorem card_comap_equiv (e : G ≃* H) (V : Subgroup H) :
    Nat.card (V.comap e.toMonoidHom) = Nat.card V := by
  have h := Nat.card_congr ((V.comap e.toMonoidHom).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv
  rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at h

theorem no_injective_perm_transport (e : G ≃* H) (X : Type*)
    (hH : ∀ ρ : H →* Equiv.Perm X, ¬ Function.Injective ρ)
    (ρ : G →* Equiv.Perm X) : ¬ Function.Injective ρ := by
  intro hρ
  exact hH (ρ.comp e.symm.toMonoidHom) (hρ.comp e.symm.injective)

end Atlas.GroupTheory
