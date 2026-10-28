module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/RootDerived.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.DerivedSubgroup
public import Theory.AtlasPort.LinearGroups.ReeG2.TorusCommutators
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem beta_mem_derivedAmbient (m : ℕ) (hp : Parameters F m) (b : F) :
    beta m b ∈ derivedAmbient m := by
  obtain ⟨l,hl⟩ := exists_betaCharacter_ne_one m hp
  let x := b / (betaCharacter m l - 1)
  have he := torus_beta_commutator m hp.cardinality l x
  have hx : (betaCharacter m l - 1)*x = b := mul_div_cancel₀ b (sub_ne_zero.mpr hl)
  rw [hx] at he
  have hh := commutator_mem_derivedAmbient m
    ((generated F m).inv_mem (torus_mem_generated m l))
    (root_mem_generated m hp.cardinality 0 x 0)
  rw [he] at hh
  simpa [rootElement] using hh

theorem gamma_mem_derivedAmbient (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (c : F) :
    gamma m c ∈ derivedAmbient m := by
  have he := torus_gamma_commutator m hcard (-1) c
  have hscalar : ((((-1 : Fˣ) : F)⁻¹ - 1)*c) = c := by
    norm_num
    linear_combination (norm := ring_nf) -(c) * (CharP.cast_eq_zero F 3)
  rw [hscalar] at he
  have hh := commutator_mem_derivedAmbient m
    ((generated F m).inv_mem (torus_mem_generated m (-1)))
    (root_mem_generated m hcard 0 0 c)
  rw [he] at hh
  simpa [rootElement] using hh

theorem torus_alpha_minus_one_commutator (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (a : F) :
    ⁅(torus m (-1 : Fˣ))⁻¹, rootElement m a 0 0⁆ =
      rootElement m a (a*(theta F m a)^3) (a^2*(theta F m a)^3) := by
  rw [commutatorElement_def, inv_inv, torus_conjugate_root m hcard,
    rootElement_inv m hcard, rootElement_mul m hcard]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  congr 1 <;> apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

theorem alpha_mem_derivedAmbient (m : ℕ) (hp : Parameters F m) (a : F) :
    alpha m a ∈ derivedAmbient m := by
  have hc := commutator_mem_derivedAmbient m
    ((generated F m).inv_mem (torus_mem_generated m (-1)))
    (root_mem_generated m hp.cardinality a 0 0)
  rw [torus_alpha_minus_one_commutator m hp.cardinality] at hc
  have hb := beta_mem_derivedAmbient m hp (a*(theta F m a)^3)
  have hg := gamma_mem_derivedAmbient m hp.cardinality (a^2*(theta F m a)^3)
  have hh := (derivedAmbient m).mul_mem hc ((derivedAmbient m).inv_mem
    ((derivedAmbient m).mul_mem hb hg))
  simpa [rootElement,mul_assoc] using hh

theorem root_mem_derivedAmbient (m : ℕ) (hp : Parameters F m) (a b c : F) :
    rootElement m a b c ∈ derivedAmbient m :=
  (derivedAmbient m).mul_mem ((derivedAmbient m).mul_mem
    (alpha_mem_derivedAmbient m hp a) (beta_mem_derivedAmbient m hp b))
    (gamma_mem_derivedAmbient m hp.cardinality c)

end Atlas.ReeG2
