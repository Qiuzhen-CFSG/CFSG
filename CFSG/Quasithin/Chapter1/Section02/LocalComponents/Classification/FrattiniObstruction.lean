module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.PGroup.HomocyclicFrattini
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# An obstruction to the extra center–Frattini assertion

If an element inverts a subgroup `C₁₂₁ × C₁₂₁`, the Frattini subgroup of that
subgroup cannot be central: the eleventh power of a coordinate generator is
nontrivial and inverted. Thus a generalized Fitting subgroup of this shape,
inverted by some group element, contradicts the equality in 1.2.1(4d).
The prime eleven satisfies the displayed A.3.6(4) congruence, and exponent 121
is permitted by its homocyclic alternative.

This configuration also excludes all four alternatives of `Proposition121Four`:
a quasisimple group cannot have abelian generalized Fitting subgroup, and the
natural alternative would force its prime parameter to equal 121 by cardinality.

This proves an obstruction for a precise configuration. It does **not** assert
existence of an SQTK C-component with that configuration, or refute the full
QTKE-local statement. That source-level question remains with the assembly
owner; one cannot infer the center equality from the Sylow shapes alone.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.6(4), pp.43–45,
and the additional equality printed in Proposition 1.2.1(4d), p.504.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02

/-- Inversion on the allowed higher-exponent homocyclic group prevents its
Frattini subgroup from being central. -/
theorem frattini_not_central_of_homocyclic_121_inversion
    {G : Type*} [Group G] (N : Subgroup G)
    (e : N ≃* StandardHomocyclicCover (Fin 2) (11 ^ 2))
    (t : G) (hinv : ∀ x : N, t * (x : G) * t⁻¹ = (x : G)⁻¹) :
    ¬ (frattini N).map N.subtype ≤ center G := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : Finite N := Finite.of_injective e e.injective
  let : Fact (IsPGroup 11 N) :=
    ⟨(standardHomocyclicCover_isPGroup (Fin 2) 11 2).of_equiv e.symm⟩
  let x : N := e.symm (Multiplicative.ofAdd (fun _ : Fin 2 => (1 : ZMod (11 ^ 2))))
  have hx : x ^ 11 ∈ frattini N := pth_power_mem_frattini_of_isPGroup (p := 11) x
  intro h
  have hz : ((x ^ 11 : N) : G) ∈ center G := h (mem_map.mpr ⟨x ^ 11, hx, rfl⟩)
  have hc : t * ((x ^ 11 : N) : G) * t⁻¹ = ((x ^ 11 : N) : G) := by
    rw [mem_center_iff.mp hz t, mul_assoc, mul_inv_cancel, mul_one]
  have heq : x ^ 11 = (x ^ 11)⁻¹ := Subtype.ext (hc.symm.trans (hinv (x ^ 11)))
  have he := congrArg (fun y => Multiplicative.toAdd (e y) (0 : Fin 2)) heq
  norm_num [map_inv, map_pow, x] at he
  exact (by decide : (11 : ZMod (11 ^ 2)) ≠ -11) he

/-- A precise configuration incompatible with the additional Chapter 1 clause. -/
theorem not_centerFrattini_of_homocyclic_121_inversion
    {G : Type*} [Group G]
    (e : Theory.GroupTheory.generalizedFitting G ≃*
      StandardHomocyclicCover (Fin 2) (11 ^ 2))
    (t : G) (hinv : ∀ x : Theory.GroupTheory.generalizedFitting G,
      t * (x : G) * t⁻¹ = (x : G)⁻¹) : ¬ CenterFrattini G := by
  intro h
  exact frattini_not_central_of_homocyclic_121_inversion _ e t hinv h.symm.le

private theorem not_quasisimple_of_homocyclic_121_fitting {G : Type*} [Group G]
    (e : Theory.GroupTheory.generalizedFitting G ≃*
      StandardHomocyclicCover (Fin 2) (11 ^ 2)) :
    ¬ Theory.GroupTheory.IsQuasisimple G := by
  intro hG
  let := hG
  have htop : Theory.GroupTheory.generalizedFitting G = ⊤ := top_unique
    (Theory.GroupTheory.component_le_generalizedFitting G ⊤
      ⟨IsSubnormal.top, Theory.GroupTheory.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩)
  let : Group.IsSolvable (Theory.GroupTheory.generalizedFitting G) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable (⊤ : Subgroup G) := htop ▸ inferInstance
  let : Group.IsSolvable G := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom)
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.injective
  let := hG.simple
  let : Nontrivial G := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center G))
  exact Group.IsPerfect.not_isSolvable G inferInstance

private theorem not_natural_of_homocyclic_121_fitting {G : Type*} [Group G] [Finite G]
    (e : Theory.GroupTheory.generalizedFitting G ≃*
      StandardHomocyclicCover (Fin 2) (11 ^ 2))
    {p : ℕ} (hp : p.Prime) :
    ¬ LocalModels.NaturalSL2Action G (Theory.GroupTheory.generalizedFitting G) p := by
  rintro ⟨F, hF, hfin, hcard, v, _, _⟩
  let : Fintype F := Fintype.ofFinite F
  have h1 : Nat.card (Theory.GroupTheory.generalizedFitting G) = 121 ^ 2 :=
    (Nat.card_congr e.toEquiv).trans
      (by norm_num [StandardHomocyclicCover, Nat.card_eq_fintype_card])
  have h2 : Nat.card (Theory.GroupTheory.generalizedFitting G) = p ^ 2 := by
    calc
      _ = Nat.card (Multiplicative (Fin 2 → F)) := Nat.card_congr v.toEquiv
      _ = Nat.card F ^ 2 := by simp [Nat.card_eq_fintype_card]
      _ = p ^ 2 := by rw [hcard]
  have heq : p = 121 := Nat.pow_left_injective (by decide : 2 ≠ 0) (h2.symm.trans h1)
  exact (by decide : ¬ Nat.Prime 121) (heq ▸ hp)

/-- The allowed higher-exponent homocyclic shape, together with inversion,
excludes every Chapter 1 alternative. Existence under the full SQTK/local
hypotheses is a separate obligation; this is not a source counterexample. -/
theorem not_proposition121Four_of_homocyclic_121_inversion
    {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (e : Theory.GroupTheory.generalizedFitting K ≃*
      StandardHomocyclicCover (Fin 2) (11 ^ 2))
    (t : K) (hinv : ∀ x : Theory.GroupTheory.generalizedFitting K,
      t * (x : K) * t⁻¹ = (x : K)⁻¹) : ¬ Proposition121Four K := by
  intro h
  cases h with
  | simple hc _ _ => exact not_quasisimple_of_homocyclic_121_fitting e hc.2
  | cover hc _ _ => exact not_quasisimple_of_homocyclic_121_fitting e hc.2
  | natural p hp _ ha => exact not_natural_of_homocyclic_121_fitting e hp ha
  | nilpotent _ hz _ _ => exact not_centerFrattini_of_homocyclic_121_inversion e t hinv hz

end CFSG.Quasithin.Chapter1.Section02
