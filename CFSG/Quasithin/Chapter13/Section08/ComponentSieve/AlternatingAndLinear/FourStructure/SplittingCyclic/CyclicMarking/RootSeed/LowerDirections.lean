module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed.Frames
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic

/-!
# Lower root directions from a natural or dual factor

A lower subrepresentation identified with the natural binary four-space or its
contragredient supplies the alternatives in `HasLowerRootDirections`. We absorb
the arbitrary flag basis into the actual lower intertwiner. In natural coordinates,
the basis vector e₀ is a nonzero simple-root displacement fixed by the central
and cross roots. In dual coordinates, the functionals q₁, q₃ and q₂ give the
lower direction and its two shear displacements. Evaluating at e₂ proves the
last direction lies outside the required
span; the coefficient of the external vector vanishes because it is outside the
lower submodule.

This realizes the lower-factor input to the central-root argument; the seed input
and the source chief-factor classification are supplied separately.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
open Representation BinaryLinear.MiddleParabolic

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem natural_embedding (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* BinaryLinear.GL V) (c : BinaryLinear.GL V) (e : W.toSubmodule ≃ₗ[ZMod 2] V)
    (he : ∀ g u, e (W.toRepresentation g u) = eH g (e u)) :
    ∃ f : V →ₗ[ZMod 2] U, Function.Injective f ∧
      (∀ u, f u ∈ W.toSubmodule) ∧
      ∀ g u, ρ (flagPullback eH c g) (f u) = f (g u) := by
  let d := c.trans e.symm
  let f := W.toSubmodule.subtype.comp d.toLinearMap
  refine ⟨f, Subtype.val_injective.comp d.injective, fun u => (d u).property, ?_⟩
  intro g u
  change (W.toRepresentation (flagPullback eH c g) (d u)).val = (d (g u)).val
  apply congrArg Subtype.val
  apply e.injective
  rw [he]
  simp [d, flagPullback, MulAut.conj_apply, LinearEquiv.mul_apply]

private theorem dual_embedding (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* BinaryLinear.GL V) (c : BinaryLinear.GL V)
    (e : W.toSubmodule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (he : ∀ g u, e (W.toRepresentation g u) = (ChiefFactors.naturalAction eH).dual g (e u)) :
    ∃ f : Module.Dual (ZMod 2) V →ₗ[ZMod 2] U, Function.Injective f ∧
      (∀ u, f u ∈ W.toSubmodule) ∧
      ∀ g u, ρ (flagPullback eH c g) (f u) = f (g.symm.dualMap u) := by
  let d := c.symm.dualMap.trans e.symm
  let f := W.toSubmodule.subtype.comp d.toLinearMap
  refine ⟨f, Subtype.val_injective.comp d.injective, fun u => (d u).property, ?_⟩
  intro g u
  change (W.toRepresentation (flagPullback eH c g) (d u)).val = (d (g.symm.dualMap u)).val
  apply congrArg Subtype.val
  apply e.injective
  rw [he]
  simp only [d, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro x
  change u (c.symm (eH (flagPullback eH c g)⁻¹ x)) = u (g.symm (c.symm x))
  simp [flagPullback, MulAut.conj_apply, LinearEquiv.mul_apply]

private theorem outside_lower_line (W : Submodule (ZMod 2) U) {v w : U}
    (hv : v ∉ W) (hw : w ∈ W) : v ∉ Submodule.span (ZMod 2) {w} := by
  intro h
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
  exact hv (W.smul_mem a hw)

private theorem natural_directions (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (eH : H ≃* BinaryLinear.GL V) (c : BinaryLinear.GL V)
    (hW : ChiefFactors.IsNatural W.toRepresentation eH) (v : U) (hv : v ∉ W.toSubmodule) :
    HasLowerRootDirections ρ (flagPullback eH c) v := by
  obtain ⟨e, he⟩ := hW
  obtain ⟨f, hf, hfW, hact⟩ := natural_embedding ρ W eH c e he
  let p : Fin 4 → V := fun i => Pi.single i 1
  have hx : actor 1 (p 1) = p 1 + p 0 := by
    ext i
    fin_cases i <;> simp [p, actorFun]
  have hz : centralRoot (p 0) = p 0 := by
    ext i
    fin_cases i <;> simp [p, centralRoot_apply]
  have ht : actor 3 (p 0) = p 0 := by
    ext i
    fin_cases i <;> simp [p, actorFun]
  refine ⟨f (p 0), ?_, ?_, outside_lower_line W.toSubmodule hv (hfW _), ?_, Or.inl ?_⟩
  · refine ⟨f (p 1), ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, hact, hx, map_add, add_sub_cancel_left]
  · intro h
    have hh : p 0 = 0 := hf (by simpa using h)
    have := congrFun hh 0
    simp [p] at this
  · rw [hact, hz]
  · rw [hact, ht]

private theorem dual_directions (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (eH : H ≃* BinaryLinear.GL V) (c : BinaryLinear.GL V)
    (e : W.toSubmodule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (he : ∀ g u, e (W.toRepresentation g u) = (ChiefFactors.naturalAction eH).dual g (e u))
    (v : U) (hv : v ∉ W.toSubmodule) :
    HasLowerRootDirections ρ (flagPullback eH c) v := by
  obtain ⟨f, hf, hfW, hact⟩ := dual_embedding ρ W eH c e he
  let q : Fin 4 → Module.Dual (ZMod 2) V := fun i => LinearMap.proj i
  have hx : (actor 1).symm.dualMap (q 0) = q 0 + q 1 := by
    apply LinearMap.ext
    intro u
    change actor 1 u 0 = u 0 + u 1
    rfl
  have hz : centralRoot.symm.dualMap (q 1) = q 1 := by
    apply LinearMap.ext
    intro u
    change (u + u 3 • (Pi.single 0 1 : V)) 1 = u 1
    simp
  have ht : (actor 3).symm.dualMap (q 1) = q 1 + q 3 := by
    apply LinearMap.ext
    intro u
    change actor 3 u 1 = u 1 + u 3
    rfl
  have hr : (actor 5).symm.dualMap (q 1) = q 1 + q 2 := by
    apply LinearMap.ext
    intro u
    change actor 5 u 1 = u 1 + u 2
    rfl
  have hra : (actor 5).symm.dualMap (q 3) = q 3 := by
    apply LinearMap.ext
    intro u
    change actor 5 u 3 = u 3
    rfl
  refine ⟨f (q 1), ?_, ?_, outside_lower_line W.toSubmodule hv (hfW _), ?_, Or.inr ?_⟩
  · refine ⟨f (q 0), ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, hact, hx, map_add, add_sub_cancel_left]
  · intro h
    have hh : q 1 = 0 := hf (by simpa using h)
    have := congrArg (fun l : Module.Dual (ZMod 2) V => l (Pi.single 1 1)) hh
    simp [q] at this
  · rw [hact, hz]
  · refine ⟨f (q 3), f (q 2), ?_, ?_, ?_, ?_⟩
    · rw [hact, ht, map_add]
    · rw [hact, hr, map_add]
    · rw [hact, hra]
    · intro hb
      obtain ⟨α, β, γ, hh⟩ := Submodule.mem_span_triple.mp hb
      have hα : α = 0 := by
        by_contra hn
        apply hv
        apply (W.toSubmodule.smul_mem_iff hn).mp
        have heq : α • v = f (q 2) - β • f (q 1) - γ • f (q 3) := by
          rw [← hh]
          abel
        rw [heq]
        exact W.toSubmodule.sub_mem
          (W.toSubmodule.sub_mem (hfW _) (W.toSubmodule.smul_mem _ (hfW _)))
          (W.toSubmodule.smul_mem _ (hfW _))
      rw [hα, zero_smul, zero_add, ← map_smul, ← map_smul, ← map_add] at hh
      have hcoord := congrArg (fun l : Module.Dual (ZMod 2) V => l (Pi.single 2 1)) (hf hh)
      simp [q] at hcoord

/-- A compatible natural or contragredient lower factor supplies the root directions
for every adapted flag basis and every vector outside that factor. -/
theorem hasLowerRootDirections_of_isNaturalOrDual (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (eH : H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hW : ChiefFactors.IsNaturalOrDual W.toRepresentation eH)
    (c : BinaryLinear.GL ChiefFactors.NaturalSpace)
    (v : U) (hv : v ∉ W.toSubmodule) :
    HasLowerRootDirections ρ (flagPullback eH c) v := by
  rcases hW with hW | ⟨e, he⟩
  · exact natural_directions ρ W eH c hW v hv
  · exact dual_directions ρ W eH c e he v hv

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
