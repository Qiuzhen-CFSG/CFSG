module
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.DualBounds
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Natural and dual sections rule out binary SL₃(2) offenders

A natural submodule and a surjective dual quotient have combined fixed
codimension greater than the rank of every nontrivial elementary actor.
The same holds when the dual quotient is initially defined only on a
second invariant summand spanning the module with the natural submodule.
Irreducibility and the inequivalence of the natural and dual modules
make the quotient vanish on the intersection, so it extends to the sum.
No splitting or disjointness assumption is used.

Source: Aschbacher--Smith, B.5.6 and its application in 14.3.29(2),
printed pp.105 and1002, refs/quasithin.pdf. The numerical obstruction
reuses the intrinsic binary SL₃(2) constituent budget.
-/

public noncomputable section
open Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDualSections
variable {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup N] [Module (ZMod 2) N]
  (σ : Representation (ZMod 2) Group M) (τ : Representation (ZMod 2) Group N)

private theorem codim_injection [FiniteDimensional (ZMod 2) N]
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) (A : Subgroup Group) :
    fixedCodim σ A ≤ fixedCodim τ A := by
  let e := LinearEquiv.ofInjective f.toLinearMap hf
  have he : fixedCodim σ A = fixedCodim f.range.toRepresentation A := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant σ
      f.range.toRepresentation (MonoidHom.id Group) e
      (fun g v => Subtype.ext (LinearMap.congr_fun (f.isIntertwining' g) v)) A
  rw [he]
  exact fixedCodim_subrepresentation_le τ f.range A

/-- A natural submodule and a dual quotient exceed every elementary actor's budget. -/
theorem not_ff [FiniteDimensional (ZMod 2) M]
    (i : W.IntertwiningMap σ) (hi : Function.Injective i)
    (p : σ.IntertwiningMap W.dual) (hp : Function.Surjective p) :
    ¬ IsFFModule σ := by
  have hzero := NaturalDual.natural_dual_zero (p.comp i)
  have hpi (v : Vector) : p (i v) = 0 :=
    congrArg (fun f : W.IntertwiningMap W.dual => f v) hzero
  let j : W.IntertwiningMap p.ker.toRepresentation :=
    ⟨i.toLinearMap.codRestrict p.ker.toSubmodule hpi,
      fun g => LinearMap.ext (fun v => Subtype.ext (LinearMap.congr_fun (i.isIntertwining' g) v))⟩
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  let q := p.ker.toSubmodule.liftQ p.toLinearMap le_rfl
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨p.ker.toSubmodule.mkQ x, rfl⟩
  have he (g : Group) (x : M ⧸ p.ker.toSubmodule) :
      q (p.ker.quotientRepresentation g x) = W.dual g (q x) := by
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact LinearMap.congr_fun (p.isIntertwining' g) x
  rintro ⟨A,hA⟩
  have hnat := codim_injection W p.ker.toRepresentation j hj A
  have hdual := fixedCodim_le_of_equivariant_surjection p.ker.quotientRepresentation W.dual q hq he A
  have hsum := fixedCodim_quotient_add_subrepresentation_le σ p.ker A
  have hstrict := ResidualFFForms.ConstituentBudget.rank_lt_natural_add_dual_fixedCodim A hA.1
  have hb := hA.2
  omega

/-- A dual quotient of a spanning invariant summand extends across an added natural submodule. -/
theorem extend_dual_quotient
    (i : W.IntertwiningMap σ) (j : τ.IntertwiningMap σ) (hj : Function.Injective j)
    (p : τ.IntertwiningMap W.dual) (hp : Function.Surjective p)
    (hspan : Function.Surjective (i.toLinearMap.coprod j.toLinearMap)) :
    ∃ q : σ.IntertwiningMap W.dual, Function.Surjective q := by
  let I : Subrepresentation W := {
    toSubmodule := j.range.toSubmodule.comap i.toLinearMap
    apply_mem_toSubmodule g := by
      intro v hv
      change i (W g v) ∈ j.range.toSubmodule
      rw [i.isIntertwining]
      exact j.range.apply_mem_toSubmodule g hv }
  let := IrreducibleCatalogue.natural_irreducible
  have hkill (v : Vector) (w : N) (h : i v = j w) : p w = 0 := by
    rcases eq_bot_or_eq_top I with hI | hI
    · have hv : v ∈ I := ⟨w,h.symm⟩
      rw [hI] at hv
      have hv0 : v = 0 := hv
      rw [hv0, map_zero] at h
      have hw : w = 0 := hj (h.symm.trans (map_zero j).symm)
      rw [hw,map_zero]
    · let e := LinearEquiv.ofInjective j.toLinearMap hj
      let f : Vector →ₗ[ZMod 2] N := e.symm.toLinearMap.comp
        (i.toLinearMap.codRestrict j.range.toSubmodule (fun v => by
          change v ∈ I
          rw [hI]
          trivial))
      have hf (v : Vector) : j (f v) = i v :=
        congrArg Subtype.val (e.apply_symm_apply _)
      let t : W.IntertwiningMap τ := ⟨f, by
        intro g
        apply LinearMap.ext
        intro v
        apply hj
        change j (f (W g v)) = j (τ g (f v))
        rw [hf, j.isIntertwining, hf, i.isIntertwining]⟩
      have hz := NaturalDual.natural_dual_zero (p.comp t)
      have hw : f v = w := hj ((hf v).trans h)
      have hh := congrArg (fun t : W.IntertwiningMap W.dual => t v) hz
      change p (f v) = 0 at hh
      rwa [hw] at hh
  let s := i.toLinearMap.coprod j.toLinearMap
  let t := p.toLinearMap.comp (LinearMap.snd (ZMod 2) Vector N)
  have hk : s.ker ≤ t.ker := by
    rintro ⟨v,w⟩ h
    change i v + j w = 0 at h
    exact hkill (-v) w (by rw [map_neg]; exact neg_eq_iff_add_eq_zero.mpr h)
  let e := s.quotKerEquivOfSurjective hspan
  let q := (s.ker.liftQ t hk).comp e.symm.toLinearMap
  have hq (v : Vector) (w : N) : q (i v + j w) = p w := by
    change (s.ker.liftQ t hk) (e.symm (s (v,w))) = _
    have he : e (s.ker.mkQ (v,w)) = s (v,w) := rfl
    rw [←he,e.symm_apply_apply]
    rfl
  refine ⟨⟨q, ?_⟩, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    obtain ⟨⟨v,w⟩,rfl⟩ := hspan x
    change q (σ g (i v + j w)) = W.dual g (q (i v + j w))
    rw [map_add, ←i.isIntertwining, ←j.isIntertwining, hq, hq, p.isIntertwining]
  · intro y
    obtain ⟨w,rfl⟩ := hp y
    exact ⟨i 0 + j w,hq 0 w⟩

/-- No splitting assumption is needed for the sum of the natural seed and orbit span. -/
theorem not_ff_of_spanning_sum [FiniteDimensional (ZMod 2) M]
    (i : W.IntertwiningMap σ) (hi : Function.Injective i)
    (j : τ.IntertwiningMap σ) (hj : Function.Injective j)
    (p : τ.IntertwiningMap W.dual) (hp : Function.Surjective p)
    (hspan : Function.Surjective (i.toLinearMap.coprod j.toLinearMap)) : ¬ IsFFModule σ := by
  obtain ⟨q,hq⟩ := extend_dual_quotient σ τ i j hj p hp hspan
  exact not_ff σ i hi q hq

end BinaryLinearThree.NaturalDualSections
