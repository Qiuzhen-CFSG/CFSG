module
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.Representation.FirstCohomologyConjugationSplitting
public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Cohomology of the binary natural-plus-dual module

The existing elementary-matrix calculation gives vanishing for the natural
module in dimensions at least four. Inverse transpose transports it to the
dual, and the direct-sum theorem gives vanishing for their sum. The canonical
nondegenerate polar pairing identifies that sum with its dual. The same
transports show that both modules have zero fixed space in dimension at
least two.

Source: Aschbacher--Smith I.1.6(6), printed p.408, and the H.9 natural-plus-dual
action. `NormalFirstCohomology` applies these facts to actual normal actors.
-/

@[expose] public noncomputable section
open BinaryLinear.OuterCyclic
open Representation
open Representation.OneCohomology
namespace BinaryNaturalDual

def linearNatural (n : ℕ) : Representation (ZMod 2) (LinearGroup n) (BinaryLinear.OuterCyclic.Space n) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem linearNatural_H1_subsingleton {n : ℕ} (hn : 4 ≤ n) :
    Subsingleton (H1 (linearNatural n)) := by
  let := SLHigherNatural.H1_subsingleton_of_four_le (K := ZMod 2) hn
  let e := H1Congr (specialLinearNatural (k := ZMod 2) n) (linearNatural n)
    (slEquivLinear n) (LinearEquiv.refl (ZMod 2) _)
    (fun g v => (slEquivLinear_apply n g v).symm)
  exact e.symm.injective.subsingleton

theorem linearNatural_dual_H1_subsingleton {n : ℕ} (hn : 4 ≤ n) :
    Subsingleton (H1 (linearNatural n).dual) := by
  let := linearNatural_H1_subsingleton hn
  have he (g : LinearGroup n) (v : BinaryLinear.OuterCyclic.Space n) :
      dotProductEquiv (ZMod 2) (Fin n) (linearNatural n g v) =
        (linearNatural n).dual (graphLinear n g) (dotProductEquiv (ZMod 2) (Fin n) v) := by
    apply LinearMap.ext
    intro w
    change dotProduct (g v) w = dotProduct v ((graphLinear n g).symm w)
    have h := graphLinear_dotProduct g ((graphLinear n g).symm w) v
    simpa only [LinearEquiv.apply_symm_apply, dotProduct_comm] using h
  let e := H1Congr (linearNatural n) (linearNatural n).dual (graphLinear n)
    (dotProductEquiv (ZMod 2) (Fin n)) he
  exact e.symm.injective.subsingleton

theorem naturalDual_H1_subsingleton {n : ℕ} (hn : 4 ≤ n) :
    Subsingleton (H1 (naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n))) := by
  let := linearNatural_H1_subsingleton hn
  let := linearNatural_dual_H1_subsingleton hn
  have he : naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n) =
      (linearNatural n).prod (linearNatural n).dual := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact naturalDualRepresentation_apply g v
  rw [he]
  exact H1_prod_subsingleton _ _

theorem naturalDual_dual_H1_subsingleton {n : ℕ} (hn : 4 ≤ n) :
    Subsingleton (H1 (naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n)).dual) := by
  let ρ := naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n)
  let := naturalDual_H1_subsingleton hn
  let e := LinearMap.BilinForm.toDual (quadratic (V := BinaryLinear.OuterCyclic.Space n)).polarBilin polar_nondegenerate
  have he (g : LinearGroup n) (v : CoordinateSpace n) : e (ρ g v) = ρ.dual g (e v) := by
    apply LinearMap.ext
    intro w
    change quadratic.polarBilin (ρ g v) w = quadratic.polarBilin v (ρ g⁻¹ w)
    rw [polar_apply, polar_apply]
    simp only [ρ, naturalDualRepresentation_apply, LinearEquiv.coe_inv]
    change v.2 (g.symm w.1) + w.2 (g v.1) =
      v.2 (g.symm w.1) + w.2 (g v.1)
    rfl
  let eH := H1Congr ρ ρ.dual (MulEquiv.refl _) e he
  exact eH.symm.injective.subsingleton

theorem linearNatural_fixed_eq_bot {n : ℕ} (hn : 2 ≤ n) :
    fixed (linearNatural n) = ⊥ := by
  apply bot_unique
  intro v hv
  have hh : v ∈ fixed (specialLinearNatural (k := ZMod 2) n) := by
    intro g
    exact hv (slEquivLinear n g)
  simpa only [SLHigherNatural.fixed_eq_bot hn, Submodule.mem_bot] using hh

theorem naturalDual_fixed_eq_bot {n : ℕ} (hn : 2 ≤ n) :
    fixed (naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n)) = ⊥ := by
  apply bot_unique
  intro v hv
  have hfst : v.1 = 0 := by
    have hh : v.1 ∈ fixed (linearNatural n) := by
      intro g
      have he := hv g
      rw [naturalDualRepresentation_apply] at he
      exact congrArg Prod.fst he
    simpa only [linearNatural_fixed_eq_bot hn, Submodule.mem_bot] using hh
  have hsnd : v.2 = 0 := by
    let e := dotProductEquiv (ZMod 2) (Fin n)
    have hh : e.symm v.2 ∈ fixed (linearNatural n) := by
      intro g
      apply e.injective
      rw [e.apply_symm_apply]
      apply LinearMap.ext
      intro w
      change dotProduct (g (e.symm v.2)) w = v.2 w
      have he0 := hv (graphLinear n g)
      rw [naturalDualRepresentation_apply] at he0
      have he := congrArg (fun q => q.2 w) he0
      change v.2 ((graphLinear n g).symm w) = v.2 w at he
      have hd := graphLinear_dotProduct g ((graphLinear n g).symm w) (e.symm v.2)
      have hd' : dotProduct (g (e.symm v.2)) w =
          v.2 ((graphLinear n g).symm w) := by
        have hee := LinearMap.congr_fun (e.apply_symm_apply v.2) ((graphLinear n g).symm w)
        change dotProduct (e.symm v.2) ((graphLinear n g).symm w) = _ at hee
        rw [← hee]
        simpa only [LinearEquiv.apply_symm_apply, dotProduct_comm] using hd
      exact hd'.trans he
    have hh0 : e.symm v.2 = 0 := by
      simpa only [linearNatural_fixed_eq_bot hn, Submodule.mem_bot] using hh
    exact e.symm.injective (hh0.trans (map_zero e.symm).symm)
  exact Prod.ext hfst hsnd

theorem naturalDual_dual_fixed_eq_bot {n : ℕ} (hn : 2 ≤ n) :
    fixed (naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n)).dual = ⊥ := by
  let ρ := naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n)
  let e := LinearMap.BilinForm.toDual (quadratic (V := BinaryLinear.OuterCyclic.Space n)).polarBilin polar_nondegenerate
  have he (g : LinearGroup n) (v : CoordinateSpace n) : e (ρ g v) = ρ.dual g (e v) := by
    apply LinearMap.ext
    intro w
    change quadratic.polarBilin (ρ g v) w = quadratic.polarBilin v (ρ g⁻¹ w)
    rw [polar_apply, polar_apply]
    simp only [ρ, naturalDualRepresentation_apply, LinearEquiv.coe_inv]
    rfl
  apply bot_unique
  intro v hv
  have hh : e.symm v ∈ fixed ρ := by
    intro g
    apply e.injective
    rw [he,e.apply_symm_apply,hv]
  have hh0 : e.symm v = 0 := by
    simpa only [ρ,naturalDual_fixed_eq_bot hn,Submodule.mem_bot] using hh
  exact e.symm.injective (hh0.trans (map_zero e.symm).symm)

end BinaryNaturalDual
