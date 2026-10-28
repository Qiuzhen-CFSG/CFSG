module

public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.WeylAction
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Bruhat
public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry

/-!
# Solvable G₂ Sylow overgroups: exclusion of the nonidentity Weyl cells

Intersect a solvable overgroup of the positive roots with either full standard
parabolic. The existing rank-one refinements put both intersections in the
Borel. Thus neither opposite simple-root element can belong to the overgroup.
Every nonidentity Weyl representative conjugates a positive-root element to
one of those two elements; a torus factor does not change this obstruction,
since it normalizes the positive roots.

The concrete Bruhat factorization of the full split-octonion automorphism
group discharges the coverage premise in the final Borel and parabolic
containment theorems. No nontrivial two-core or restriction on odd primes is
assumed. The field hypothesis is exactly characteristic two and order greater
than two, so the argument includes F₄.

Source: Aschbacher–Smith, printed p.1144, the larger-field paragraph after
(k); the Bruhat route is GLS III, Theorems 2.3.5 and 2.6.7. The concrete
octonion and root formulas come from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.SolvableSylowPlacement

open Subgroup Atlas.SplitOctonion Explicit LieParabolicSetup SolvableParabolic

variable {F : Type*} [Field F]

private theorem negative_long_not_mem_borel :
    weylR * rootE (1 : F) * weylR⁻¹ ∉ borel := by
  intro h
  have hp := borel_le_shortPlaneStabilizer h
  have hz := hp.1 (basisVector 1) (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  simp [weylR, weylREquiv, weylRLinear, weylRApply,
    rootE, rootEEquiv, rootELinear, rootEApply, basisVector] at hz

private theorem negative_short_not_mem_borel :
    weylS * rootF (1 : F) * weylS⁻¹ ∉ borel := by
  intro h
  have hp := parabolic_le_pointStabilizer (borel_le_parabolic₂ h)
  obtain ⟨a, ha⟩ := (mem_pointStabilizer_iff _).mp hp
  have hz := congrArg (fun x : Carrier F => x 1) ha
  simp [weylS, weylSEquiv, weylSLinear, weylSApply,
    rootF, rootFEquiv, rootFLinear, rootFApply, basisVector] at hz

private theorem solvable_inf (H K : Subgroup (Model F)) (hH : Group.IsSolvable H) :
    Group.IsSolvable (H ⊓ K : Subgroup (Model F)) := by
  let : Group.IsSolvable H := hH
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)

variable [Finite F] [CharP F 2]

private theorem negative_long_not_mem (hq : 2 < Nat.card F)
    (H : Subgroup (Model F)) (hU : unipotent ≤ H) (hH : Group.IsSolvable H) :
    weylR * rootE (1 : F) * weylR⁻¹ ∉ H := by
  intro hg
  have hle : H ⊓ parabolic₂ ≤ borel := long_standard_le_borel hq _
    (le_inf hU (le_sup_left.trans borel_le_parabolic₂))
    (solvable_inf H parabolic₂ hH) inf_le_right
  apply negative_long_not_mem_borel (F := F)
  exact hle ⟨hg, parabolic₂.mul_mem
    (parabolic₂.mul_mem weylR_mem_parabolic (rootE_mem_parabolic 1))
    (parabolic₂.inv_mem weylR_mem_parabolic)⟩

private theorem negative_short_not_mem (hq : 2 < Nat.card F)
    (H : Subgroup (Model F)) (hU : unipotent ≤ H) (hH : Group.IsSolvable H) :
    weylS * rootF (1 : F) * weylS⁻¹ ∉ H := by
  intro hg
  have hle : H ⊓ parabolic₁ ≤ borel := short_standard_le_borel hq _
    (le_inf hU (le_sup_left.trans borel_le_parabolic₁))
    (solvable_inf H parabolic₁ hH) inf_le_right
  have hs : (weylS : Model F) ∈ parabolic₁ :=
    mem_sup_right (subset_closure (by simp))
  have hf : rootF (1 : F) ∈ parabolic₁ := borel_le_parabolic₁
    (mem_sup_left (subset_closure (by simp)))
  apply negative_short_not_mem_borel (F := F)
  exact hle ⟨hg, parabolic₁.mul_mem (parabolic₁.mul_mem hs hf) (parabolic₁.inv_mem hs)⟩

/-- A solvable overgroup of the positive roots contains no nonidentity Weyl
representative multiplied by an element of the actual split torus. -/
theorem weyl_index_eq_zero_of_solvable (hq : 2 < Nat.card F)
    (H : Subgroup (Model F)) (hU : unipotent ≤ H) (hH : Group.IsSolvable H)
    (i : Fin 12) (t : Model F) (ht : t ∈ splitTorus)
    (hwt : weylRep i * t ∈ H) : i = 0 := by
  by_contra hi
  obtain ⟨x, hx, he⟩ := exists_negative_simple_conjugate (F := F) i hi
  have hy : t⁻¹ * x * t ∈ unipotent := by
    simpa only [inv_inv] using torus_normalizes_unipotent (splitTorus.inv_mem ht) hx
  have hc : weylRep i * x * (weylRep i)⁻¹ ∈ H := by
    have hm := H.mul_mem (H.mul_mem hwt (hU hy)) (H.inv_mem hwt)
    have heq : (weylRep i * t) * (t⁻¹ * x * t) * (weylRep i * t)⁻¹ =
        weylRep i * x * (weylRep i)⁻¹ := by group
    rwa [heq] at hm
  rcases he with he | he
  · exact negative_long_not_mem hq H hU hH (he ▸ hc)
  · exact negative_short_not_mem hq H hU hH (he ▸ hc)

/-- Concrete Bruhat coverage, together with the proved root-cell exclusions,
puts every solvable overgroup of the full positive-root Sylow in the Borel. -/
theorem le_borel_of_bruhatCover (hBruhat : BruhatCover F) (hq : 2 < Nat.card F)
    (H : Subgroup (Model F)) (hU : unipotent ≤ H) (hH : Group.IsSolvable H) :
    H ≤ borel := by
  intro g hg
  obtain ⟨i, u, hu, t, ht, v, hv, he⟩ := hBruhat g
  have hwt : weylRep i * t ∈ H := by
    have hm := H.mul_mem (H.mul_mem (H.inv_mem (hU hu)) hg) (H.inv_mem (hU hv))
    have heq : u⁻¹ * g * v⁻¹ = weylRep i * t := by rw [he]; group
    rwa [heq] at hm
  have hi := weyl_index_eq_zero_of_solvable hq H hU hH i t ht hwt
  rw [hi, weylRep_zero, mul_one] at he
  rw [he]
  exact borel.mul_mem (borel.mul_mem (mem_sup_left hu) (mem_sup_right ht))
    (mem_sup_left hv)

/-- The requested full-parabolic alternative, conditional only on concrete
Bruhat coverage of the split-octonion model. -/
theorem le_parabolic_of_bruhatCover (hBruhat : BruhatCover F) (hq : 2 < Nat.card F)
    (H : Subgroup (Model F)) (hU : unipotent ≤ H) (hH : Group.IsSolvable H) :
    H ≤ parabolic₁ ∨ H ≤ parabolic₂ :=
  Or.inl ((le_borel_of_bruhatCover hBruhat hq H hU hH).trans borel_le_parabolic₁)

/-- Every solvable overgroup of the positive-root Sylow in the full G₂ model
lies in its Borel, including over the field of four elements. -/
theorem le_borel (hq : 2 < Nat.card F)
    (H : Subgroup (Model F)) (hU : unipotent ≤ H) (hH : Group.IsSolvable H) :
    H ≤ borel :=
  le_borel_of_bruhatCover bruhatCover hq H hU hH

/-- The full standard-parabolic alternative for a solvable Sylow overgroup. -/
theorem le_parabolic (hq : 2 < Nat.card F)
    (H : Subgroup (Model F)) (hU : unipotent ≤ H) (hH : Group.IsSolvable H) :
    H ≤ parabolic₁ ∨ H ≤ parabolic₂ :=
  le_parabolic_of_bruhatCover bruhatCover hq H hU hH

end Atlas.G2.SolvableSylowPlacement
