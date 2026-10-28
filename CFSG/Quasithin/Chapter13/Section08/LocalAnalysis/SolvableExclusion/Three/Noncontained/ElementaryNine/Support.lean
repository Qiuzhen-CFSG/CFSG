module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.ModuleAction
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds
public import Theory.Representation.DualCommutator

/-!
# Eight dimensions in the literal elementary-nine support

Hyperplane orbit counting bounds the moving dimension, not just the total
dimension. Apply it to the dual representation: its fixed codimension is
the dimension of the original commutator space. Thus four-element orbits of
hyperplanes of P* force eight dimensions in [U_H/V₁,P*]. The character-space
sum is proved in the lower representation library and is not an assumption.

The source application uses the given faithful action on the literal quotient
U_H/V₁. Only the orbit bound remains explicit here; the local SL₂(3) image
recognition must construct it. There is no endpoint-order assumption and no
replacement of this support by an unrelated module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968); hyperplane counting as in G.7.1(3), p.347.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryCoprimeDegree
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

variable {K W : Type*} [Group K] [Finite K] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite K] in
/-- Faithfulness survives passage to the dual of the finite binary module. -/
theorem dual_injective (ρ : Representation (ZMod 2) K W)
    (hρ : Function.Injective ρ) : Function.Injective ρ.dual := by
  intro x y hxy
  apply inv_injective
  apply hρ
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
  intro f
  have h := congrArg (fun z : Module.End (ZMod 2) (Module.Dual (ZMod 2) W) => z f v) hxy
  change f (ρ x⁻¹ v) = f (ρ y⁻¹ v) at h
  simpa only [map_sub, sub_eq_zero] using h

omit [Finite K] [FiniteDimensional (ZMod 2) W] in
/-- The coinvariant kernel is the same embedded commutator subspace. -/
theorem coinvariants_eq_support (ρ : Representation (ZMod 2) K W)
    (P : Subgroup K) : Coinvariants.ker (ρ.comp P.subtype) = subspaceCommutator ρ ⊤ P := by
  unfold Coinvariants.ker subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨⟨p, w⟩, rfl⟩
    exact ⟨p, p.property, w, Submodule.mem_top, rfl⟩
  · rintro ⟨p, hp, w, _, rfl⟩
    exact ⟨(⟨p, hp⟩, w), rfl⟩

private theorem eight_le_fixedCodim (ρ : Representation (ZMod 2) K W)
    (hρ : Function.Injective ρ) (P : Subgroup K) [IsElementaryAbelian 3 P]
    (hne : P ≠ ⊥)
    (horbit : ∀ J : Subgroup P, J.index = 3 →
      4 ≤ Nat.card (normalizerHyperplaneOrbit P J)) :
    8 ≤ fixedCodim ρ P := by
  classical
  have hsum := hyperplane_dimension_sum ρ (p := 3) (by decide) P
  have hproper := fixed_finrank_lt_of_faithful ρ hρ P hne
  have hpos : 0 < hyperplaneDimensionSum ρ P 3 := by omega
  obtain ⟨J, hJ, hm⟩ := Finset.sum_pos_iff.mp hpos
  have hidx := (mem_hyperplanes P 3 J).mp hJ
  have hdegree := orderOf_le_hyperplaneMultiplicity ρ (p := 3) (by decide) P J hidx hm
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at hdegree
  have hbound : 8 ≤ hyperplaneDimensionSum ρ P 3 := calc
    8 = 4 * 2 := rfl
    _ ≤ Nat.card (normalizerHyperplaneOrbit P J) * hyperplaneMultiplicity ρ P J :=
      Nat.mul_le_mul (horbit J hidx) hdegree
    _ ≤ _ := orbit_mul_multiplicity_le_sum ρ P J hidx
  have hdim := fixedCodim_add_finrank ρ P
  change fixedCodim ρ P + Module.finrank (ZMod 2) (invariants (ρ.comp P.subtype)) = _ at hdim
  omega

/-- The actual commutator subspace has dimension at least eight. Duality
discharges the support identification without assuming a faithful section. -/
theorem support_finrank_ge_eight (ρ : Representation (ZMod 2) K W)
    (hρ : Function.Injective ρ) (P : Subgroup K) [IsElementaryAbelian 3 P]
    (hne : P ≠ ⊥)
    (horbit : ∀ J : Subgroup P, J.index = 3 →
      4 ≤ Nat.card (normalizerHyperplaneOrbit P J)) :
    8 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ P) := by
  have h := eight_le_fixedCodim ρ.dual (dual_injective ρ hρ) P hne horbit
  have he : fixedCodim ρ.dual P = Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ P) := by
    rw [← coinvariants_eq_support ρ P]
    exact finrank_quotient_dual_invariants_eq_commutator (ρ.comp P.subtype)
  rwa [he] at h

variable {G : Type*} [Group G] [Finite G]

/-- Application to [Ũ_H,P] with the actual star action. The only remaining
action premise is the orbit bound to be supplied by local image recognition. -/
theorem source_support_finrank_ge_eight
    {H L₁ T M Vα V₃ V₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (r : ReducedOdd 3 H L₁ T M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)]
    (hcard : Nat.card (Source.starImage H r.P) = 9)
    (a : Five.StarAction H (Source.UH H V₃) V₁) (ha : Function.Injective a.action)
    (horbit : ∀ J : Subgroup (Source.starImage H r.P), J.index = 3 →
      4 ≤ Nat.card (normalizerHyperplaneOrbit (Source.starImage H r.P) J)) :
    8 ≤ Module.finrank (ZMod 2) (subspaceCommutator
      (Supercritical.Offenders.linearAction a) ⊤ (Source.starImage H r.P)) := by
  have hne : Source.starImage H r.P ≠ ⊥ := by
    intro he
    have hc := card_eq_one.mpr he
    omega
  exact support_finrank_ge_eight (Supercritical.Offenders.linearAction a)
    (Supercritical.Offenders.linearAction_injective a ha) _ hne horbit

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

end
