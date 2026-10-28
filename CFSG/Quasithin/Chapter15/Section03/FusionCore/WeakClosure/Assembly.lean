module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Consequences
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConsequences
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Displacement

/-!+# Assembly after the orthogonal orbit and weak-closure calculations

The dimension and the earlier fixed-line order discharge the numerical
premises of the Frattini argument. The resulting conclusions concern the
actual weak-closure parameters and every conjugate of `V` contained in `M`.
For 15.3.47, the fixed nonsingular vector proves that a nontrivial commutator
cannot be totally singular. Its normalizer is therefore in `M`, where the
weak-closure conclusion applies.

Two intermediate inputs remain: `OrthogonalFusionCalculations`, and the
two-case proof that `W₀(T,V)` centralizes `V`. Neither is asserted to follow
from the earlier source inputs here. This module assembles their consequences;
it does not assert 15.3.46–47 from the earlier source inputs alone.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- All three consequences in 15.3.46(4), with only the centralization step
left as an intermediate input. In particular the normalizer is ambient. -/
theorem weakClosure_zero_consequences
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hW : ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G)) :
    0 < ChapterE.globalW V T ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ M →
        V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) ∧
      normalizer (ChapterE.indexedWeakClosure V T 0 : Set G) ≤ M := by
  have hcard : Nat.card V = 16 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, d.dimension] at hc
    exact hc
  have hVne : V ≠ ⊥ := by
    intro he
    simp [he] at hcard
  refine ⟨globalW_pos_of_weakClosure_zero hW,
    conjugate_in_M_le_centralizer_of_weakClosure_zero T h.sylow_le h.normalizer_eq hW,
    normalizer_weakClosure_zero_le M V T h.module_le_sylow hVne
      h.sylow_le d.normalizes ?_ h.residual_uniqueness hW⟩
  apply not_le_centralizer_sup_sylow T M V h.module_eq h.central_fixed
  rw [h.central_order, hcard]
  norm_num

/-- The source's nonsingularity assertion for `[V,x]` follows from the
fixed nonsingular vector; it is not an additional hypothesis. -/
theorem not_totallySingular_commutator_of_centralizes_fixedPlane
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (hP : IsDefinitePlane d.form P)
    (x : G) (hx : x ∈ centralizer (fixedPlane V (planeStabilizer T P) : Set G))
    (hne : ⁅V, zpowers x⁆ ≠ ⊥) :
    ¬ IsTotallySingular d.form ⁅V, zpowers x⁆ := by
  have hxM : x ∈ M := normalizer_fixedPlane_le_of_orthogonal_calculations c h hP
    (Subgroup.centralizer_le_normalizer _ hx)
  apply d.not_totallySingular_commutator_of_fixed_nonsingular ⟨x, hxM⟩ c.v
    (c.vector_nonsingular hP) ?_ hne
  have hcomm := hx (c.v : G) (c.vector_mem_fixedPlane hP.1)
  change x * (c.v : G) * x⁻¹ = c.v
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

/-- The full alternative of 15.3.47 after the two missing calculations for
15.3.46. The normalizing condition is on each whole conjugate subgroup. -/
theorem commutator_alternative_of_orthogonal_calculations
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (hP : IsDefinitePlane d.form P)
    (hW : ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G))
    (x : G) (hx : x ∈ centralizer (fixedPlane V (planeStabilizer T P) : Set G)) :
    ⁅V, zpowers x⁆ = ⊥ ∨
      ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ normalizer ((⁅V, zpowers x⁆ : Subgroup G) : Set G) →
        V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  by_cases hne : ⁅V, zpowers x⁆ = ⊥
  · exact Or.inl hne
  refine Or.inr ?_
  have hxM : x ∈ M := normalizer_fixedPlane_le_of_orthogonal_calculations c h hP
    (Subgroup.centralizer_le_normalizer _ hx)
  have hcommV : ⁅V, zpowers x⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (d.normalizes hxM))
  have hN := normalizer_le_of_not_totallySingular d.form h.normalizer_eq
    (controlsFusion_of_orthogonal_calculations c h)
    (nonsingular_centralizer_le_of_orthogonal_calculations c h) hcommV
    (not_totallySingular_commutator_of_centralizes_fixedPlane d h c hP x hx hne)
  intro g hg
  exact conjugate_in_M_le_centralizer_of_weakClosure_zero T h.sylow_le
    h.normalizer_eq hW g (hg.trans hN)

end CFSG.Quasithin.Chapter15.Section03.FusionCore
