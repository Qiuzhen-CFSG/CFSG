module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.LocalAction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Transport
public import Theory.Representation.NormalElementaryQuotient

/-!
# The actual Sylow action on the component omega subgroup

The source module is U_L = Ω₁(T ∩ L), viewed inside T. Normalization follows
from T normalizing L; no ambient normality of L or U_L is imposed. Conjugation
has exactly C_T(U_L) as kernel. Passing to its actual range produces the
faithful binary representation used in the outer-offender argument.

`StrictActionBound` records the outstanding quantitative model calculation,
not its existence: every nontrivial image of an elementary subgroup loses
more fixed points than it gains in image order. The final theorem converts
this numerical inequality to exclusion of genuine FF-star offenders.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, and Definitions B.1.3 and B.2.2, pp.67 and 74–75.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L R : Subgroup G} {n : ℕ}

def componentOmegaInSylow (T : Sylow 2 G) (L : Subgroup G) : Subgroup T :=
  (omegaOneAmbient (componentSylow T L)).subgroupOf T

theorem componentOmega_normal (h : StandardSetup T z L) :
    (componentOmegaInSylow T L).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact ((le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
    inf_normalizer_le_normalizer_inf).trans (normalizer_le_omega_normalizer _)

noncomputable def omegaAction (h : StandardSetup T z L) :
    T →* MulAut (componentOmegaInSylow T L) := by
  let := componentOmega_normal h
  exact MulAut.conjNormal

theorem omegaAction_ker (h : StandardSetup T z L) :
    (omegaAction h).ker = centralizer (componentOmegaInSylow T L : Set T) := by
  ext t
  change omegaAction h t = 1 ↔ _
  constructor
  · intro ht u hu
    have he := congrArg (fun a : MulAut (componentOmegaInSylow T L) =>
      (a ⟨u, hu⟩ : T)) ht
    change t * u * t⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ht
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change t * (u : T) * t⁻¹ = (u : T)
    rw [← ht _ u.property, mul_inv_cancel_right]

theorem omegaAction_apply (h : StandardSetup T z L) (t : T)
    (u : componentOmegaInSylow T L) :
    ((omegaAction h t u : T) : G) = (t : G) * (u : T) * (t : G)⁻¹ := rfl

noncomputable def omegaProjection (h : StandardSetup T z L) :
    T →* (omegaAction h).range := (omegaAction h).rangeRestrict

theorem omegaProjection_ker (h : StandardSetup T z L) :
    (omegaProjection h).ker = centralizer (componentOmegaInSylow T L : Set T) := by
  rw [omegaProjection, MonoidHom.ker_rangeRestrict, omegaAction_ker]

noncomputable def omegaRepresentation (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (componentOmegaInSylow T L)] :
    Representation (ZMod 2) (omegaAction h).range (Additive (componentOmegaInSylow T L)) := by
  let := componentOmega_normal h
  exact Representation.NormalElementaryQuotient.representation _ (omegaProjection h)
    (omegaAction h).rangeRestrict_surjective (omegaProjection_ker h)

/-- The binary action is the original ambient conjugation, on the same U_L. -/
theorem omegaRepresentation_apply (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (componentOmegaInSylow T L)]
    (t : T) (v : Additive (componentOmegaInSylow T L)) :
    (((omegaRepresentation h (omegaProjection h t) v).toMul : T) : G) =
      (t : G) * (v.toMul : T) * (t : G)⁻¹ := by
  let := componentOmega_normal h
  exact congrArg (fun t : T => (t : G))
    (Representation.NormalElementaryQuotient.representation_apply
      (componentOmegaInSylow T L) (omegaProjection h)
      (omegaAction h).rangeRestrict_surjective (omegaProjection_ker h) t v)

/-- The representation of the actual conjugation image is faithful. -/
theorem omegaRepresentation_injective (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (componentOmegaInSylow T L)] :
    Function.Injective (omegaRepresentation h) := by
  let := componentOmega_normal h
  exact Representation.NormalElementaryQuotient.representation_injective
    (componentOmegaInSylow T L) (omegaProjection h)
    (omegaAction h).rangeRestrict_surjective (omegaProjection_ker h)

/-- The representation fixed space has exactly the actual relative-centralizer order. -/
theorem omegaRepresentation_fixedSpace_card (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (componentOmegaInSylow T L)] (A : Subgroup T) :
    Nat.card (Representation.BinaryOffender.fixedSpace (omegaRepresentation h)
      (A.map (omegaProjection h))) =
      Nat.card (componentOmegaInSylow T L ⊓ centralizer (A : Set T) : Subgroup T) := by
  let := componentOmega_normal h
  exact Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv
    (componentOmegaInSylow T L) (omegaProjection h)
    (omegaAction h).rangeRestrict_surjective (omegaProjection_ker h) A)

/-- The strict loss of fixed points required from the semilinear model calculation.
Only nontrivial images of actual elementary subgroups of T are tested. -/
def StrictActionBound (h : StandardSetup T z L) : Prop :=
  ∀ A : Subgroup T, IsElementaryAbelian 2 A → A.map (omegaProjection h) ≠ ⊥ →
    Nat.card (componentOmegaInSylow T L ⊓ centralizer (A : Set T) : Subgroup T) *
      Nat.card (A.map (omegaProjection h)) < Nat.card (componentOmegaInSylow T L)

/-- The strict cardinal inequality excludes actual FF-star offenders in the
faithful action image, with the source definition of best offender. -/
theorem image_not_bestOffender_of_bound (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (componentOmegaInSylow T L)] (hb : StrictActionBound h)
    (A : Subgroup T) (hA : IsElementaryAbelian 2 A) :
    ¬ Representation.BinaryOffender.IsBestOffender (omegaRepresentation h)
      (A.map (omegaProjection h)) := by
  let := componentOmega_normal h
  intro hbest
  have hoff := hbest.isOffender (omegaRepresentation h)
  have hlt := hb A hA hoff.1.1
  have hfix := omegaRepresentation_fixedSpace_card h A
  have hcU := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (componentOmegaInSylow T L))
  have hcF := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Representation.BinaryOffender.fixedSpace (omegaRepresentation h)
      (A.map (omegaProjection h)))
  rw [Nat.card_zmod] at hcU hcF
  have hdim := (Representation.BinaryOffender.fixedCodim_le_rank_iff
    (omegaRepresentation h) (A.map (omegaProjection h))).mp hoff.2
  unfold Representation.BinaryOffender.weight at hdim
  have hc : Nat.card (componentOmegaInSylow T L) ≤
      Nat.card (componentOmegaInSylow T L ⊓ centralizer (A : Set T) : Subgroup T) *
        Nat.card (A.map (omegaProjection h)) := by
    rw [← hfix, hcF, hoff.1.card_eq_two_pow_rank, ← pow_add]
    change Nat.card (Additive (componentOmegaInSylow T L)) ≤ _
    rw [hcU]
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    omega
  exact (not_lt_of_ge hc) hlt


end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
