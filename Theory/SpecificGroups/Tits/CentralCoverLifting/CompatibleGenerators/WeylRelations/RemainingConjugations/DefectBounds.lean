module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate10
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.SourceSetup

import Mathlib.Tactic.NormNum
/-!
# Eliminating four central-error coordinates

Write p,q,t,u for the errors of VII(s₄), VII(s₃), VII(r₃), VIII(s₂).
Eight replayed identities give integer relations among these central elements.
Their combinations first kill q*t², then bound t by fourth power one, and
finally kill u and p by their odd-power relations and square-one bounds.
The generic certificate is applied here to `normalized_source hroot`, so
these are results in the actual normalized presentation.

Source: Parrott (1972), §5, p.683. The integer combinations below are explicit
and checked by Lean; the word identities come from the preceding certificate.
-/
public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
open Context
set_option backward.isDefEq.respectTransparency false

private def coeffScale (n : ℤ) (v : Coeff) : Coeff :=
  (n * v.1, n * v.2.1, n * v.2.2.1, n * v.2.2.2.1,
    n * v.2.2.2.2.1, n * v.2.2.2.2.2.1, n * v.2.2.2.2.2.2)

private theorem coeffScale_eq_smul (n : ℤ) (v : Coeff) : coeffScale n v = n • v := by
  ext <;> simp [coeffScale]

private structure Vanishes {G : Type*} [Group G] (D : Context G) (v : Coeff) : Prop where
  eq : D.scalar v = 1

private theorem vadd {G : Type*} [Group G] {D : Context G} {v u : Coeff}
    (hv : Vanishes D v) (hu : Vanishes D u) : Vanishes D (v + u) :=
  ⟨vanishes_add hv.eq hu.eq⟩

private theorem vscale {G : Type*} [Group G] {D : Context G} {v : Coeff}
    (n : ℤ) (h : Vanishes D v) : Vanishes D (coeffScale n v) := by
  constructor
  rw [coeffScale_eq_smul]
  exact vanishes_smul n h.eq

private theorem scalar_bounds {G : Type*} [Group G] (D : Context G) (H : Source D) :
    D.scalar (0, 1, 0, 0, 0, 0, 0) = 1 ∧
    D.scalar (0, 0, 0, 0, 0, 1, 0) = 1 ∧
    D.scalar (0, 0, 0, 1, 2, 0, 0) = 1 ∧
    D.scalar (0, 0, 0, 0, 4, 0, 0) = 1 := by
  have hA : Vanishes D (0, 2, 0, 0, 0, 0, 0) := ⟨(n34 D H).scalar_eq_one⟩
  have hB : Vanishes D (0, 0, 0, 0, 0, 2, 0) := ⟨(n38 D H).scalar_eq_one⟩
  have hC : Vanishes D (0, 0, 0, -2, -4, 0, 0) := ⟨(n344 D H).scalar_eq_one⟩
  have hD : Vanishes D (0, 0, 0, -5, -18, 0, 0) := ⟨(n1930 D H).scalar_eq_one⟩
  have hE : Vanishes D (0, 0, 0, -33, -66, -14, 0) := ⟨(n2137 D H).scalar_eq_one⟩
  have hF : Vanishes D (0, 0, 0, 536, 1036, 184, 0) := ⟨(n4940 D H).scalar_eq_one⟩
  have hG : Vanishes D (0, -3, 0, -148, -288, -59, 0) := ⟨(n6052 D H).scalar_eq_one⟩
  have hH : Vanishes D (0, 0, 0, -1263, -2542, -411, 0) := ⟨(n6191 D H).scalar_eq_one⟩
  have hX : Vanishes D (0, 0, 0, 1, 2, 0, 0) :=
    (by have hv := (vadd (D := D) (v := (0, 0, 0, 1, 2, 14, 0)) (u := (0, 0, 0, 0, 0, -14, 0)) (by have hv := (vadd (D := D) (v := (0, 0, 0, -32, -64, 0, 0)) (u := (0, 0, 0, 33, 66, 14, 0)) (by have hv := (vscale (D := D) (v := (0, 0, 0, -2, -4, 0, 0)) (16) hC); norm_num [coeffScale] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, -33, -66, -14, 0)) (-1) hE); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 0, 0, 2, 0)) (-7) hB); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv)
  have h8 : Vanishes D (0, 0, 0, 0, 8, 0, 0) :=
    (by have hv := (vadd (D := D) (v := (0, 0, 0, 5, 18, 0, 0)) (u := (0, 0, 0, -5, -10, 0, 0)) (by have hv := (vscale (D := D) (v := (0, 0, 0, -5, -18, 0, 0)) (-1) hD); norm_num [coeffScale] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 1, 2, 0, 0)) (-5) hX); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv)
  have h4 : Vanishes D (0, 0, 0, 0, 4, 0, 0) :=
    (by have hv := (vadd (D := D) (v := (0, 0, 0, 0, 4, -184, 0)) (u := (0, 0, 0, 0, 0, 184, 0)) (by have hv := (vadd (D := D) (v := (0, 0, 0, 0, 36, -184, 0)) (u := (0, 0, 0, 0, -32, 0, 0)) (by have hv := (vadd (D := D) (v := (0, 0, 0, -536, -1036, -184, 0)) (u := (0, 0, 0, 536, 1072, 0, 0)) (by have hv := (vscale (D := D) (v := (0, 0, 0, 536, 1036, 184, 0)) (-1) hF); norm_num [coeffScale] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 1, 2, 0, 0)) (536) hX); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 0, 8, 0, 0)) (-4) h8); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 0, 0, 2, 0)) (92) hB); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv)
  have hU : Vanishes D (0, 0, 0, 0, 0, 1, 0) :=
    (by have hv := (vadd (D := D) (v := (0, 0, 0, 0, 0, 411, 0)) (u := (0, 0, 0, 0, 0, -410, 0)) (by have hv := (vadd (D := D) (v := (0, 0, 0, 0, 16, 411, 0)) (u := (0, 0, 0, 0, -16, 0, 0)) (by have hv := (vadd (D := D) (v := (0, 0, 0, 1263, 2542, 411, 0)) (u := (0, 0, 0, -1263, -2526, 0, 0)) (by have hv := (vscale (D := D) (v := (0, 0, 0, -1263, -2542, -411, 0)) (-1) hH); norm_num [coeffScale] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 1, 2, 0, 0)) (-1263) hX); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 0, 4, 0, 0)) (-4) h4); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 0, 0, 2, 0)) (-205) hB); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv)
  have hP : Vanishes D (0, 1, 0, 0, 0, 0, 0) :=
    (by have hv := (vadd (D := D) (v := (0, 1, 0, 0, 0, 59, 0)) (u := (0, 0, 0, 0, 0, -59, 0)) (by have hv := (vadd (D := D) (v := (0, 1, 0, 0, -8, 59, 0)) (u := (0, 0, 0, 0, 8, 0, 0)) (by have hv := (vadd (D := D) (v := (0, 1, 0, 148, 288, 59, 0)) (u := (0, 0, 0, -148, -296, 0, 0)) (by have hv := (vadd (D := D) (v := (0, -2, 0, 0, 0, 0, 0)) (u := (0, 3, 0, 148, 288, 59, 0)) (by have hv := (vscale (D := D) (v := (0, 2, 0, 0, 0, 0, 0)) (-1) hA); norm_num [coeffScale] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, -3, 0, -148, -288, -59, 0)) (-1) hG); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 1, 2, 0, 0)) (-148) hX); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv) h8); norm_num [Prod.mk_add_mk] at hv; exact hv) (by have hv := (vscale (D := D) (v := (0, 0, 0, 0, 0, 1, 0)) (-59) hU); norm_num [coeffScale] at hv; exact hv)); norm_num [Prod.mk_add_mk] at hv; exact hv)
  exact ⟨hP.eq, hU.eq, hX.eq, h4.eq⟩

/-- The checked word identities eliminate VII(s₄) and VIII(s₂), and reduce
the other two errors to a single central element of fourth power one. -/
theorem remaining_defect_bounds
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    FreeGroup.lift normalizedGenerator (parrottRelator .vii_s4) = 1 ∧
    FreeGroup.lift normalizedGenerator (parrottRelator .viii_s2) = 1 ∧
    FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3) *
      (FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)) ^ 2 = 1 ∧
    (FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)) ^ 4 = 1 := by
  obtain ⟨hp, hu, hx, ht⟩ := scalar_bounds (normalizedContext hroot) (normalized_source hroot)
  constructor
  · simpa [Context.scalar, normalizedContext, relatorValue] using congrArg Subtype.val hp
  constructor
  · simpa [Context.scalar, normalizedContext, relatorValue] using congrArg Subtype.val hu
  constructor
  · simpa [Context.scalar, normalizedContext, relatorValue] using congrArg Subtype.val hx
  · simpa [Context.scalar, normalizedContext, relatorValue] using congrArg Subtype.val ht
end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
