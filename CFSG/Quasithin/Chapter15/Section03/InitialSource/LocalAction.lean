module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Components
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ActionQuotient
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# The original Chapter 15 local-module action is solvable

The solvable residual is normal in H. Once it centralizes the original
central involutions Z, it centralizes their full H-conjugate span V(H).
Thus the actual quotient H/C_H(V(H)) used by the Chapter 15 preliminary
action API is solvable. The quotient map and all subgroup images are the
published localActionMap and localActionImage constructions.

The kernel also lies in Mc whenever C_G(Z) has that unique maximal local
overgroup. These are source consequences of the original empty-family
hypothesis, not an orthogonal-module marking or an assumed action model.
The natural orthogonal alternative of 15.1.3 remains a separate reduction.

Source: Aschbacher–Smith 14.1.6(1),(3), printed p.977, applied to the
Chapter 14/15 convention V(H)=⟨Zᴴ⟩, and 15.3.11, printed pp.1123–1124.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The actual local action kernel lies in the original distinguished overgroup. -/
theorem localModule_centralizer_le_partner (T : Sylow 2 G) (H : Subgroup G)
    {Mc : Subgroup G}
    (hMc : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    centralizer (localModule T H : Set G) ≤ Mc :=
  (centralizer_le (le_conjugateSpanBy (centralInvolutions T) H)).trans
    (centralizer_le_partner T hMc)

variable
  (hA : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
  (hC : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
  (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
  (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
include hA hC hG hempty

/-- Source 14.1.6(1) for the precise conjugate-span module used in Chapter 15. -/
theorem residual_le_centralizer_localModule {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    (solvableResidual H).map H.subtype ≤ centralizer (localModule T H : Set G) :=
  le_centralizer_conjugateSpanBy_of_normalizes _ _ _
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (solvableResidual H)))
    (residual_le_centralizer_Z hA hC hG T hempty hH)

/-- Solvability of the literal quotient in the existing Section 15.3 action API. -/
theorem localActionQuotient_isSolvable {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    Group.IsSolvable (LocalActionQuotient (centralInvolutions T) H) := by
  let q := localActionMap (centralInvolutions T) H
  have hres : solvableResidual (LocalActionQuotient (centralInvolutions T) H) = ⊥ := by
    rw [← map_solvableResidual_eq q (QuotientGroup.mk'_surjective _)]
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mpr
    exact residual_le_centralizer_localModule hA hC hG T hempty hH
      (mem_map_of_mem H.subtype hx)
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual
    (G := LocalActionQuotient (centralInvolutions T) H)
  exact ⟨n, hn.trans hres⟩

/-- Every actual source subgroup image inherits the proved solvable action. -/
theorem localActionImage_isSolvable {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G)) (X : Subgroup G) :
    Group.IsSolvable (localActionImage (centralInvolutions T) H X) := by
  let := localActionQuotient_isSolvable hA hC hG T hempty hH
  infer_instance

end CFSG.Quasithin.Chapter15.Section03.InitialSource
