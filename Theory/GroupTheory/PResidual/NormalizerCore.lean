module

public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Residual normalizers detected by prime cores

If the embedded p-core of P lies in its embedded p-residual R, then the
embedded p-core of R equals that of P. One inclusion uses relative
normality of R in P; the other uses normality of the core of P in R.
Characteristicity then bounds N(R) by the normalizer of this common core.
In particular N(R) = P whenever the core has normalizer P.

These are general group-theoretic reductions for the two-node binary
parabolics in Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed p.960. Core absorption is an explicit additional premise,
which must be established in each concrete parabolic.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A subgroup normalizes its intrinsic residual embedded in the ambient group. -/
theorem le_normalizer_embedded_pResidual (p : ℕ) (P : Subgroup G) :
    P ≤ normalizer ((pResidual p P).map P.subtype) := by
  have h := (pResidual p P).le_normalizer_map P.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h

/-- Absorbing the ambient local core identifies the residual's own local core. -/
theorem pCoreIn_embedded_pResidual_eq_of_core_le (p : ℕ) (P : Subgroup G)
    (h : P.pCoreIn p ≤ (pResidual p P).map P.subtype) :
    ((pResidual p P).map P.subtype).pCoreIn p = P.pCoreIn p := by
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes (map_subtype_le _) (le_normalizer_embedded_pResidual p P)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn p P) h
      ((map_subtype_le _).trans (P.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image P (pCore p P))))

/-- Recover the residual normalizer from core absorption and the core normalizer. -/
theorem normalizer_embedded_pResidual_eq_of_core_le (p : ℕ) (P : Subgroup G)
    (h : P.pCoreIn p ≤ (pResidual p P).map P.subtype)
    (hn : normalizer (P.pCoreIn p) = P) :
    normalizer ((pResidual p P).map P.subtype) = P := by
  apply le_antisymm _ (le_normalizer_embedded_pResidual p P)
  have hle := normalizer_le_normalizer_characteristic_image
    ((pResidual p P).map P.subtype) (pCore p ((pResidual p P).map P.subtype))
  change normalizer ((pResidual p P).map P.subtype) ≤
    normalizer (((pResidual p P).map P.subtype).pCoreIn p : Set G) at hle
  rwa [pCoreIn_embedded_pResidual_eq_of_core_le p P h, hn] at hle
end Subgroup

end
