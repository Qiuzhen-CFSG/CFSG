module

public import CFSG.Quasithin.ChapterB.Section06To07.Residual
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Quotient-factor overgroups and an obstruction to B.6.8(3)

The maximal-subgroup image in the literal quotient `H/J` is proper and
contains the literal Sylow image. A factor whose Sylow orbit generates the
two-residual cannot lie in that image: otherwise the residual and Sylow
subgroup would generate inside a proper subgroup.

The final theorem records an obstruction to the full-normalizer assertion
printed in Aschbacher--Smith, *The Classification of Quasithin Groups*,
B.6.8(3), pp.113--115. A product of two proper subgroups is not maximal
in the product group. We transport this obstruction through a marked
isomorphism of the actual factor normalizer in `H/J`.

The motivating example is `A₅ wr C₂`, with `M = A₄ wr C₂` and `J = 1`.
For one simple factor, the normalizer is `A₅ × A₅`, whereas its intersection
with `M` is `A₄ × A₄`. Its actual conjugation image on that factor is still
a minimal parabolic. The example's wreath-product identifications are not
proved in this file; the obstruction theorem takes a marked product
isomorphism explicitly. In particular, this file does not assert the
printed normalizer conclusion or the general automizer conclusion.
-/

public section
noncomputable section

namespace CFSG.Quasithin.ChapterB.FactorNormalizers

open Subgroup Theory.GroupTheory

variable {H : Type*} [Group H]

/-- The source's `M*`, using the original maximal subgroup and quotient map. -/
abbrev starMax (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    Subgroup (minimalParabolicStarQuotient T hP) :=
  (minimalParabolicMax T hP).map (QuotientGroup.mk' (minimalParabolicCore T hP))

/-- Taking the quotient by the core preserves properness of `M`. -/
theorem starMax_ne_top (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    starMax T hP ≠ ⊤ := by
  intro he
  have hk : (QuotientGroup.mk' (minimalParabolicCore T hP)).ker ≤
      minimalParabolicMax T hP := by
    rw [QuotientGroup.ker_mk']
    exact normalCore_le _
  have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (minimalParabolicCore T hP))) he
  rw [starMax, comap_map_eq_self hk, comap_top] at hh
  exact (minimalParabolicMax_spec T hP).1.ne_top hh

variable [Finite H]

/-- The original Sylow image lies in the original maximal-subgroup image. -/
theorem starSylow_le_starMax (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    (minimalParabolicStarSylow T hP : Subgroup _) ≤ starMax T hP := by
  rw [minimalParabolicStarSylow_coe]
  exact map_mono (minimalParabolicMax_spec T hP).2

/-- A factor generating the star residual under the Sylow action lies outside `M*`.
This uses the earlier factor-orbit premise without assuming ambient normality. -/
theorem factor_not_le_starMax (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (L : Subgroup (minimalParabolicStarQuotient T hP))
    (ho : componentOrbit L (minimalParabolicStarSylow T hP) =
      pResidual 2 (minimalParabolicStarQuotient T hP)) :
    ¬ L ≤ starMax T hP := by
  intro hl
  have hr : pResidual 2 (minimalParabolicStarQuotient T hP) ≤ starMax T hP := by
    rw [← ho]
    exact (componentOrbit_le_sup L _).trans (sup_le hl (starSylow_le_starMax T hP))
  have hh := sup_le hr (starSylow_le_starMax T hP)
  rw [minimalParabolic_residual_star_sup_sylow T hP] at hh
  exact starMax_ne_top T hP (top_unique hh)

private theorem prod_not_coatom {A B : Type*} [Group A] [Group B]
    (P : Subgroup A) (Q : Subgroup B) (hP : P ≠ ⊤) (hQ : Q ≠ ⊤) :
    ¬ IsCoatom (P.prod Q) := by
  intro hm
  have hu : P.prod (⊤ : Subgroup B) ≠ ⊤ := by
    intro he
    apply hP
    apply top_unique
    intro a _
    have hh : (a, (1 : B)) ∈ P.prod (⊤ : Subgroup B) := by rw [he]; trivial
    exact hh.1
  have he := (hm.le_iff_eq hu).mp (prod_mono le_rfl le_top)
  apply hQ
  apply top_unique
  intro b _
  have hh : ((1 : A), b) ∈ P.prod (⊤ : Subgroup B) := ⟨P.one_mem, trivial⟩
  rw [he] at hh
  exact hh.2

omit [Finite H] in
/-- A marked product decomposition obstructs even maximality of the literal
`N_M*(L)` inside `N_H*(L)`. Both normalizers are relative to `H/J`.
The product identification is an explicit premise, not a claim about all factors. -/
theorem not_isCoatom_of_product (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (L : Subgroup (minimalParabolicStarQuotient T hP))
    {A B : Type*} [Group A] [Group B]
    (e : normalizer (L : Set (minimalParabolicStarQuotient T hP)) ≃* A × B)
    (P : Subgroup A) (Q : Subgroup B) (hPproper : P ≠ ⊤) (hQproper : Q ≠ ⊤)
    (he : ((starMax T hP).subgroupOf
      (normalizer (L : Set (minimalParabolicStarQuotient T hP)))).map e.toMonoidHom =
        P.prod Q) :
    ¬ IsCoatom ((starMax T hP).subgroupOf
      (normalizer (L : Set (minimalParabolicStarQuotient T hP)))) := by
  intro hm
  have hh := (e.mapSubgroup.isCoatom_iff _).mpr hm
  change IsCoatom (((starMax T hP).subgroupOf
    (normalizer (L : Set (minimalParabolicStarQuotient T hP)))).map e.toMonoidHom) at hh
  rw [he] at hh
  exact prod_not_coatom P Q hPproper hQproper hh

end CFSG.Quasithin.ChapterB.FactorNormalizers
