module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.ProductBranches
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.OuterBranch

/-!
# Select an escaping ordinary component of the Thompson image

Every alternative of the complete B.5.6 interface yields an ordinary
component of J(I)* outside M_I*. The trivial actor contradicts escape,
and the single S₃ lies in the exact normalizer of Y₊*. In the quasisimple
case B.5.1 supplies the Sylow supplement. In both product cases the
at-most-two bound on normal S₃ factors and the Sylow intersection in
their normalizers place those factors in M_I*, so a residual component
must escape. In the outer A₆–C₃ case the characteristic cubic factor
lies in M_I*, forcing the A₆ component to escape.

The local adapter uses the literal Thompson action and its proved offender
generation. It takes the complete `SourceAlternative` already constructed
by the parent, together with the earlier Sylow, theta, normalizer and
escape conclusions. This deduction serves both three-rank branches and
needs no exponent assertion about Y₊. The universal classification and
the subsequent lift to a C-component remain with their source owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
B.2.5–7, B.5.3/6, and 15.3.15(2)/26(2), printed pp.76, 104–105,
1123–1126 and 1130.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection
variable {A : Type*} [Group A] [Finite A]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Exhaustive selection from the complete source alternatives on a normal
offender-generated actor escaping the normalizer of a two-perfect subgroup. -/
theorem exists_component_outside_of_sourceAlternative
    (N Y M : Subgroup A) [N.Normal] (S : Sylow 2 A)
    (hY : IsPPerfect 2 Y) (hSM : (S : Subgroup A) ≤ M)
    (hM : normalizer (Y : Set A) = M) (hNM : ¬ N ≤ M)
    (ρ : Representation (ZMod 2) N V) (hg : offenderSubgroup ρ = ⊤)
    (h : SourceAlternative ρ) :
    ∃ E : Subgroup N, IsComponent N E ∧ ¬ E.map N.subtype ≤ M := by
  cases h with
  | trivial ht =>
    let : Subsingleton N := ht
    exact (hNM (N.eq_bot_of_subsingleton ▸ bot_le)).elim
  | quasisimple hq ha =>
    exact exists_component_outside_of_quasisimple N M S hSM hNM ρ hq ha
  | symmetricThree c =>
    exact (hNM (StarSelection.symmetricThree_le_of_normalizer_eq
      N c.equiv S Y M hY hSM hM)).elim
  | twoFactors c =>
    exact ProductBranches.exists_component_outside_of_twoFactors
      N Y M S hY hSM hM hNM ρ c
  | outerSixThree c =>
    exact exists_component_outside_of_outerSixThree N Y M S hY hSM hM hNM ρ hg c
  | hyperplane c =>
    exact ProductBranches.exists_component_outside_of_hyperplane
      N Y M S hY hSM hM hNM ρ c

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
open StarSelection.QuotientSelection
variable {G : Type*} [Group G] [Finite G] (d : LocalData G)

/-- An ordinary component of the literal J(I)* escapes M_I* in every complete
FF source alternative. The parent supplies the characteristic-two module
instance and classification; offender generation is proved in `ThompsonAction`. -/
theorem exists_star_component_of_sourceAlternative {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hθ : theta (d.MI I) = d.Yplus)
    (hN : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M)
    (hZI : d.Z ≤ I) [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]
    (h : SourceAlternative (d.thompsonStarAction I hZI)) :
    ∃ E : Subgroup (d.thompsonStar I), IsComponent (d.thompsonStar I) E ∧
      ¬ E.map (d.thompsonStar I).subtype ≤ d.starImage I d.M := by
  obtain ⟨P, hP⟩ := d.exists_starSylow hS
  apply exists_component_outside_of_sourceAlternative (d.thompsonStar I)
    (d.starImage I d.Yplus) (d.starImage I d.M) P
    (d.starYplus_twoPerfect hI hθ) ?_ hN hJ (d.thompsonStarAction I hZI)
    (d.thompsonStarAction_generated I hZI) h
  rw [hP]
  exact map_mono (comap_mono (inf_le_left.trans d.sylow_le))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
