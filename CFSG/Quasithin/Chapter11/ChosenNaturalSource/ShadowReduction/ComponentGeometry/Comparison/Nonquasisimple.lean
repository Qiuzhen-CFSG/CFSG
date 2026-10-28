module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.PrimeSupport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Cartan.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Kernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.Nilpotent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Preparation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.MaximalFromStars

/-!
# The nonquasisimple radical argument on the original chosen flag

The source's multiple-overgroup hypothesis discharges the standing guard
in the maximal-local radical argument. Canonical starred membership then
gives centralization of the literal reduced subgroup of KzT. A.4.11
makes the Fitting preimage centralize VK and V1, excluding the first
nonquasisimple alternative on p.777.

The complete 11.1.1 catalogue now reduces to the exceptional elementary
extension. It supplies the literal residual quotient, its two-group kernel
and the Frattini factorization, after excluding the nilpotent-extension row.
These results and their Cartan equality endpoint are re-exported below.
Cartan.Complete constructs the actual normal containing component in N_G(R₁)
and proves that it equals the residual. The original full-Sylow A₅ seed
and the actual PSL₂(p) residual exclude every proper quasisimple container.
Thus all of N_G(R₁), and in particular XT, normalizes the residual.

The all-prime canonical-star theorem now discharges the final remaining
premise of maximal-local radical centralization. Thus both nonquasisimple
alternatives close on the original chosen flag. `ofFlag_eq_of_nonquasisimple`
retains only the exact preceding geometry, Proposition1132At, and complete
11.1.1 catalogue inputs; the parent owns their earlier-source assembly.
The older conditional and single-prime endpoints remain available.
The R1 radical/Sylow assertions concern KzR1, and the component embeddings
retain the actual ambient normalizer N_G(R1).
Source: Aschbacher--Smith, 3.2.14, p.585, and 11.4.2, p.777.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open Chapter3.RadicalCentralization Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- Shared maximal-local radical centralization on the original chosen
setup. The canonical starred-membership source input remains explicit. -/
theorem ofFlag_maximal_radical_centralizes_of_stars
    (S : D.NonbinaryNaturalInput) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (J ⧸ pCore 2 J))
    (hstars : CanonicalRadicalsStarred T J) :
    (solvableRadical J).map J.subtype ≤
      centralizer ((reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G)).map
        (J ⊔ (T : Subgroup G)).subtype : Set G) :=
  maximal_solvableRadical_centralizes_sylowJoin_of_stars
    S.source.simpleQTKE T S.many hJ hn hstars

/-- The source Fitting-centralization clause, using the actual chosen flag. -/
theorem ofFlag_fitting_centralizes_of_stars
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hstars : CanonicalRadicalsStarred T (ofFlag S f X z H).Kz)
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G)) :
    (ofFlag S f X z H).V₁ ≤ pointOmega (ofFlag S f X z H) ∧
      fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G) :=
  ⟨line_le_pointOmega h hR,
    fittingPreimage_centralizes_line h hR (ofFlag_maximal_radical_centralizes_of_stars S hJ hn hstars)⟩

/-- The first source alternative is excluded with 11.4.1(1) discharged
from its earlier linear and Proposition1132At inputs. -/
theorem ofFlag_not_fitting_seed_split_of_stars
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hstars : CanonicalRadicalsStarred T (ofFlag S f X z H).Kz)
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G)) :
    (ofFlag S f X z H).Kz ≠
      fittingPreimage (ofFlag S f X z H) ⊔ (ofFlag S f X z H).L₁ :=
  not_fitting_seed_split h (fixed_and_transitive D S _ hlinear h1132).1 hne hR
    (ofFlag_maximal_radical_centralizes_of_stars S hJ hn hstars)

/-- Final assembly after the three remaining source producers: canonical
stars, the literal Frattini factorization, and Cartan normalization.
No separate radical or Fitting-centralization premise remains. -/
theorem ofFlag_eq_of_stars_and_normalizer_split
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hstars : CanonicalRadicalsStarred T (ofFlag S f X z H).Kz)
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hsplit : (ofFlag S f X z H).Kz =
      fittingPreimage (ofFlag S f X z H) ⊔ normalizerResidual (ofFlag S f X z H))
    (hX : X ≤ normalizer (normalizerResidual (ofFlag S f X z H) : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K :=
  eq_of_fitting_normalizer_split h (fixed_and_transitive D S _ hlinear h1132).1 hline
    (ofFlag_fitting_centralizes_of_stars S f X z H h hJ hn hstars hR).2 hsplit hX

/-- The chosen-flag equality endpoint with the full catalogue reduction and
Frattini argument discharged. Canonical stars and the actual Cartan
normalization remain with this task's final nonquasisimple assembly. -/
theorem ofFlag_eq_of_stars_catalogue_and_cartan
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hstars : CanonicalRadicalsStarred T (ofFlag S f X z H).Kz)
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hc : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (hX : X ≤ normalizer (normalizerResidual (ofFlag S f X z H) : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_cases he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact he
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hF := (ofFlag_fitting_centralizes_of_stars S f X z H h hJ hn hstars hR).2
  have hs := (Frattini.ofFlag_frattini_of_catalogue S f X z H h hA hseed hf he hn hF hc).1
  exact eq_of_fitting_normalizer_split h hf hline hF hs hX

/-- The nonquasisimple equality with the full catalogue, literal Frattini
factorization and Cartan normalization discharged. Canonical starred
membership remains with this task's final source assembly. -/
theorem ofFlag_eq_of_stars_and_catalogue
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hstars : CanonicalRadicalsStarred T (ofFlag S f X z H).Kz)
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K :=
  Cartan.ofFlag_eq_of_fitting_centralizes S f X z H h hA hseed
    (fixed_and_transitive D S _ hlinear h1132).1 hn
    (ofFlag_fitting_centralizes_of_stars S f X z H h hJ hn hstars hR).2 hline hXN hc

/-- The original equality in every prime-power Fitting case. Canonical
stars, point-radical and Fitting centralization, Frattini and Cartan inputs
are discharged; preceding line-geometry premises remain explicit. -/
theorem ofFlag_eq_of_primePower_fitting
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    {p : ℕ} [Fact p.Prime]
    (hprime : IsPGroup p
      (fittingSubgroup ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)))
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K :=
  ofFlag_eq_of_stars_and_catalogue S f X z H h hA hseed hlinear h1132 hJ hn
    (ChosenStars.canonicalRadicalsStarred_of_fitting_isPGroup S.source.simpleQTKE T hJ hn hprime)
    hR hline hXN hc

/-- Complete the exceptional elementary-extension row on the actual
chosen flag, without a canonical-star or Fitting-centralization premise. -/
theorem ofFlag_eq_of_elementary_extension
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hfour : S.field.degree = 2) {p : ℕ} (hp : Source.ExceptionalPrime p)
    (he : HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (ElementaryModel p 2) (fun Q _ => Source.IsSL Q 2 p)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  let : Fact p.Prime := ⟨hp.1⟩
  have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
  exact ofFlag_eq_of_primePower_fitting S f X z H h hA hseed hlinear h1132 hJ hn
    (fitting_isPGroup_of_elementary_extension hp3 he) hR hline hXN
    (.four hfour (.elementaryExtension p hp he))

/-- The complete source catalogue now leaves only a nilpotent SL₂(5)
extension with at least two odd Fitting primes. The same owner must still
prove characteristic-normalizer control in that branch before asserting 11.4.2. -/
theorem ofFlag_eq_or_nilpotent_two_fitting_primes
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      S.field.degree = 2 ∧
      HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
        (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
        (fun Q _ => Source.IsSL Q 2 5) ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧
        p ∣ Nat.card (fittingSubgroup
          ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)) ∧
        q ∣ Nat.card (fittingSubgroup
          ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)) := by
  by_cases heq : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact Or.inl heq
  let E := ofFlag S f X z H
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hr := Frattini.point_quotient_two_rank_le_one S.source.simpleQTKE h hn
  let : Group.IsPerfect E.Kz := Radical.relative_component_perfect h.point_component
  have hnil : S.field.degree = 2 ∧
      HasExtension (E.Kz ⧸ pCore 2 E.Kz)
        (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
        (fun Q _ => Source.IsSL Q 2 5) := by
    cases hc with
    | equal he => exact ((h.strict_comparison hf heq).2.1.ne he).elim
    | lie hm =>
      exact (hn (Frattini.Catalogue.lie_quasisimple_of_rank_le_one S.field.degree_pos hr hm)).elim
    | four hd hm =>
      rcases Frattini.Catalogue.fieldFour_extensions hr hn hm with hnil | ⟨p,hp,he⟩
      · exact ⟨hd,hnil⟩
      · exact (heq (ofFlag_eq_of_elementary_extension S f X z H h hA hseed
          hlinear h1132 hJ hn hR hline hXN hd hp he)).elim
  have hodd : Odd (Nat.card (fittingSubgroup (E.Kz ⧸ pCore 2 E.Kz))) :=
    Nat.coprime_two_left.mp ((pPrimeCore_coprime_card
      (p := 2) (G := E.Kz ⧸ pCore 2 E.Kz)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 (pCore_quotient_pCore_eq_bot 2))))
  rcases primePower_or_two_odd_primes hodd with ⟨p,hp,hP⟩ | htwo
  · let : Fact p.Prime := ⟨hp⟩
    exact Or.inl (ofFlag_eq_of_primePower_fitting S f X z H h hA hseed
      hlinear h1132 hJ hn hP hR hline hXN hc)
  · exact Or.inr ⟨hnil.1,hnil.2,htwo⟩


/-- Canonical starred membership on the original chosen nonbinary-natural
setup, for every maximal nonquasisimple local component. -/
theorem ofFlag_canonicalRadicalsStarred
    (S : D.NonbinaryNaturalInput) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (J ⧸ pCore 2 J)) : CanonicalRadicalsStarred T J :=
  ChosenStars.canonicalRadicalsStarred S.source.simpleQTKE T hJ hn

/-- Shared maximal-local 3.2.14, with canonical stars discharged and the
literal reduced subgroup of JT retained. -/
theorem ofFlag_maximal_radical_centralizes
    (S : D.NonbinaryNaturalInput) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (J ⧸ pCore 2 J)) :
    (solvableRadical J).map J.subtype ≤
      centralizer ((reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G)).map
        (J ⊔ (T : Subgroup G)).subtype : Set G) :=
  ChosenStars.maximal_solvableRadical_centralizes_sylowJoin
    S.source.simpleQTKE T S.many hJ hn

/-- The source VK and Fitting-centralization conclusions on the actual flag. -/
theorem ofFlag_fitting_centralizes
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G)) :
    (ofFlag S f X z H).V₁ ≤ pointOmega (ofFlag S f X z H) ∧
      fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G) :=
  ofFlag_fitting_centralizes_of_stars S f X z H h hJ hn
    (ofFlag_canonicalRadicalsStarred S hJ hn) hR

/-- The nonquasisimple branch of source 11.4.2. Canonical stars, radical
centralization, the complete nonquasisimple catalogue reduction, the literal
Frattini factorization and residual quotient, and Cartan normalization are
all discharged. Only the preceding source geometry and catalogue remain
with the parent comparison owner. -/
theorem ofFlag_eq_of_nonquasisimple
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hJ : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hR : (ofFlag S f X z H).R₁ ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K :=
  ofFlag_eq_of_stars_and_catalogue S f X z H h hA hseed hlinear h1132 hJ hn
    (ofFlag_canonicalRadicalsStarred S hJ hn) hR hline hXN hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
