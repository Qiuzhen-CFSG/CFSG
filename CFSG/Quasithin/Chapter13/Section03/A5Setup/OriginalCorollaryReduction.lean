module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
public import CFSG.Quasithin.Chapter10.Section03

/-!
# Stopping the uniform A₅ normalization argument at 10.2.13

Corollary 10.2.13 makes the original nonnormal component's two-core quotient
L₃(2). In the uniform A₅ branch this already contradicts its actual A₅
quotient. Thus the Chapter 13.6 normalization input needs only this earlier
corollary; the later replacement construction in Chapter 10, §3 is unnecessary.
The corollary itself retains its original source producer, including the
marked-module and weak-closure arguments of §10.2.

Source: Aschbacher–Smith, Corollary 10.2.13, printed p.755, and
Hypothesis 13.3.1(4), printed p.884.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}

/-- The exact universal normalization consumer follows already from original
10.2.13 restricted to A₅ in this branch; no Chapter 10 replacement
component or other quotient family is required. -/
theorem normalization_of_nonnormal_linearThree_source
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (h10213 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple S I →
      Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) →
      ¬ (S : Subgroup G) ≤ normalizer (I : Set G) →
      Nonempty ((I ⧸ pCore 2 I) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
      (S : Subgroup G) ≤ normalizer (I : Set G) := by
  apply normalization_of_A5_source h e
  intro S I hi hfive
  by_contra hn
  exact Chapter10.incompatible_replacement_quotient hfive (h10213 S I hi hfive hn)

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
