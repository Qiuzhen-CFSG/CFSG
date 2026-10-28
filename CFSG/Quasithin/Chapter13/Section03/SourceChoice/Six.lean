module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SixChoice
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource

/-!
# The literal A₆ choice in Hypothesis 13.3.1

For any original faithful local component K with two-core quotient A₆ or
its central three-cover, the cubic-rank obstruction proves T-normality.
The faithful reduced-module construction then selects an actual member of
Irr⁺(K,R₂(KT),T), inside O₂(K), with full K-commutator generation.

This discharges the normalization and existence part of the A₆ branch of
13.3.2 without using maximality or the universal 12.2.2 interface. It does
not assert T-invariance of the selected subgroup, the five-model catalogue,
or the natural/core representation classification.
Source: Aschbacher--Smith, Hypothesis 13.3.1 and 13.3.2(2--3), pp.884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1.Section02.LocalModels Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K : Subgroup G}

/-- Normalization and actual homogeneous choice for the A₆/three-cover branch
of the original universal local-component assertion. -/
theorem Hypothesis1331.six_chosen_setup
    (h : Hypothesis1331 T L)
    (hK : K ∈ MainForward.faithfulLocalComponents T)
    (hm : IsAlternating (K ⧸ pCore 2 K) 6 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 6) :
    (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T K V) ∧
        IsElementaryAbelian 2 V ∧ V ≠ ⊥ ∧ V ≤ K.pCoreIn 2 ∧
        K ≤ normalizer (V : Set G) ∧ V = ⁅V,K⁆ := by
  obtain ⟨hn,V,⟨D⟩⟩ := faithful_local_six_exists_chosen h.qtke hK hm
  exact ⟨hn,V,⟨D⟩,D.elementary,D.ne_bot,D.le_componentCore,D.normalizes,D.eq_commutator⟩

/-- In particular, the originally selected L has the same actual choice. -/
theorem Hypothesis1331.exists_six_chosen
    (h : Hypothesis1331 T L)
    (hm : IsAlternating (L ⧸ pCore 2 L) 6 ∨ IsAlternatingCover (L ⧸ pCore 2 L) 6) :
    ∃ V : Subgroup G, Nonempty (ChosenModule T L V) ∧
      IsElementaryAbelian 2 V ∧ V ≠ ⊥ ∧ V ≤ L.pCoreIn 2 ∧
      L ≤ normalizer (V : Set G) ∧ V = ⁅V,L⁆ :=
  (h.six_chosen_setup h.local_component hm).2

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
