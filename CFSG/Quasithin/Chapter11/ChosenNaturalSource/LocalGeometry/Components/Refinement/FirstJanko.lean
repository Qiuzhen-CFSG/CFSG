module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstJankoModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstTernary

/-!
# Excluding J₁ at the first flag normalizer

The actual PSL₂(4) marking identifies L₁/O₂(L₁) with A₅. Relative normality
of the containing component K supplies its normalization by T. The J₁
model generation theorem then puts K in ⟨L₁,N_G(T)⟩. The preceding bound
N_G(T) ≤ N_G(L), source Theorem 3.3.1, puts K in N_G(L), where component
uniqueness forces K = L₁. Thus the strict J₁ row is impossible.

The literal Cartan consumer retains the complete embedding disjunction
and leaves only SL₃(4) and PSL₃(4), besides the already proved refinement
alternatives. Construction of the field-four triangle, second-component
equality, exhaustive embeddings and final 11.1.1--11.1.3 assembly remain
with qt-d-1222-natural-relative-components. The preceding Sylow-normalizer
bound is supplied by qt-d-1222-natural-line-action; the flag and Cartan
facts by qt-d-1222-natural-flag-cartan. Their ultimate discharge remains
with qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
proof of 11.1.2, printed p.762, using Theorem 3.3.1.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The J₁ quotient forces the actual containing component into N_G(L),
using the earlier Sylow-normalizer bound from source Theorem 3.3.1. -/
theorem first_janko_le_component_normalizer
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K) (eK : (K ⧸ pCore 2 K) ≃* Janko1.Model) :
    K ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 by simpa [hfour] using hF)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  apply (Janko.containing_le_sup_normalizer T K (f.Li 0) hLK hTK
    (f.sylow_normalizes_Li 0) eK (e.trans a)).trans
  exact sup_le (((localResidual_le _).trans inf_le_left).trans L.le_normalizer) hNT

/-- The strict J₁ row is impossible in the original first normalizer. -/
theorem first_component_not_janko
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rintro ⟨eK⟩
  exact hLK.ne (flag_component_eq_of_le_component_normalizer D S f 0 hm hK.1 hLK.le
    (first_janko_le_component_normalizer D S f hm hfour hNT hK hLK.le eK))

/-- The first-normalizer Cartan sieve now leaves only SL₃(4) and PSL₃(4)
in addition to the already proved refinement alternatives. -/
theorem first_refinement_or_linearFour_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)) := by
  by_cases he : f.Li 0 = K
  · exact .inl (.equal (by simpa using he))
  rcases first_refinement_or_linearFour_or_janko_of_cartan D S f hu hm hfix hX hK hLK
    hXcard hfaith hk with h | ⟨hn,h⟩
  · exact .inl h
  · refine .inr ⟨hn,?_⟩
    rcases h with h | h | h
    · exact .inl h
    · exact .inr h
    · exact (first_component_not_janko D S f hm hn hNT hK (lt_of_le_of_ne hLK he) h).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
