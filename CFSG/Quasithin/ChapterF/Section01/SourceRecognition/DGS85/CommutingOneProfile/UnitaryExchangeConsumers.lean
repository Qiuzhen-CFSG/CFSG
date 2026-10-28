module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitarySourceSigns
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MarkedConsumers

/-!
# The nonelementary original-pair comparison from its apartment exchange

The source nonelementary full-Borel quotient selects the actual PSU3 or SU3
marking. The proved signs build the finite split quotient and its marked U5
comparison. The prepared original pair supplies both local catalogues by
nonsolvability, and Chapter 15 restores its original endpoints and entire
Borel, using the same selected perfect factor.

The Chapter 12 application retains full KnownSimple. The actual Cartan,
reflection involutions and apartment exchange are explicit earlier Chapter 14
inputs; their construction and unrestricted catalogue exclusion remain with
the complete source assembly. No unitary mark, quotient, rotation, split data
or root-sign assumption is added to these consumers.
Source: DGS, Groups and Graphs (1985), (11.8), pp.175--177,
Theorem D and (15.2), pp.224,226--228; Aschbacher--Smith F.1.12 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction OriginalExtension SuzukiContainment Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (models : ∀ i : Bool, IsRankOneModel
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
        (Reduction.G₀ L S).subtype ⧸ pCore 2
          ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
            (Reduction.G₀ L S).subtype)))
    (hne : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)
include h hc hb hcomm models hne c t htfix htmove htsq htnorm hexchange

/-- The nonelementary source selects its unitary marking and constructs the
marked reduced comparison. Only local catalogues and the original reflection
and exchange data remain as independent source inputs. -/
theorem original_nonElementary_reduced_comparison_of_exchange :
    ∃ (m : ℕ), 0 < m ∧ ∃ M : GreenBook.UnitaryFive.Model (2^m),
      Nonempty (Iso (reducedAmalgam L S) (UnitaryFiveNative.amalgam M false)) := by
  obtain ⟨m,hm,mark⟩ := original_borel_nonElementary_unitary_beta h hc hb hcomm
    (models false) (models true) hne
  obtain ⟨comparison⟩ := originalUnitaryFiniteComparisonOfExchange h hc hb hcomm
    (models false) hm mark c t htfix htmove htsq htnorm hexchange
  exact ⟨m,hm,comparison.model,⟨comparison.comparison⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- Restore the original pair from its literal nonelementary commuting-edge
branch. The prepared nonsolvable parabolics discharge the local catalogues;
the supplied reflections and exchange yield the marked reduced comparison. -/
theorem comparison_of_commuting_one_nonElementary_exchange
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false)
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true))
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥)
    (hne : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1
      ¬ IsElementaryAbelian 2 (reducedSylow ![L,R] (sourceS L H) ⧸
        ((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
          (reducedSylow ![L,R] (sourceS L H))))
    (c : CompatibleCartans ![L,R] (reducedSylow ![L,R] (sourceS L H)))
    (t : Bool → (reducedAmalgam ![L,R] (sourceS L H)).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam ![L,R] (sourceS L H))) i =
      base (Universal.cosetFamily (reducedAmalgam ![L,R] (sourceS L H))) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam ![L,R] (sourceS L H))) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam ![L,R] (sourceS L H))) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (ReducedCartan.cartan c : Set (reducedAmalgam ![L,R] (sourceS L H)).Universal))
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam ![L,R] (sourceS L H)).Universal)
      (sourceGraph (reducedAmalgam ![L,R] (sourceS L H)))
      (cartanApartment (reducedAmalgam ![L,R] (sourceS L H)) (ReducedCartan.reflectionGroup c t)) 4) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  let hf := d.hypothesisF11 h hTH
  let := QuadrangleStructure.original_core_normal_in_sylow
    (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1
  have hfull : ∃ hn : (((Q (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map
        (Reduction.G₀ ![L,R] (sourceS L H)).subtype).subgroupOf
          (twoCore (commonBorel ![L,R] (sourceS L H)))).Normal,
      letI := hn
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel ![L,R] (sourceS L H)) ⧸
        ((Q (Reduction.reducedFamily ![L,R] (sourceS L H))
          (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map
            (Reduction.G₀ ![L,R] (sourceS L H)).subtype).subgroupOf
              (twoCore (commonBorel ![L,R] (sourceS L H)))) := by
    have hq := (ChapterF.Source.DGS85.NoncommutingProfile.reduced_base_Q_map hf true).trans
      (reduced_parabolic_core hf 1).symm
    rw [hq]
    change ∃ hn : (((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
      (reducedSylow ![L,R] (sourceS L H))).Normal,
      letI := hn
      ¬ IsElementaryAbelian 2 (reducedSylow ![L,R] (sourceS L H) ⧸
        ((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
          (reducedSylow ![L,R] (sourceS L H)))
    exact ⟨QuadrangleStructure.original_core_normal_in_sylow
      (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1,hne⟩
  have models (i : Bool) : IsRankOneModel
      ((graphLocalGroup (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) i)).map
          (Reduction.G₀ ![L,R] (sourceS L H)).subtype ⧸ pCore 2
            ((graphLocalGroup (Reduction.reducedFamily ![L,R] (sourceS L H))
              (base (Reduction.reducedFamily ![L,R] (sourceS L H)) i)).map
                (Reduction.G₀ ![L,R] (sourceS L H)).subtype)) := by
    let a := (graphLocalGroup (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) i)).equivMapOfInjective
        (Reduction.G₀ ![L,R] (sourceS L H)).subtype (Reduction.G₀ ![L,R] (sourceS L H)).subtype_injective
    exact (Reduction.reduced_actor_models_of_nonsolvable_parabolics hf
      (d.parabolics_not_solvable h hp) (base (Reduction.reducedFamily ![L,R] (sourceS L H)) i)).of_equiv
        (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  obtain ⟨m,hm,M,⟨f⟩⟩ := original_nonElementary_reduced_comparison_of_exchange
    hf hc hb hcomm models hfull c t htfix htmove htsq htnorm hexchange
  exact d.concreteComparison_of_reduced_alternatives h hTH hp
    (.unitaryFive (2^m) (Nat.prime_two.isPrimePow.pow (Nat.ne_of_gt hm))
      (even_two.pow_of_ne_zero (Nat.ne_of_gt hm)) M false ⟨f⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false)
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true))
  (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
    Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥)
  (hne : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (Global.sourceS L H)) 1
    ¬ IsElementaryAbelian 2 (reducedSylow ![L,R] (Global.sourceS L H) ⧸
      ((parabolic ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)) 1).pCoreIn 2).subgroupOf
        (reducedSylow ![L,R] (Global.sourceS L H))))

    (c : CompatibleCartans ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)))
    (t : Bool → (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam ![L,R] (Global.sourceS L H))) i =
      base (Universal.cosetFamily (reducedAmalgam ![L,R] (Global.sourceS L H))) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam ![L,R] (Global.sourceS L H))) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam ![L,R] (Global.sourceS L H))) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (ReducedCartan.cartan c : Set (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal))
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
      (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H)))
      (cartanApartment (reducedAmalgam ![L,R] (Global.sourceS L H)) (ReducedCartan.reflectionGroup c t)) 4)
include D h hmany hn hpsl hH d hp hc hb hcomm hne c t htfix htmove htsq htnorm hexchange in
/-- The full KnownSimple chosen-module application on the same perfect factor.
Reflections and exchange remain explicit; no unitary marking, finite quotient,
profile, split data, rotation or root-sign premise is supplied. -/
theorem rankOne_comparison_of_commuting_one_nonElementary_exchange :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_commuting_one_nonElementary_exchange
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    hc hb hcomm hne c t htfix htmove htsq htnorm hexchange

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
