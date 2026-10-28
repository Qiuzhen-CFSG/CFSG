module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.Contracts
public import Theory.GroupTheory.PrimeRankElementary

/-!+# Local group inputs for the Rudvalis normalizer exclusion

The low-displacement class is the class of the literal marked element `b²`.
Its centralizers must be maximal, with double centralizer of order at most
two. Together with the two-rank bound six these are the group-theoretic
inputs to the common-fixed-space argument. None is asserted by definition.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
Ru paragraph, manuscript p.17; GLS3 Tables 5.3r and 5.6.1.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion
open Subgroup

def standardA : standardGroup :=
  ⟨generatorA, subset_closure (Set.mem_insert _ _)⟩

def standardB : standardGroup :=
  ⟨generatorB, subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- Only the class with possible moved dimension twelve needs maximality.
The centralizers and double centralizers are in the actual matrix group. -/
def LowInvolutionCentralizers : Prop :=
  ∀ t : standardGroup, IsConj t (standardB ^ 2) →
    IsCoatom (centralizer ({t} : Set standardGroup)) ∧
      Nat.card (centralizer (centralizer ({t} : Set standardGroup) : Set standardGroup)) ≤ 2

/-- The independent finite group calculation used by the source argument. -/
def LocalStructure : Prop :=
  primeRank 2 standardGroup ≤ 6 ∧ LowInvolutionCentralizers

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion
