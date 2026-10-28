module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableCubicSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableMarkedCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicExclusion

/-!
# Excluding the original prime-three decomposable row

The original decomposable action produces the same cubic nonsylow marked
component and its C.2.7 input. Its literal marked centralizer is the full
centralizer of the original sixteen-element Thompson fixed subgroup.
The proved marked cubic-source exclusion therefore contradicts this row.
The original 15.1.14 conclusions follow for this impossible branch.

The component, original fixed group, radical, and quotient marking are
unchanged. No global residual assertion or extra reconstruction premise
is assumed. The prime-five decomposable branch remains separate.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original full prime-three decomposable source is impossible, using
its actual cubic component and elementary marked centralizer. -/
theorem PreparedChosenModule.false_of_decomposable_three_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 3 →
      False := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hthree
  obtain ⟨e,heZ,_,_,es,_,_,_,_,hz,_,hi,hms,_,_,t,_⟩ :=
    h.decomposable_three_cubic_nonsylow_source_without_residual
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hthree
  have hMZ := (h.decomposable_three_marked_core_geometry
    hG T hempty hM hJ hu hne hfull c d hd s π hp hs hdec hthree e heZ es).1
  let : IsElementaryAbelian 2 (thompsonFixed T V) := IsElementaryAbelian.of_le inf_le_left
  exact es.false_of_cubic_marked_source (h := h) hG hM hu hi hms
    (thompsonFixed T V) hMZ t hz

/-- All original 15.1.14 clauses in the excluded prime-three decomposable row. -/
theorem PreparedChosenModule.source_lemma_15_1_14_of_decomposable_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 3 →
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
          (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G) ∧
      M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T V : Set G) ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hthree
  exact (h.false_of_decomposable_three_source
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hthree).elim

end CFSG.Quasithin.Chapter15.Section01
