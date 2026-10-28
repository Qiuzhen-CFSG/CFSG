module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Normalized
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicFactors
public import Theory.GroupTheory.ComponentLocalOrbitComplement
public import Theory.GroupTheory.PResidual.ConjugateSpanNormalizer
/-!
# Restricting the cubic orbit to the original source parabolic

For every source parabolic P, the two-residual of P₀=⟨P,S⟩ is the
S-orbit of the embedded O²(P). In an ordinary component, distinct orbit
factors commute. Thus O²(P) has a commuting complement in O²(P₀).
If a moving A₃ block exists and P₀ is minimal parabolic, the already
proved orbit theorem identifies O²(P₀) with A₄ or A₄ × A₄. Its commuting
factor classification then gives actual A₃ factors in the original P,
contradicting the literal source exclusion.

The same universal characteristic pair now proves ordinary placement
conditionally only on minimality of the literal closures. S need not
normalize L. Minimality and the constrained-component restriction remain
with the source assembly owner qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 15.1.22(*), printed pp.1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem IsSourceParabolic.closure_residual_orbit
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hL : d.L ∈ Chapter1.L G d.S) :
    (pResidual 2 (d.parabolicClosure P)).map (d.parabolicClosure P).subtype =
      componentOrbit ((pResidual 2 P).map P.subtype) d.S := by
  let E := (pResidual 2 P).map P.subtype
  have hgen : E ⊔ d.S = d.parabolicClosure P := by
    have hs := hP.residual_sup_sylow_intersection hL
    rw [←twoResidual_eq_primeToResidual_three hP.twoThree] at hs
    change E ⊔ (d.S ⊓ P) = P at hs
    change E ⊔ d.S = P ⊔ d.S
    calc
      E ⊔ d.S = (E ⊔ (d.S ⊓ P)) ⊔ d.S := by
        rw [sup_assoc, sup_eq_right.mpr (show d.S ⊓ P ≤ d.S from inf_le_left)]
      _ = P ⊔ d.S := congrArg (· ⊔ d.S) hs
  rw [Subgroup.embedded_pResidual_eq_conjugateSpanBy E d.S (d.parabolicClosure P)
    (embedded_pResidual_mono 2 (show P ≤ d.parabolicClosure P from le_sup_left))
    (T.isPGroup'.to_le d.S_le_T) hgen,conjugateSpanBy_eq_iSup_conj]
  rfl

/-- Restrict the actual cubic residual model along the original ordinary
component. Its other orbit factors provide the required commuting complement. -/
theorem IsSourceParabolic.aThree_product_of_ordinary_closure_model
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hL : d.L ∈ Chapter1.L G d.S)
    (hcL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (ha : ChapterC.IsAlternatingBlock AlternatingFourPair.A 3)
    (hm : Nonempty (pResidual 2 (d.parabolicClosure P) ≃* AlternatingFourPair.A) ∨
      Nonempty (pResidual 2 (d.parabolicClosure P) ≃* AlternatingFourPair.Model)) :
    IsAThreeProduct P := by
  let E := (pResidual 2 P).map P.subtype
  let N := componentOrbit E d.S
  have hEN : E ≤ N := le_componentOrbit E d.S
  have hEL : E ≤ d.L := (map_subtype_le _).trans hP.le_component
  have hnorm : d.S ⊓ normalizer (d.L : Set G) ≤ normalizer (E : Set G) :=
    hP.normalized.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  obtain ⟨C,hCN,hEC,hgen⟩ := hcL.relative_local_orbit_commuting_complement
    d.L_component.1 hEL d.S_le_G1 hnorm
  let eN : pResidual 2 (d.parabolicClosure P) ≃* N :=
    ((pResidual 2 (d.parabolicClosure P)).equivMapOfInjective
      (d.parabolicClosure P).subtype (d.parabolicClosure P).subtype_injective).trans
        (MulEquiv.subgroupCongr (hP.closure_residual_orbit hL))
  have hmN : Nonempty (N ≃* AlternatingFourPair.A) ∨
      Nonempty (N ≃* AlternatingFourPair.Model) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      exact Or.inl ⟨eN.symm.trans e⟩
    · obtain ⟨e⟩ := hm
      exact Or.inr ⟨eN.symm.trans e⟩
  have hcomm : E.subgroupOf N ≤ centralizer (C.subgroupOf N : Set N) := by
    intro e he c hc
    exact Subtype.ext (hEC he c hc)
  have hjoin : E.subgroupOf N ⊔ C.subgroupOf N = ⊤ := by
    rw [←subgroupOf_sup hEN hCN,hgen,subgroupOf_self]
  have hmodel := AlternatingFourPair.commuting_factor_model
    (E.subgroupOf N) (C.subgroupOf N) hcomm hjoin hmN
  let eE : pResidual 2 P ≃* E.subgroupOf N :=
    ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (subgroupOfEquivOfLe hEN).symm
  have hr : pResidual 2 P = ⊥ ∨ Nonempty (pResidual 2 P ≃* AlternatingFourPair.A) ∨
      Nonempty (pResidual 2 P ≃* AlternatingFourPair.Model) := by
    rcases hmodel with hz | hm
    · left
      apply le_bot_iff.mp
      intro x hx
      have he : eE ⟨x,hx⟩ = 1 := Subtype.ext (mem_bot.mp (hz ▸ (eE ⟨x,hx⟩).property))
      exact mem_bot.mpr (congrArg Subtype.val (eE.injective (he.trans (map_one eE).symm)))
    · right
      rcases hm with hm | hm
      · obtain ⟨e⟩ := hm
        exact Or.inl ⟨eE.trans e⟩
      · obtain ⟨e⟩ := hm
        exact Or.inr ⟨eE.trans e⟩
  exact alternatingThree_factors_in_subnormal (pResidual 2 P)
    (inferInstance : (pResidual 2 P).Normal).isSubnormal ha hr

/-- Ordinary components cannot contain the moving A₃ block once the literal
closure is minimal parabolic. No normalization of L by S is assumed. -/
theorem PreExclusionSource.no_moving_block_of_ordinary_minimal
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hcL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (R : Sylow 2 (d.parabolicClosure P))
    (hmin : IsMinimalParabolicOver R ⊤) :
    ¬ HasMovingAThreeBlock (d.parabolicClosure P) R := by
  rintro ⟨A,hb,ha,_⟩
  have hfit := s.parabolicClosure_fitting (h := h) hP
  have hr := (hP.closure_sqtk hG h).stronglyQuasithin 3 Nat.prime_three (by decide)
  have he := alternatingThree_orbit_eq_residual hfit hr R hmin A hb ha
  have hm := (cubic_orbit_models hfit hr R A hb ha).2
  rw [he] at hm
  obtain ⟨e⟩ := ha.equiv_alternatingFour
  exact hP.not_aThree_product (hP.aThree_product_of_ordinary_closure_model
    s.local_component hcL (ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e ha) hm)
/-- The same universal pair yields placement in the ordinary branch.
Only minimality of each literal closure remains to be established by the
source assembly; the moving-block restriction is discharged here. -/
theorem PreExclusionSource.parabolic_placement_of_ordinary_minimal
    {d : CaseIComponentData T M Mc V} {p : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized p)
    (hcL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hminimal : ∀ P ∈ d.sourceParabolics, ∀ R : Sylow 2 (d.parabolicClosure P),
      (R : Subgroup (d.parabolicClosure P)).map (d.parabolicClosure P).subtype = d.S →
      IsMinimalParabolicOver R ⊤) :
    ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML := by
  obtain ⟨D,hD,_⟩ := FixedPair.exists_uniform_pair.{u,u}
    T (MainForward.sylow_ne_bot hG T)
  have hB := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.1
  intro P hP
  obtain ⟨R,hR⟩ := s.parabolicClosure_sylow (h := h) hP
  have hm := hminimal P hP R hR
  have hi : ParabolicClosureStructure (d.parabolicClosure P) R :=
    ⟨hm,s.parabolicClosure_fitting (h := h) hP,hP.closure_solvable⟩
  by_cases hc : FixedPair.firstSeed R (d.localPair D (d.parabolicClosure P) R hR hB) ≤
      center (d.parabolicClosure P)
  · exact d.placement_of_localPair_alternative hG hM hJ hu h D
      (d.parabolicClosure P) P le_sup_left hP.le_component R hR hB (Or.inl hc)
  by_cases hn : ((d.localPair D (d.parabolicClosure P) R hR hB).second.map
      (baumann (R : Subgroup (d.parabolicClosure P))).subtype).Normal
  · exact d.placement_of_localPair_alternative hG hM hJ hu h D
      (d.parabolicClosure P) P le_sup_left hP.le_component R hR hB (Or.inr hn)
  exact (s.no_moving_block_of_ordinary_minimal (h := h) hG hcL hP R hm
    (hP.moving_block_of_no_pair_alternative hG h R hR hB D hD hi hc hn)).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
