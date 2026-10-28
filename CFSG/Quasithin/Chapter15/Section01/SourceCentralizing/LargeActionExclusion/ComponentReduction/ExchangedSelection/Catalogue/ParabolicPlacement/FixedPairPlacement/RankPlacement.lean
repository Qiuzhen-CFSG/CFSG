module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Source
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedSource
public import Theory.GroupTheory.WreathTwoThreeCore
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Placement from the component's three-rank and the literal wreath quotient

Adjoining a normalizing two-group does not increase three-rank. Hence an
S₃-wreath quotient of P N_S(L) forces three-rank at least two in P and L.
The SQTK normality theorem applies inside the actual G₁ and proves that L
is normal there, for ordinary as well as constrained C-components. It
therefore supplies S-normalization to the existing universal-pair argument.
All literal closures are minimal parabolic and every source parabolic is
placed in M ∩ L or M_L. No normalization or moving-block premise is assumed.

The unproved branch of (*) is narrowed to a moved component of three-rank
at most one, with S₃ quotient for every source parabolic. Its closure and
residual arguments remain with qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 15.1.22(*), pp.1098--1099, and 1.2.1(3), p.504.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem threeRank_join_twoGroup_le (P A : Subgroup G)
    (hA : IsPGroup 2 A) (hn : A ≤ normalizer (P : Set G)) :
    primeRank 3 (P ⊔ A : Subgroup G) ≤ primeRank 3 P := by
  let X := P ⊔ A
  let B := P.subgroupOf X
  let C := A.subgroupOf X
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hgen : B ⊔ C = ⊤ := by
    rw [←subgroupOf_sup (show P ≤ X from le_sup_left)
      (show A ≤ X from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (X ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B C hA.comap_subtype hgen
  have hres : pResidual 2 X ≤ B := sInf_le ⟨inferInstance,hquot⟩
  calc
    primeRank 3 X = primeRank 3 (pResidual 2 X) :=
      (ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)).symm
    _ ≤ primeRank 3 B := primeRank_mono 3 hres
    _ = primeRank 3 P := primeRank_congr 3 (subgroupOfEquivOfLe le_sup_left)

/-- The literal wreath quotient forces three-rank two inside P itself,
not merely in P N_S(L). -/
theorem IsSourceParabolic.two_le_threeRank_of_wreath
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (he : Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    2 ≤ primeRank 3 P := by
  obtain ⟨e⟩ := he
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let ew := e.trans (RegularWreathProduct.congr eSL.symm
    (MulEquiv.refl (Multiplicative (ZMod 2))))
  let := WreathTwoResidual.threeCore_elementary
  have hr : 2 ≤ primeRank 3 WreathTwoResidual.Actor :=
    IsElementaryAbelian.primeRank_ge_of_card _ WreathTwoResidual.threeCore_card
  have hq : 2 ≤ primeRank 3 ((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) := by
    rwa [primeRank_congr 3 ew]
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup] at hq
  exact hq.trans (threeRank_join_twoGroup_le P d.sylowNormalizer
    (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) hP.normalized)

/-- A source component of three-rank at least two is normal in G₁.
The SQTK theorem applies in the actual marked centralizer. -/
theorem component_normal_of_threeRank
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hr : 2 ≤ primeRank 3 d.L) : (d.L.subgroupOf d.G1).Normal := by
  let := h.elementary
  let : IsElementaryAbelian 2 d.Z1 :=
    IsElementaryAbelian.of_le (d.Z1_le_fixed.trans inf_le_left)
  have hs := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    (IsElementaryAbelian.isPGroup 2 d.Z1)
  apply Chapter1.Section02.rank_two_component_normal hs d.L_component.2
  rwa [primeRank_congr 3 (subgroupOfEquivOfLe d.L_component.1)]

/-- Normalization is a consequence of rank, including in the constrained case. -/
theorem sylow_normalizes_of_threeRank
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hr : 2 ≤ primeRank 3 d.L) : d.S ≤ normalizer (d.L : Set G) :=
  d.S_le_G1.trans ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp
    (d.component_normal_of_threeRank hG h hr))

/-- A single wreath parabolic proves normalization of the original component. -/
theorem IsSourceParabolic.sylow_normalizes_of_wreath
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (he : Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    d.S ≤ normalizer (d.L : Set G) :=
  d.sylow_normalizes_of_threeRank hG h
    ((hP.two_le_threeRank_of_wreath he).trans (primeRank_mono 3 hP.le_component))

/-- If S permutes the component, every source parabolic has the S₃ quotient;
the wreath case is excluded by an actual rank calculation. -/
theorem IsSourceParabolic.symmetricThree_of_sylow_not_normalizes
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hn : ¬ d.S ≤ normalizer (d.L : Set G)) :
    Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃* Equiv.Perm (Fin 3)) :=
  hP.quotient.resolve_right (fun he => hn (hP.sylow_normalizes_of_wreath hG h he))

/-- The remaining moved-component branch has three-rank at most one. -/
theorem threeRank_le_one_of_sylow_not_normalizes
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hn : ¬ d.S ≤ normalizer (d.L : Set G)) : primeRank 3 d.L ≤ 1 := by
  by_contra! hr
  exact hn (d.sylow_normalizes_of_threeRank hG h (by omega))

/-- Rank supplies all three structural inputs on each literal closure,
including minimality, in both component branches. -/
theorem PreExclusionSource.parabolicClosure_structure_of_threeRank
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hr : 2 ≤ primeRank 3 d.L) {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (R : Sylow 2 (d.parabolicClosure P)) :
    ParabolicClosureStructure (d.parabolicClosure P) R :=
  ⟨hP.closure_minimal_of_sylow_normalizes (d.sylow_normalizes_of_threeRank hG h hr) R,
    s.parabolicClosure_fitting (h := h) hP, hP.closure_solvable⟩

/-- The same universal characteristic pair proves (*) for every source
parabolic whenever the marked component has three-rank at least two. -/
theorem PreExclusionSource.parabolic_placement_of_threeRank
    {d : CaseIComponentData T M Mc V} {p : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized p)
    (hr : 2 ≤ primeRank 3 d.L) :
    ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML :=
  s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h
    (d.sylow_normalizes_of_threeRank hG h hr)

/-- One literal wreath quotient discharges placement for the whole family,
including its S₃ members. No ordinary-component hypothesis is needed. -/
theorem PreExclusionSource.parabolic_placement_of_wreath
    {d : CaseIComponentData T M Mc V} {p : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized p)
    {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (he : Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    ∀ Q ∈ d.sourceParabolics, Q ≤ M ⊓ d.L ∨ Q ≤ d.ML :=
  s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h
    (hP.sylow_normalizes_of_wreath hG h he)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
