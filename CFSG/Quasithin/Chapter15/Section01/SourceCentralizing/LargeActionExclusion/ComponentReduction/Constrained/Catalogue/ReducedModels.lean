module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherLinear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherSymplectic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherG2
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SymplecticSource

/-!
# The reduced FF group catalogue on the whole local family

The actual B.5 source classifier is restricted by the natural and
doubled-natural linear-three exclusions and the proved symplectic and G₂
exclusions. The symplectic argument now uses the actual natural moved
section to preserve both parabolic types for every K in L(G₁,S); it needs
no ambient C-componenthood or C.2.7 parabolic premise. It leaves rank-one groups, the binary rank-two groups, the
alternating rows through degree eight, SL₅(2), and the cubic A₆ cover.
Every alternative has an actual isomorphism on the original normalizer
image; the cover retains both its center and its central quotient.

The original pre-exclusion and exchanged-source consumers discharge all
field-exclusion premises. Their marker application retains Z₁, row and
prime. This is the group portion of the constrained catalogue: general
local-family Borel placement, finite block recognition and the actual
parabolic and centralizer clauses remain with this task before assembly
of ConstrainedAlternatives. Original 15.1.14 retains its existing producer
and pre-exclusion assembly owner.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095, and B.5.1,
pp.99--103. The elementary group extraction follows the existing
ChapterC.C27Source.StarModels proof, retaining its concrete isomorphisms.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ProjectiveLine

/-- The actual FF image after higher-field rank-two elimination. Every row
retains an isomorphism, including the actual cubic cover in the last row. -/
inductive ReducedFFModel (A : Type*) [Group A] : Prop
  | linearTwo (F : BinaryField) (equiv : A ≃* SL(2,F.Carrier))
  | linearThree (equiv : A ≃* SL(3,ZMod 2))
  | g2DerivedTwo (equiv : A ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | alternating (n : ℕ) (degree : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
      (equiv : A ≃* alternatingGroup (Fin n))
  | linearFiveTwo (equiv : A ≃* SL(5,ZMod 2))
  | tripleSix (centerEquiv : center A ≃* Multiplicative (ZMod 3))
      (quotientEquiv : (A ⧸ center A) ≃* alternatingGroup (Fin 6))

private noncomputable def binaryThreeEquiv (F : BinaryField) (hF : F.degree = 1) :
    SL(3,F.Carrier) ≃* SL(3,ZMod 2) := by
  let := Fintype.ofFinite F.Carrier
  have hc : Fintype.card F.Carrier = 2 := by
    rw [←Nat.card_eq_fintype_card,F.card_eq,hF]
    rfl
  let a : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two hc).symm
  exact Atlas.fieldEquivSL 3 a

variable {D : Type*} [Group D] [Finite D]
private noncomputable def binarySymplecticDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private noncomputable def binaryFourAlternatingEquiv :
    SL(4,ZMod 2) ≃* alternatingGroup (Fin 8) :=
  Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
variable {L J : Subgroup D}
variable {E : Type*} [Group E]

private theorem binary_linear {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : E ≃* SL(d,ZMod 2)) : ReducedFFModel E := by
  rcases hd with rfl | rfl
  · exact .alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (e.trans binaryFourAlternatingEquiv)
  · exact .linearFiveTwo e

omit [Finite D] in
private theorem irreducible_model (e : E ≃* L)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L J)
    (hlinear : ∀ F : BinaryField, ActionEquiv (ρ.comp L.subtype) (linearNatural F 3) → F.degree = 1)
    (hsp : ∀ (F : BinaryField), 1 < F.degree →
      ActionEquiv (ρ.comp L.subtype) (binarySymplectic F) → False)
    (hg2 : ∀ (F : BinaryField), 1 < F.degree → ¬ Nonempty (E ≃* Atlas.G2.Model F.Carrier)) : ReducedFFModel E := by
  cases h with
  | linearTwo F _ a _ _ => exact .linearTwo F (e.trans a.groupEquiv)
  | linearThree F _ a _ => exact .linearThree ((e.trans a.groupEquiv).trans (binaryThreeEquiv F (hlinear F a)))
  | symplectic F large _ a _ => exact (hsp F large a).elim
  | symplecticTwo a _ =>
    exact .alternating 6 (Or.inr (Or.inl rfl)) (e.trans (a.subgroupEquiv.trans binarySymplecticDerivedEquiv))
  | g2 F large _ a _ _ => exact (hg2 F large ⟨e.trans a.groupEquiv⟩).elim
  | g2Two a _ _ => exact .g2DerivedTwo (e.trans a.subgroupEquiv)
  | symmetric n hn a _ _ =>
    apply ReducedFFModel.alternating n _ (e.trans a.subgroupEquiv)
    rcases hn with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  | alternatingSix _ a _ _ => exact .alternating 6 (Or.inr (Or.inl rfl)) (e.trans a.groupEquiv)
  | alternatingSeven _ _ a _ _ _ => exact .alternating 7 (Or.inr (Or.inr (Or.inl rfl))) (e.trans a)
  | tripleSix _ a _ =>
    have hc : (center E).map e.toMonoidHom = center L := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
    exact .tripleSix ((centerCongr e).trans a.centerEquiv)
      ((QuotientGroup.congr _ _ e hc).trans a.quotientEquiv)
  | binaryLinear d hd _ a _ => exact binary_linear hd (e.trans a.groupEquiv)
  | orthogonalSix _ _ a _ _ =>
    exact .alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (e.trans a.groupEquiv)
  | symmetricEight _ a _ =>
    exact .alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (e.trans a.subgroupEquiv)
  | exteriorFive _ _ a _ _ _ => exact .linearFiveTwo (e.trans a)

omit [Finite D] in
private theorem reduced_model_of_source (e : E ≃* L)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hlinear : ∀ F : BinaryField,
      ActionEquiv (c.sectionData.action.comp L.subtype) (linearNatural F 3) → F.degree = 1)
    (hdouble : ∀ F : BinaryField,
      ActionEquiv (c.sectionData.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2) → F.degree = 1)
    (hsp : ∀ (F : BinaryField), 1 < F.degree →
      ActionEquiv (c.sectionData.action.comp L.subtype) (binarySymplectic F) → False)
    (hg2 : ∀ (F : BinaryField), 1 < F.degree → ¬ Nonempty (E ≃* Atlas.G2.Model F.Carrier)) :
    ReducedFFModel E := by
  cases c.clause_one with
  | irreducible _ _ _ source _ => exact irreducible_model _ e source hlinear hsp hg2
  | doubleThree F _ a _ _ =>
    exact .linearThree ((e.trans a.groupEquiv).trans (binaryThreeEquiv F (hdouble F a)))
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact binary_linear hd (e.trans a.groupEquiv)
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact binary_linear hd (e.trans a.groupEquiv)

open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- All higher-field rank-two rows are eliminated on every eligible member
of the original local family. No ambient C-component or marked-parabolic
hypothesis is imposed on K. -/
theorem localFamily_reduced_ff_model
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) : ReducedFFModel (d.normalizerImage K) := by
  obtain ⟨a,hLJ,c,hl,hd⟩ := d.localFamily_linear_source_rows_binary hG hempty hM hJ hu h hK hq hout hf
  let := a.reduced.elementary
  exact reduced_model_of_source _ (subgroupOfEquivOfLe hLJ).symm c hl hd
    (fun F hn e => d.localFamily_symplectic_source_impossible hG hempty hM hJ hu h hK hq hout
      a _ hLJ c.sectionData F hn e)
    (fun F hn he => d.localFamily_normalizerImage_not_G2 hG hempty hM hJ hu h hK hq hout hf hn
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,he⟩)

/-- The original component has the reduced actual FF group catalogue before
prime exclusion. All higher-field rank-two rows have been discharged. -/
theorem PreExclusionSource.constrained_reduced_ff_model
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) : ReducedFFModel (d.normalizerImage d.L) := by
  exact d.localFamily_reduced_ff_model hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

/-- The exchanged selection has the same reduced catalogue on either plane size. -/
theorem ExchangedSource.constrained_reduced_ff_model
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) : ReducedFFModel (d.normalizerImage d.L) := by
  exact d.localFamily_reduced_ff_model hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Actual original-marker consumer of the reduced FF group catalogue,
retaining its Z₁, row and prime. Original 15.1.14 remains explicit for its
existing producer and pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_reduced_ff_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        CaseIComponentData.ReducedFFModel (d.normalizerImage d.L)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf =>
    s.constrained_reduced_ff_model (h := h) hG hempty hM hJ hu hf⟩

/-- Original-marker application to every eligible K in the fixed L(G₁,S),
for either source prime. The selected component and all original data remain
unchanged; no component record is manufactured for K. -/
theorem PreparedChosenModule.source_preExclusion_local_reduced_ff_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          CaseIComponentData.ReducedFFModel (d.normalizerImage K) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun _ hK hq hout hf =>
    d.localFamily_reduced_ff_model hG hempty hM hJ hu h hK hq hout hf⟩
end CFSG.Quasithin.Chapter15.Section01
