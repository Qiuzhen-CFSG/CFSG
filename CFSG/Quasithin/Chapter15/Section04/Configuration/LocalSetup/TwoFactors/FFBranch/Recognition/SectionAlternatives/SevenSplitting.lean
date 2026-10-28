module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.Source
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The literal four-dimensional moved space for an A₇ offender actor

The seven nonsplit natural rows of B.5.1(2) have different actual actors,
so an A₇ component forces a fixed complement. For an A₇ actor, the full
marked B.4.2 list leaves the four-dimensional exceptional section: the
natural seven-point row would embed S₇ into A₇. Its central subspace is
zero by the proved complement, hence the moved space itself has dimension
four. In an ambient A₇ FF action, simplicity identifies both the normal
offender subgroup and its component with the whole actor, transporting
these conclusions to the original module.

The original 13.2.12 point-action consumer uses this splitting before
applying the exceptional Baumann-image theorem to its moved subgroup.
Source: Aschbacher--Smith B.4.2(7), B.5.1(1)--(2), pp.86,99;
13.2.12, printed p.882.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.SourceSections.Seven
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives QuasisimpleComparison

private noncomputable def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,F.card_eq,h]
    simp)

private theorem seven_card {K : Type*} [Group K]
    (e : K ≃* alternatingGroup (Fin 7)) : Nat.card K = 2520 := by
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
  decide

private theorem seven_not_linearTwo {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) (F : BinaryField)
    (a : K ≃* SL(2,F.Carrier)) : False := by
  have hb := linearTwo_degree_le (SourceSections.small_sylow (.alternatingSeven e))
    F a.symm.toMonoidHom a.symm.injective
  have hc := seven_card e
  rw [Nat.card_congr a.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq] at hc
  interval_cases hn : F.degree <;> norm_num [hn] at hc

private theorem seven_not_linearThree {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) (F : BinaryField)
    (a : K ≃* SL(3,F.Carrier)) : False := by
  have hb := linearThree_degree_le (SourceSections.small_sylow (.alternatingSeven e))
    F a.symm.toMonoidHom a.symm.injective
  have hp := F.degree_pos
  have hc := seven_card e
  rw [Nat.card_congr a.toEquiv,
    card_eq_card_quotient_mul_card_subgroup (center SL(3,F.Carrier)),
    Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,
    Matrix.PSL3.LinearThree.card_projective_mul_scalar,F.card_eq] at hc
  interval_cases hn : F.degree <;> norm_num [hn] at hc

private theorem seven_not_symplectic {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) (F : BinaryField)
    (a : K ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hd := symplectic_degree_eq_one (SourceSections.small_sylow (.alternatingSeven e))
    F a.symm.toMonoidHom a.symm.injective
  let b := a.trans ((Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp
    (fieldTwoEquiv F hd)).trans
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm)
  have hc := seven_card e
  rw [Nat.card_congr b.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hc
  norm_num [Nat.factorial] at hc

private theorem seven_not_g2 {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) (F : BinaryField)
    (a : K ≃* Atlas.G2.Model F.Carrier) : False := by
  have hd := g2_degree_eq_one (SourceSections.small_sylow (.alternatingSeven e))
    F a.symm.toMonoidHom a.symm.injective
  have hc := seven_card e
  rw [Nat.card_congr (a.trans (Atlas.G2.fieldEquiv (fieldTwoEquiv F hd))).toEquiv,
    Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at hc
  omega

private theorem seven_not_alternating {K : Type*} [Group K] {n : ℕ}
    (hn : n = 6 ∨ n = 8) (e : K ≃* alternatingGroup (Fin 7))
    (a : K ≃* alternatingGroup (Fin n)) : False := by
  have hc := seven_card e
  rcases hn with rfl | rfl <;>
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hc <;>
    norm_num [Nat.factorial] at hc

private theorem seven_not_derivedG2 {K : Type*} [Group K]
    (e : K ≃* alternatingGroup (Fin 7))
    (a : K ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hc := seven_card e
  rw [Nat.card_congr a.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hc
  omega

/-- None of B.5.1(2)'s nonsplit natural actions has an A₇ actor. -/
theorem not_nonsplit {K W : Type*} [Group K] [Finite K]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) K W) (e : K ≃* alternatingGroup (Fin 7)) :
    ¬ NonsplitNatural ρ := by
  intro h
  cases h with
  | linearTwo F h => exact seven_not_linearTwo e F h.some.groupEquiv
  | symplectic F h => exact seven_not_symplectic e F h.some.groupEquiv
  | g2 F h => exact seven_not_g2 e F h.some.groupEquiv
  | alternatingSix h => exact seven_not_alternating (Or.inl rfl) e h.some.groupEquiv
  | alternatingEight h => exact seven_not_alternating (Or.inr rfl) e h.some.groupEquiv
  | derivedG2 h => exact seven_not_derivedG2 e h.some.groupEquiv
  | linearThree h => exact seven_not_linearThree e BinaryField.two h.some.groupEquiv

/-- The original B.5 moved space splits off its component-fixed space when
that component is actually A₇. The original central quotient is not discarded. -/
theorem source_split {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (K : Subgroup A)
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (e : K ≃* alternatingGroup (Fin 7)) :
    IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ K) := by
  by_contra hn
  exact not_nonsplit _ e (c.clause_two hn).2

/-- For an A₇ actor, the full irreducible source list forces the exceptional
four-dimensional central section; natural S₇ requires a larger marked actor. -/
theorem source_dimension {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W)
    (b : BoundedBranch ρ) (e : A ≃* alternatingGroup (Fin 7))
    (eK : generalizedFitting A ≃* alternatingGroup (Fin 7)) :
    Function.Injective b.source.sectionData.action ∧
      Module.finrank (ZMod 2) (b.source.sectionData.space.toSubmodule ⧸
        b.source.sectionData.central.toSubmodule) = 4 := by
  have ha : SmallActorModel A := .alternatingSeven e
  cases b.source.clause_one with
  | irreducible _ hf _ h _ =>
    refine ⟨hf,?_⟩
    cases h with
    | linearTwo F _ a _ _ => exact (seven_not_linearTwo eK F a.groupEquiv).elim
    | linearThree F _ a _ => exact (seven_not_linearThree eK F a.groupEquiv).elim
    | symplectic F _ _ a _ => exact (seven_not_symplectic eK F a.groupEquiv).elim
    | symplecticTwo a _ =>
      exact (seven_not_alternating (Or.inl rfl) eK
        (a.subgroupEquiv.trans binarySymplecticDerivedEquiv)).elim
    | g2 F _ _ a _ _ => exact (seven_not_g2 eK F a.groupEquiv).elim
    | g2Two a _ _ => exact (seven_not_derivedG2 eK a.subgroupEquiv).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (seven_not_linearTwo eK BinaryField.four
          (a.subgroupEquiv.trans alternatingFiveLinearEquiv)).elim
      · have hc := (offenderSubgroup b.source.sectionData.action).card_subgroup_dvd_card
        rw [Nat.card_congr a.action.groupEquiv.toEquiv,
          Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,seven_card e] at hc
        norm_num [Nat.factorial] at hc
    | alternatingSix _ a _ _ => exact (seven_not_alternating (Or.inl rfl) eK a.groupEquiv).elim
    | alternatingSeven _ _ _ hd _ _ => exact hd
    | tripleSix _ a _ =>
      have hc := seven_card eK
      rw [card_eq_card_quotient_mul_card_subgroup (center (generalizedFitting A)),
        Nat.card_congr a.quotientEquiv.toEquiv,Nat.card_congr a.centerEquiv.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin] at hc
      norm_num [Nat.factorial] at hc
    | binaryLinear d hd _ a _ =>
      exact (SourceSections.no_linearFourFive ha _ d hd a.groupEquiv).elim
    | orthogonalSix _ _ a _ _ => exact (seven_not_alternating (Or.inr rfl) eK a.groupEquiv).elim
    | symmetricEight _ a _ => exact (seven_not_alternating (Or.inr rfl) eK a.subgroupEquiv).elim
    | exteriorFive _ _ a _ _ _ =>
      exact (SourceSections.no_linearFourFive ha _ 5 (Or.inr rfl) a).elim
  | doubleThree F _ a _ _ => exact (seven_not_linearThree eK F a.groupEquiv).elim
  | naturalDual d hd _ h => exact (SourceSections.no_linearFourFive ha _ d hd h.some.groupEquiv).elim
  | repeatedNatural d _ hd _ _ _ h =>
    exact (SourceSections.no_linearFourFive ha _ d hd h.some.groupEquiv).elim

/-- In an A₇ action the normal offender actor and its component are the
whole actor. Thus the literal moved space has dimension four and a fixed
complement in the original module, not just in a section. -/
theorem offender_moved_split {E W : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (hff : IsFFModule ρ)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (e : E ≃* alternatingGroup (Fin 7)) :
    IsCompl (subspaceCommutator ρ ⊤ ⊤) (fixedSpace ρ ⊤) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⊤) = 4 := by
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup E := e.isSimpleGroup
  have hN : N = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance).resolve_left
    (offenderSubgroup_ne_bot_of_ff ρ hff)
  let eN : N ≃* alternatingGroup (Fin 7) :=
    ((MulEquiv.subgroupCongr hN).trans topEquiv).trans e
  let : IsSimpleGroup N := eN.isSimpleGroup
  let K := generalizedFitting N
  let : IsQuasisimple K := b.quasisimple
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hK : K = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K inferInstance).resolve_left
    ((nontrivial_iff_ne_bot K).mp inferInstance)
  let eK : K ≃* alternatingGroup (Fin 7) :=
    ((MulEquiv.subgroupCongr hK).trans topEquiv).trans eN
  have hmap : K.map N.subtype = ⊤ := by
    rw [hK,←MonoidHom.range_eq_map,range_subtype,hN]
  let s := b.source.sectionData
  have hsplit := source_split (ρ.comp N.subtype) K b.source eK
  have hcentral : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (disjoint_iff.mp hsplit.disjoint).le
      ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
  have hdim := (source_dimension (ρ.comp N.subtype) b eN eK).2
  have hspace : s.space.toSubmodule = subspaceCommutator ρ ⊤ ⊤ := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp N.subtype) ⊤ K = _
    rw [subspaceCommutator_comp_map,hmap]
  have heq := (s.central.toSubmodule.quotEquivOfEqBot hcentral).finrank_eq
  have hd : Module.finrank (ZMod 2) s.space.toSubmodule = 4 := heq.symm.trans hdim
  rw [hspace] at hd
  rw [show b.source.sectionData.space.toSubmodule = subspaceCommutator ρ ⊤ ⊤ from hspace,
    fixedSpace_comp_map,hmap] at hsplit
  exact ⟨hsplit,hd⟩

/-- The full marked B.4.2 list for an actual A₇ component leaves either
its exceptional four-space with no outer actor, or the marked natural S₇
section. This retains the full ambient action, not just its restriction. -/
theorem source_natural_or_exceptional {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (b : BoundedBranch ρ)
    (ha : SmallActorModel A)
    (eK : generalizedFitting A ≃* alternatingGroup (Fin 7)) :
    (generalizedFitting A = ⊤ ∧
      Module.finrank (ZMod 2) (b.source.sectionData.space.toSubmodule ⧸
        b.source.sectionData.central.toSubmodule) = 4) ∨
    Nonempty (MarkedActionEquiv b.source.sectionData.action
      (offenderSubgroup b.source.sectionData.action) (generalizedFitting A)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) := by
  cases b.source.clause_one with
  | irreducible _ hf _ h _ =>
    cases h with
    | linearTwo F _ a _ _ => exact (seven_not_linearTwo eK F a.groupEquiv).elim
    | linearThree F _ a _ => exact (seven_not_linearThree eK F a.groupEquiv).elim
    | symplectic F _ _ a _ => exact (seven_not_symplectic eK F a.groupEquiv).elim
    | symplecticTwo a _ =>
      exact (seven_not_alternating (Or.inl rfl) eK
        (a.subgroupEquiv.trans binarySymplecticDerivedEquiv)).elim
    | g2 F _ _ a _ _ => exact (seven_not_g2 eK F a.groupEquiv).elim
    | g2Two a _ _ => exact (seven_not_derivedG2 eK a.subgroupEquiv).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (seven_not_linearTwo eK BinaryField.four
          (a.subgroupEquiv.trans alternatingFiveLinearEquiv)).elim
      · exact Or.inr ⟨a⟩
    | alternatingSix _ a _ _ => exact (seven_not_alternating (Or.inl rfl) eK a.groupEquiv).elim
    | alternatingSeven _ h _ hd _ _ => exact Or.inl ⟨h,hd⟩
    | tripleSix _ a _ =>
      have hc := seven_card eK
      rw [card_eq_card_quotient_mul_card_subgroup (center (generalizedFitting A)),
        Nat.card_congr a.quotientEquiv.toEquiv,Nat.card_congr a.centerEquiv.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin] at hc
      norm_num [Nat.factorial] at hc
    | binaryLinear d hd _ a _ =>
      exact (SourceSections.no_linearFourFive ha _ d hd a.groupEquiv).elim
    | orthogonalSix _ _ a _ _ => exact (seven_not_alternating (Or.inr rfl) eK a.groupEquiv).elim
    | symmetricEight _ a _ => exact (seven_not_alternating (Or.inr rfl) eK a.subgroupEquiv).elim
    | exteriorFive _ _ a _ _ _ =>
      exact (SourceSections.no_linearFourFive ha _ 5 (Or.inr rfl) a).elim
  | doubleThree F _ a _ _ => exact (seven_not_linearThree eK F a.groupEquiv).elim
  | naturalDual d hd _ h => exact (SourceSections.no_linearFourFive ha _ d hd h.some.groupEquiv).elim
  | repeatedNatural d _ hd _ _ _ h =>
    exact (SourceSections.no_linearFourFive ha _ d hd h.some.groupEquiv).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.SourceSections.Seven
