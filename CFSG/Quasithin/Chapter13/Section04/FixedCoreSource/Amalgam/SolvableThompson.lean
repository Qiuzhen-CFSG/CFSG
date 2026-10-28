module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableOddPrimeExclusion
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Internal
public import Theory.GroupAction.MarkedCubicRecognition.SubnormalObstruction
public import Theory.Representation.NormalElementaryQuotient.Thompson

/-!
# Ordinary Thompson normality in the solvable noncommuting amalgam

A faithful solvable binary FF action with trivial two-core has an actual
subnormal S₃ factor by B.1.8. The marked Heisenberg extension has no such
subgroup. Its faithful binary actions are therefore non-FF. Apply the
normal elementary quotient criterion to the original omega span, using
the proved full kernel O₂(X), to obtain normality of J(T) in X.

This discharges the Thompson clause of 13.4.7(1iii) without assuming the
six-dimensional calculation. It concerns ordinary J(T); it does not
assert J₁(T) normality, the residual commutator, or the plane exclusion.
GeneralPairSource applies this clause to the actual general-pair consumer.

Source: Aschbacher--Smith 13.4.7, printed pp.901--902; B.1.8, p.70,
and B.2.5--8, p.76.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E]
  [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

private theorem heisenberg_nonFF (ρ : Representation (ZMod 2) H E)
    (hs : Group.IsSolvable H) (hc : pCore 2 H = ⊥) (hf : Function.Injective ρ)
    (e : H ≃* MarkedCubicRecognition.HeisenbergExtension) : ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨d⟩ := ChapterB.solvableFFStructure_nonempty ρ hs hc hf hff
  let i : Fin d.count := ⟨0,d.count_pos⟩
  let F := d.factor i
  let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
  have hF : F.IsSubnormal :=
    (d.toSolvableFFFactors.factor_normal_in_offenderSubgroup i).isSubnormal.trans
      (d.toSolvableFFFactors.factor_le_offenderSubgroup i)
      (inferInstance : (offenderSubgroup ρ).Normal).isSubnormal
  obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact MarkedCubicRecognition.SubnormalObstruction.no_subnormal_symmetricThree
    (F.map e.toMonoidHom) (hF.map e.surjective)
    ⟨(F.equivMapOfInjective e.toMonoidHom e.injective).symm.trans
      ((d.factorModel i).trans eS)⟩

/-- A reduced normal elementary module with the actual Heisenberg action
quotient forces ordinary elementary Thompson normality. -/
theorem thompson_normal_of_heisenberg_quotient
    {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (U : Subgroup X) (hr : IsPReduced 2 U)
    (hk : centralizer (U : Set X) = pCore 2 X)
    (hs : Group.IsSolvable X)
    (e : (X ⧸ pCore 2 X) ≃* MarkedCubicRecognition.HeisenbergExtension) :
    (elementaryAbelianMaxJ (S : Subgroup X)).Normal := by
  let : U.Normal := hr.normal
  let : IsElementaryAbelian 2 U := hr.elementary
  let : Group.IsSolvable X := hs
  let q := QuotientGroup.mk' (pCore 2 X)
  have hq := QuotientGroup.mk'_surjective (pCore 2 X)
  have hker : q.ker = centralizer (U : Set X) := by
    rw [QuotientGroup.ker_mk',hk]
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hc : pCore 2 (X ⧸ pCore 2 X) = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hn : ¬ IsFFModule ρ := heisenberg_nonFF ρ inferInstance hc
    (NormalElementaryQuotient.representation_injective U q hq hker) e
  have hk2 : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hUS : U ≤ (S : Subgroup X) :=
    (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S
  exact NormalElementaryQuotient.thompson_normal_of_nonFF S U q hq hker hk2 hUS hn

open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original solvable noncommuting branch normalizes J(T), using the
literal two-core quotient and the proved full omega-action kernel. -/
theorem original_pair_solvable_thompson_normal
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)) :
    A ⊔ B ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let X := A ⊔ B
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let U := W.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  let S := T.subtype hTX
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hr := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  obtain ⟨hk,⟨e⟩⟩ := original_pair_solvable_noncommuting_model h₀ D m
    hTA hTB eA eB hne hindexA hindexB hcentral hcores hs hcomm
  have hker : centralizer (U : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) U
    have hm : (centralizer (U : Set X)).map X.subtype = X ⊓ centralizer (W : Set G) := by
      simpa only [U,top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
        map_subgroupOf_eq_of_le hWX] using hh.symm
    exact hm.trans hk
  let := thompson_normal_of_heisenberg_quotient S U hr hker hs e
  have hn := (elementaryAbelianMaxJ (S : Subgroup X)).le_normalizer_map X.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hn
  exact hn

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
