module
public import Theory.SpecificGroups.PSL2.PrimeSylowComponents
public import Theory.GroupTheory.CComponent.UniqueResidual
public import Theory.GroupTheory.CComponent.SimpleImageKernel
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel

/-!
# Radical images of contained outside components

Restrict the actual radical quotient of K to a nontrivial perfect subgroup I.
Its kernel is solvable, and Dickson's theorem identifies the nonsolvable
image as full prime PSL₂ or A₅. Full-Sylow component uniqueness lifts through
the radical and a solvable Sylow supplement, proving normality inside H.
It does not identify components lying in different Sylow overgroups.

For a normal H-component with prime PSL₂ radical quotient above five,
its image is the simple generalized Fitting subgroup of H/rad(H).
The proved prime-field E.1.14 calculation and solvable-kernel lifting
then give n(H)≤1. CoreImage applies these results to the original flag,
retaining the full solvable and central-cover kernels.
Source: Aschbacher--Smith A.3.12(8), E.1.14(6), and 11.4.4,
printed pp.47--48,214,778 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem radical_eq_bot_of_simple {A : Type*} [Group A] [Finite A]
    [IsSimpleGroup A] (hs : ¬ Group.IsSolvable A) : solvableRadical A = ⊥ := by
  rcases (inferInstance : (solvableRadical A).Normal).eq_bot_or_eq_top with hh | hh
  · exact hh
  · have htop : Group.IsSolvable (⊤ : Subgroup A) := hh ▸ inferInstanceAs
      (Group.IsSolvable (solvableRadical A))
    let := htop
    exact (hs (Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom) topEquiv.surjective)).elim

/-- The radical quotient of an actual perfect subgroup of a prime-field
rank-one component is the full prime model or A₅. The quotient map is
restricted from the original K; no abstract family tag is used. -/
theorem perfect_subgroup_radical_prime_models
    (I K : Subgroup G) [Group.IsPerfect I] (hI : I ≠ ⊥) (hIK : I ≤ K)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ solvableRadical K) 2 p) :
    ClassicalGroup.IsPSL (I ⧸ solvableRadical I) 2 p ∨
      Nonempty ((I ⧸ solvableRadical I) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let q := QuotientGroup.mk' (solvableRadical K)
  let a := e.toMonoidHom.comp (q.comp (inclusion hIK))
  have hker : a.ker = (solvableRadical K).comap (inclusion hIK) := by
    ext i
    change e (q (inclusion hIK i)) = 1 ↔ inclusion hIK i ∈ solvableRadical K
    rw [map_eq_one_iff _ e.injective]
    exact QuotientGroup.eq_one_iff _
  let j : a.ker →* solvableRadical K :=
    ((inclusion hIK).comp a.ker.subtype).codRestrict _ (by
      intro x
      exact hker.le x.property)
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext ((inclusion_injective hIK) (congrArg Subtype.val hh))
  let : Group.IsSolvable a.ker := Group.isSolvable_of_isSolvable_injective hj
  have hns : ¬ Group.IsSolvable a.range := by
    intro hh
    let := hh
    let : Nontrivial I := (nontrivial_iff_ne_bot I).mpr hI
    have hi : Group.IsSolvable I := Group.isSolvable_of_ker_le_range
      a.ker.subtype a.rangeRestrict (by intro i hi; exact ⟨⟨i,congrArg Subtype.val hi⟩,rfl⟩)
    exact Group.IsPerfect.not_isSolvable I hi
  let : Group.IsSolvable a.rangeRestrict.ker := by
    exact Group.isSolvable_of_isSolvable_injective
      (f := (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict a)).toMonoidHom)
      (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict a)).injective
  let er := solvableRadicalQuotientEquiv a.rangeRestrict a.rangeRestrict_surjective
  by_cases ht : a.range = ⊤
  · let eA : a.range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      (MulEquiv.subgroupCongr ht).trans topEquiv
    let : IsSimpleGroup a.range := by
      let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
      exact eA.isSimpleGroup
    have hr := radical_eq_bot_of_simple hns
    exact Or.inl ⟨F,inferInstance,inferInstance,hF,
      ⟨er.trans ((QuotientGroup.quotientMulEquivOfEq hr).trans
        (QuotientGroup.quotientBot.trans eA))⟩⟩
  · have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    obtain ⟨_,_,⟨eA⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five
      ho hF a.range ht hns
    let : IsSimpleGroup a.range := eA.isSimpleGroup
    have hr := radical_eq_bot_of_simple hns
    exact Or.inr ⟨er.trans ((QuotientGroup.quotientMulEquivOfEq hr).trans
      (QuotientGroup.quotientBot.trans eA))⟩

/-- In a surviving prime radical model, every original H-component is
normal in H. Uniqueness is calculated inside each full-Sylow overgroup;
it does not assert equality of components lying in different overgroups. -/
theorem component_normal_of_prime_radical_model
    (K H I : Subgroup G) (hK : (⊤ : Subgroup K).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hHK : H ≤ K ⊔ (T : Subgroup G))
    (hI : (I.subgroupOf H).IsCComponent)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ solvableRadical K) 2 p) :
    (I.subgroupOf H).Normal := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have htQ : (⊤ : Subgroup (K ⧸ solvableRadical K)).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      hK.map_quotient (solvableRadical K)
  have htF : (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using htQ.map_equiv e
  have huK : SylowOvergroupComponentUnique K :=
    SylowOvergroupComponentUnique.of_quotient (solvableRadical K)
      (SylowOvergroupComponentUnique.of_equiv e
        (Theory.PSL2.PrimeSylowComponents.sylow_unique Fact.out ho hF htF))
  let C := K ⊔ (T : Subgroup G)
  let : (K.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hTK)
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have huC : SylowOvergroupComponentUnique C :=
    SylowOvergroupComponentUnique.of_solvable_supplement K (T : Subgroup G) C
      le_sup_left le_sup_right rfl huK
  let eH : H ≃* H.subgroupOf C := (subgroupOfEquivOfLe hHK).symm
  apply hI.normal_of_unique
  intro J hJ
  apply map_injective (f := eH.toMonoidHom) eH.injective
  exact huC (T.subtype le_sup_right) (H.subgroupOf C) (fun _ ht => hTH ht)
    _ _ (hJ.map_equiv eH) (hI.map_equiv eH)

private theorem prime_simple_socle_generation
    {J : Type*} [Group J] [Finite J] [IsSimpleGroup (generalizedFitting J)]
    (U : Sylow 2 J) (hn : ¬ IsMulCommutative (generalizedFitting J))
    (hgen : generalizedFitting J ⊔ (U : Subgroup J) = ⊤)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hm : ClassicalGroup.IsPSL (generalizedFitting J) 2 p) :
    ChapterE.IsEGenerated 1 J := by
  have hs := SimpleSocle.structure_of_sylow_supplement hn U hgen
  apply ChapterE.ValuesOdd.PSLTwoGeneration.isEGenerated_of_component_and_large_escape
  · intro S A _ _ ha
    exact ChapterE.ValuesEvenClassical.RankOneUpper.eCaseComponent_top hn U hgen
      (S : Subgroup J) A ha
  · exact ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.largeFamilyEscape_of_prime_socle
      hp (hp.odd_of_ne_two (by omega)) hp5 hm hs.1 hs.2.2.1

/-- A normal C-component with actual prime-PSL₂ radical quotient above five
and a Sylow supplement gives generation at most one. The solvable kernel
is removed and then restored by the proved E-generation lifting theorem. -/
theorem generation_le_one_of_prime_radical_component
    {J : Type*} [Group J] [Finite J] (U : Sylow 2 J)
    (I : Subgroup J) [I.Normal] (hI : I.IsCComponent)
    (hgen : I ⊔ (U : Subgroup J) = ⊤)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hm : ClassicalGroup.IsPSL (I ⧸ solvableRadical I) 2 p) :
    ChapterE.generationParameter J ≤ 1 := by
  let q := QuotientGroup.mk' (solvableRadical J)
  let D := I.map q
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (solvableRadical J))
  have hr : solvableRadical (J ⧸ solvableRadical J) = ⊥ :=
    solvableRadical_quotient_solvableRadical
  have hD : D.IsCComponent := hI.map_quotient (solvableRadical J)
  let : D.Normal := (inferInstance : I.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup D := hD.isSimpleGroup_of_solvableRadical_eq_bot hr
  have hDn := hD.not_isMulCommutative_of_solvableRadical_eq_bot hr
  have hDgen : D ⊔ (Uq : Subgroup (J ⧸ solvableRadical J)) = ⊤ := by
    change I.map q ⊔ (U : Subgroup J).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have htwo := isPGroup_quotient_of_sup_eq_top D Uq Uq.isPGroup' hDgen
  have hcore := SimpleSocle.pCore_eq_bot hr 2
  have hF := (simple_two_quotient_structure D hDn htwo hcore).1
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.subgroupOf le_rfl
  have hk := kernel_eq_solvableRadical_of_top_isCComponent htop
    (q.subgroupMap I) (q.subgroupMap_surjective I)
  let eI : (I ⧸ solvableRadical I) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap I) (q.subgroupMap_surjective I))
  have hDm : ClassicalGroup.IsPSL D 2 p := hm.of_mulEquiv eI.symm
  let : IsSimpleGroup (generalizedFitting (J ⧸ solvableRadical J)) := hF.symm ▸ inferInstanceAs (IsSimpleGroup D)
  have hFn : ¬ IsMulCommutative (generalizedFitting (J ⧸ solvableRadical J)) := hF.symm ▸ hDn
  have hFm : ClassicalGroup.IsPSL (generalizedFitting (J ⧸ solvableRadical J)) 2 p := hF.symm ▸ hDm
  have hFgen : generalizedFitting (J ⧸ solvableRadical J) ⊔ (Uq : Subgroup _) = ⊤ :=
    hF.symm ▸ hDgen
  exact ChapterE.generationParameter_le (by decide)
    (ChapterE.IsEGenerated.of_solvableRadical_quotient (by decide)
      (prime_simple_socle_generation Uq hFn hFgen hp hp5 hFm))


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
