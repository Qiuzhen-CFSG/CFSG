module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.RankTwoResidualExclusions
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeLocal
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLocal
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLine
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ParabolicPlacement

/-!
# Matching the surviving component to the original rank-one residual

Restrict the actual component central quotient to the fixed residual. Its
solvable kernel and nontrivial two-core image permit the full-parabolic
exclusions. The unitary residual forces a PSU₅(4) component; the Suzuki
residual forces a Ree component and is placed in its actual Suzuki
parabolic by the same quotient map followed by inner conjugation.
All normality, centralizer, rank and original-module clauses are retained.
The matching rows still require the centered-module exclusion; these
results do not assert odd-normalizer control or residual uniqueness.
Source: Aschbacher--Smith 4.4.11--12, printed pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

variable {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]

/-- A unitary residual excludes every Ree model of its actual containing cover. -/
theorem unitary_five_of_unitary_residual
    (F K W : Subgroup G) (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2)
    (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hsu : ClassicalGroup.IsPSU S 3 (2 ^ s))
    (hmodel : UnitaryFiveOrReeModel (K ⧸ center K)) :
    ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
  rcases hmodel with h | ⟨m,hm,⟨e⟩⟩
  · exact h
  · let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact (no_ree_local_of_three_dvd hS (unitary_not_two_exponent hs hsu)
      (unitary_three_dvd_card hs hsu) π hπ hm _ hp hpne r hnorm).elim

/-- The surviving unitary residual has parameter four. The line-parabolic
order is imposed on the actual residual representation, not an unrelated section. -/
theorem unitary_parameter_of_unitary_five_residual
    (F K W : Subgroup G) (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2)
    (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hsu : ClassicalGroup.IsPSU S 3 (2 ^ s))
    (hmodel : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) : s = 2 := by
  obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hmodel
  have hc : Nat.card E = 16 := hcard
  let := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hc
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hc hconj
  let t := e.trans a
  let r := residualQuotientMap hFK t
  let := residualQuotientMap_kernel_solvable hFK t
  obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
  exact (unitary_five_line_representation hS π hπ hs hsu
    (HermitianForm.IdentityGram.identityGram J) hc hconj rfl _ hp hpne r hnorm).1

/-- The Suzuki residual is conjugated into the full Suzuki-side Ree parabolic,
using its original inclusion followed by the containing component's central quotient. -/
theorem ree_suzuki_parabolic_of_suzuki_residual
    (F K W : Subgroup G) (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2)
    (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    {a : ℕ} (ha : 1 ≤ a) (es : S ≃* SuzukiMatrixGroup a)
    (hmodel : UnitaryFiveOrReeModel (K ⧸ center K)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ e : (K ⧸ center K) ≃* ReeF4.Model m,
      ∃ g : ReeF4.Model m,
        (residualQuotientMap hFK e).range.map (MulAut.conj g).toMonoidHom ≤
          ReeF4.ConverseParabolics.parabolic m .suzuki := by
  rcases hmodel with h | ⟨m,hm,⟨e⟩⟩
  · obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := h
    have hc : Nat.card E = 16 := hcard
    let := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hc
    obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hc hconj
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
    exact (no_suzuki_unitary_five_local hS π hπ ha es
      (HermitianForm.IdentityGram.identityGram J) hc hconj rfl _ hp hpne r hnorm).elim
  · let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    obtain ⟨g,hg⟩ := ree_suzuki_parabolic_representation hS (suzuki_not_two_exponent ha es)
      π hπ hm _ hp hpne r hnorm
    exact ⟨m,hm,e,g,hg⟩

/-- The unitary component configuration, retaining the original module and residual. -/
@[expose] def UnitaryFiveComponentCase (L W A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ ClassicalGroup.IsPSU (K ⧸ center K) 5 4 ∧
    W ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    12 ≤ primeRank 2 (K ⧸ center K) ∧
    ∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f

/-- The Suzuki configuration retains the ambient component and the literal
quotient representation into its full Ree Suzuki parabolic. -/
@[expose] def ReeSuzukiComponentCase (L W A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ W ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype,
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      12 ≤ primeRank 2 (K ⧸ center K) ∧
      (∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f) ∧
      let J := K.map (normalizer (A : Set G)).subtype
      ∃ m : ℕ, 1 ≤ m ∧ ∃ e : (J ⧸ center J) ≃* ReeF4.Model m,
        ∃ g : ReeF4.Model m,
          (residualQuotientMap hFK e).range.map (MulAut.conj g).toMonoidHom ≤
            ReeF4.ConverseParabolics.parabolic m .suzuki ∧
          let q := (MulAut.conj g).toMonoidHom.comp
            (e.toMonoidHom.comp (QuotientGroup.mk' (center J)))
          let P := ReeF4.ConverseParabolics.parabolic m .suzuki
          (P.comap q).map J.subtype ≤ normalizer (L : Set G) ∧
            ((q.comp (inclusion hFK)).range.subgroupOf P).Normal

private def mappedComponentCentralQuotientEquiv {N : Subgroup G} (K : Subgroup N) :
    (K.map N.subtype ⧸ center (K.map N.subtype)) ≃* (K ⧸ center K) :=
  let e := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

/-- Applying the actual unitary residual exclusion removes the Ree component row. -/
theorem unitary_five_component_of_remaining_case
    {L W A : Subgroup G}
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hS : ¬ Group.IsSolvable S)
    (π : oddActorResidual L A →* S) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hsu : ClassicalGroup.IsPSU S 3 (2 ^ s))
    (hc : UnitaryFiveOrReeComponentCase L W A S) : UnitaryFiveComponentCase L W A S := by
  obtain ⟨K,hK,hn,hout,hcore,hm,hw,hf,hcent,hr,hsection⟩ := hc
  let z := mappedComponentCentralQuotientEquiv K
  have hu := unitary_five_of_unitary_residual (oddActorResidual L A)
    (K.map (normalizer (A : Set G)).subtype) W hf hWF hne hcomm hS π hπ hs hsu
    (hm.of_mulEquiv z)
  exact ⟨K,hK,hn,hout,hcore,hu.of_mulEquiv z.symm,hw,hf,hcent,hr,hsection⟩

/-- The exact residual also forces the parameter in the surviving component case. -/
theorem unitary_parameter_of_five_component_case
    {L W A : Subgroup G}
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hS : ¬ Group.IsSolvable S)
    (π : oddActorResidual L A →* S) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hsu : ClassicalGroup.IsPSU S 3 (2 ^ s))
    (hc : UnitaryFiveComponentCase L W A S) : s = 2 := by
  obtain ⟨K,_,_,_,_,hm,_,hf,_⟩ := hc
  let z := mappedComponentCentralQuotientEquiv K
  exact unitary_parameter_of_unitary_five_residual (oddActorResidual L A)
    (K.map (normalizer (A : Set G)).subtype) W hf hWF hne hcomm hS π hπ hs hsu
    (hm.of_mulEquiv z)

/-- The Suzuki application retains the actual quotient and conjugation maps,
as well as every original component clause. -/
theorem ree_suzuki_component_of_remaining_case [Finite G]
    {L W A : Subgroup G}
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hS : ¬ Group.IsSolvable S)
    (π : oddActorResidual L A →* S) (hπ : Function.Surjective π)
    {a : ℕ} (ha : 1 ≤ a) (es : S ≃* SuzukiMatrixGroup a)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hc : UnitaryFiveOrReeComponentCase L W A S) : ReeSuzukiComponentCase L W A S := by
  obtain ⟨K,hK,hn,hout,hcore,hm,hw,hf,hcent,hr,hsection⟩ := hc
  let z := mappedComponentCentralQuotientEquiv K
  obtain ⟨m,hm,e,g,hg⟩ := ree_suzuki_parabolic_of_suzuki_residual (oddActorResidual L A)
    (K.map (normalizer (A : Set G)).subtype) W hf hWF hne hcomm hS π hπ ha es
    (hm.of_mulEquiv z)
  exact ⟨K,hK,hn,hout,hcore,hw,hf,hcent,hr,hsection,m,hm,e,g,hg,
    ree_suzuki_parabolic_preimage_and_normality (map_subtype_le K) hf hu e g hg⟩

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
