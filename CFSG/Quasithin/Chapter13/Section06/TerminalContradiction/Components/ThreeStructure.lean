module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure.Models
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure.LinearResidual
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.GroupTheory.CComponent.ExceptionalQuotients

/-!
# The three-local deductions in 13.6.27

The actual candidate equivalences establish centerlessness and three-rank
two. The component commutator argument then excludes the three-core of
H/O₂(H) and shows that every other C-component has order prime to three.
For J₂ and M₂₃ the proved outer two-group bounds identify K with O^{3′}(H).
The construction `threePrimeQuotientEquiv` compares K/O₂(K) with its image
in H/O₃′(H), the quotient used by A.3.18, without equating the ambient cores.

Quasisimplicity of the intrinsic two-core quotient is retained as an earlier
source premise, exactly as in A.3.18. After independently supplied uniqueness
and trivial Fitting, the actual PSL₃(4) automorphism calculation proves the
linear residual dichotomy and generation, hence the full `Alternative`.
This direct route replaces the universal A.3.18 specialization for this
fixed model. `conclusion_of_candidate` assembles the conditional local
conclusion; the parent still supplies the candidate, uniqueness, the earlier
quasisimplicity premise, and the large-prime exclusions from 13.6.26(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.6.27,
printed pp.934–935, and A.3.18, pp.51–52. The corrected core conclusion is
O₃(H/O₂(H)) = 1, as explained in the sibling `Structure` module.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure
universe u
variable {H : Type u} [Group H] [Finite H] {K : Subgroup H}

/-- The rank premise of A.3.18 holds for the selected actual component. -/
theorem candidate_rank_hypothesis (S : Sylow 2 H) (hmodel : Candidate (S : Subgroup H) K) :
    1 < primeRank 3 K := by
  have hr := (candidate_three_rank_ge_two hmodel).trans
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup)
  omega

/-- The source three-core and other-component exclusions, before component
uniqueness is established. SQTK supplies the ambient rank bound. -/
theorem local_three_exclusions {C : GroupClass.{u}} (hH : IsSQTK C H)
    (S : Sylow 2 H) (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hmodel : Candidate (S : Subgroup H) K) :
    pCore 3 (H ⧸ pCore 2 H) = ⊥ ∧
      ∀ D : Subgroup H, D.IsCComponent → D ≠ K → Nat.Coprime 3 (Nat.card D) := by
  have hz := candidate_center_eq_bot hK hmodel
  have hr := candidate_three_rank_ge_two hmodel
  have hH3 := hH.stronglyQuasithin 3 (by decide) (by decide)
  exact ⟨hK.threeCore_twoCore_quotient_eq_bot hz hr hH3,
    fun _ hD hne => hK.other_coprime_three_of_rank hz hr hH3 hD hne⟩

/-- Both sporadic branches give the first residual alternative directly,
using the actual outer groups and the normality of K in H. -/
theorem sporadic_eq_primeToResidual {C : GroupClass.{u}} (hH : IsSQTK C H)
    (hK : K.IsCComponent) [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23)) :
    K = primeToResidual 3 H := by
  have hm : Candidate (⊥ : Subgroup H) K := by
    rcases hmodel with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) := by
    rcases hmodel with h | h
    · exact Sporadic.LeechRelated.J2.outer_isTwoGroup.of_equiv
        (MulAut.outerCongr (Classical.choice h)).symm
    · exact Sporadic.Mathieu.m23_outer_isTwoGroup.of_equiv
        (MulAut.outerCongr (Classical.choice h)).symm
  exact hK.eq_primeToResidual_three_of_outer_twoGroup
    (candidate_center_eq_bot hK hm) (candidate_three_rank_ge_two hm)
    (hH.stronglyQuasithin 3 (by decide) (by decide)) ho

/-- The component's two-core quotient has no nontrivial normal three-prime subgroup. -/
theorem candidate_quotient_threePrimeCore_eq_bot (S : Sylow 2 H)
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hmodel : Candidate (S : Subgroup H) K) : pPrimeCore 3 (K ⧸ pCore 2 K) = ⊥ := by
  obtain ⟨E, _, hc⟩ := exists_elementary_nine_of_three_rank (candidate_three_rank_ge_two hmodel)
  apply CComponentExceptionalQuotient.primeCore_bot
  · rw [candidate_center_eq_bot hK hmodel]
    exact IsPGroup.of_card (n := 0) (by simp)
  · exact dvd_trans (show 3 ∣ Nat.card E by rw [hc]; decide) E.card_subgroup_dvd_card

/-- The exact component-image equivalence for H* = H/O₃′(H) in A.3.18.
This does not assert that O₃′(H) is O₂(H). -/
noncomputable def threePrimeQuotientEquiv (S : Sylow 2 H)
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hmodel : Candidate (S : Subgroup H) K) :
    (K ⧸ pCore 2 K) ≃* K.map (QuotientGroup.mk' (pPrimeCore 3 H)) :=
  CComponentExceptionalQuotient.quotientEquiv K hK.subnormal
    (candidate_quotient_threePrimeCore_eq_bot S hK hmodel)

/-- The image used by A.3.18 is centerless, excluding every model with a
nontrivial center after transporting its actual center calculation. -/
theorem threePrime_image_center_eq_bot (S : Sylow 2 H)
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hmodel : Candidate (S : Subgroup H) K) :
    center (K.map (QuotientGroup.mk' (pPrimeCore 3 H))) = ⊥ := by
  let e := threePrimeQuotientEquiv S hK hmodel
  apply eq_bot_iff.mpr
  intro x hx
  have hm : e.symm x ∈ center (K ⧸ pCore 2 K) := ((centerCongr e).symm ⟨x, hx⟩).property
  rw [candidate_center_eq_bot hK hmodel, mem_bot] at hm
  exact e.symm.map_eq_one_iff.mp hm

/-- Linear generation with an explicit outer-order bound. The source application
below supplies that bound from the proved actual-model calculation. -/
theorem linear_generation (S : Sylow 2 H) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* L3Four)
    (hd : NontrivialDynkinAction (S : Subgroup H) K e)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hf : fittingSubgroup (H ⧸ pCore 2 H) = ⊥)
    (ho : Nat.card (MulAut.Outer L3Four) ∣ 12) :
    primeToResidual 3 H ⊔ (S : Subgroup H) = ⊤ := by
  let _ := hK.perfect
  let _ : IsSimpleGroup L3Four := Atlas.psl_simple_high_rank 3 (by decide)
  let _ : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  have hm : Candidate (S : Subgroup H) K := Or.inr (Or.inr ⟨e, hd⟩)
  have hz := candidate_center_eq_bot hK hm
  let _ : IsQuasisimple (K ⧸ pCore 2 K) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  apply hK.primeToResidual_three_sup_sylow hz (candidate_three_rank_ge_two hm) hu hf _ S
  rwa [Nat.card_congr (MulAut.outerCongr e).toEquiv]

/-- The source linear generation, with the concrete outer-order premise discharged. -/
theorem linear_generation_of_unique_component (S : Sylow 2 H) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* L3Four)
    (hd : NontrivialDynkinAction (S : Subgroup H) K e)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hf : fittingSubgroup (H ⧸ pCore 2 H) = ⊥) :
    primeToResidual 3 H ⊔ (S : Subgroup H) = ⊤ :=
  linear_generation S hK e hd hu hf
    Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve

/-- The complete linear alternative, retaining the same quotient marking and
actual diagram action as the candidate supplied by the seed. -/
theorem linear_alternative_of_unique_component (S : Sylow 2 H) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* L3Four)
    (hd : NontrivialDynkinAction (S : Subgroup H) K e)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hf : fittingSubgroup (H ⧸ pCore 2 H) = ⊥) :
    Alternative (S : Subgroup H) K :=
  Or.inr ⟨e, hd, linear_generation_of_unique_component S hK e hd hu hf,
    linear_residual_dichotomy_of_unique_component hK e hu hf⟩

/-- The residual dichotomy for all candidates. Only the actual PSL₃(4)
branch can produce the PGL₃(4) extension, with its diagram action retained. -/
theorem residual_dichotomy_of_unique_component {C : GroupClass.{u}} (hH : IsSQTK C H)
    (S : Sylow 2 H) (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hmodel : Candidate (S : Subgroup H) K)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hf : fittingSubgroup (H ⧸ pCore 2 H) = ⊥) :
    K = primeToResidual 3 H ∨
      ∃ e : (K ⧸ pCore 2 K) ≃* L3Four,
        NontrivialDynkinAction (S : Subgroup H) K e ∧
          Nonempty (primeToResidual 3 (H ⧸ pCore 2 H) ≃* PGL3Four) := by
  let _ := hK.normal_of_unique hu
  rcases hmodel with hJ | hM | ⟨e, hd⟩
  · exact Or.inl (sporadic_eq_primeToResidual hH hK (Or.inl hJ))
  · exact Or.inl (sporadic_eq_primeToResidual hH hK (Or.inr hM))
  · exact (linear_residual_dichotomy_of_unique_component hK e hu hf).imp_right
      (fun hr => ⟨e, hd, hr⟩)

/-- All selected models give the exact source alternative after the independent
component-isolation and Fitting exclusions. -/
theorem alternative_of_unique_component (S : Sylow 2 H) (hK : K.IsCComponent)
    (hmodel : Candidate (S : Subgroup H) K)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hf : fittingSubgroup (H ⧸ pCore 2 H) = ⊥) :
    Alternative (S : Subgroup H) K := by
  rcases hmodel with hJ | hM | ⟨e, hd⟩
  · exact sporadic_alternative_of_unique_component S hK (Or.inl hJ) hu hf
  · exact sporadic_alternative_of_unique_component S hK (Or.inr hM) hu hf
  · exact linear_alternative_of_unique_component S hK e hd hu hf

/-- Conditional source assembly for the actual local group and its restricted
Sylow subgroup. The three-core exclusion discharges the missing prime in
13.6.26(2); the resulting trivial Fitting supplies both extension arguments.
The seed, Suzuki isolation, and earlier source premises remain with the parent. -/
theorem conclusion_of_candidate {C : GroupClass.{u}} (hH : IsSQTK C H)
    (S : Sylow 2 H) (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hmodel : Candidate (S : Subgroup H) K)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (H ⧸ pCore 2 H) = ⊥) :
    Conclusion (S : Subgroup H) := by
  have hthree := (local_three_exclusions hH S hK hmodel).1
  have hf := fitting_twoCore_quotient_eq_bot hthree hlarge
  obtain ⟨hF, hR⟩ := structure_of_unique_component hK hmodel hu hthree hlarge
  exact ⟨K, hK, alternative_of_unique_component S hK hmodel hu hf, hu, hF, hR⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure
