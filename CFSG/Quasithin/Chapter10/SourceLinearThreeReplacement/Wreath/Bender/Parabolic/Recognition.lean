module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Parabolic.Placement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Normal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Recognition
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Dihedral
import all CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Cases
import all CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Pair
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Recognition of the original H-star two-core quotient

The actual maximal overlap is a {2,3}-group with S₃-wreath quotient.
The marked E.2.2 Cartan calculations force field exponent two, using only
the adequate generation bound. The unitary torus and dihedral quotient
above O₂,₃ exclude the normal rows. The exchanged A₅ pair embeds the
original H/O₂(H) in S₅ wr C₂, and the overlap order forces surjectivity.

The internal Cases and Pair imports intentionally reuse this chapter's
already proved component calculations, separately from their omega-module
application. Structure supplies the defining parabolic-core equation.
No private declaration occurs in the public theorem's statement, and no
positive-fixed-space or omega-kernel premise enters this application.

Source: Aschbacher--Smith E.2.2 and 10.2.3(3), pp.215--216,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender.Parabolic
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry

/-- A genuine marked Cartan exponent is two when the maximal subgroup has
only primes two and three. The generation parameter is used only as a bound. -/
private theorem cartan_exponent_two {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hM : IsPGroup 6 (minimalParabolicMax S hP)) {f : ℕ} (hf : 2 ≤ f)
    (d : IntrinsicHallCartanData S hP f) : f = 2 := by
  have h6 := hM.to_le d.hall_le
  obtain ⟨n,hn⟩ := h6.exists_card_dvd_pow
  have hn' : Nat.card d.witness.abelianGroup ∣ 2 ^ n * 3 ^ n := by
    simpa only [← mul_pow, show 2 * 3 = 6 by decide] using hn
  have h3 : IsPGroup 3 d.witness.abelianGroup := IsPGroup.of_card_dvd_pow
    ((d.witness.odd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hn')
  obtain ⟨k,hk⟩ := (h3.to_le d.witness.cyclic_le).exists_card_eq
  have hb := mersenne_three_power_bound (d.witness.card.symm.trans hk)
  omega

/-- The six-prime maximal subgroup fixes the source exponent at two,
while preserving normality and the literal original component and Borel. -/
private theorem component_cases_two {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hn : 1 < generationParameter X)
    (hM : IsPGroup 6 (minimalParabolicMax S hP)) :
    ∃ K : Subgroup X, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (S : Subgroup X) = ⊤ ∧
      let M := minimalParabolicMax S hP
      (K.Normal ∧ SingleClauses M K S ∧
        (ExchangedModel M K 2 ∨ DiagramModel M K S 2)) ∨
      (¬ K.Normal ∧ ExchangedClauses M K S ∧ ExchangedModel M K 2) := by
  have hs : ¬ Group.IsSolvable X := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hX S hP hs
  have he (f : ℕ) (hf : 2 ≤ f) (hr : ReducedCases (minimalParabolicMax S hP) K S f) : f = 2 := by
    obtain ⟨d⟩ := hr.intrinsic_at S hP (by omega) hK hqs
    exact cartan_exponent_two S hP hM hf d
  refine ⟨K,hK,hqs,hgen,?_⟩
  by_cases hnorm : K.Normal
  · let := hnorm
    obtain ⟨f,hf,_,hr⟩ := normal_marked_bounds hX S hP hs hn K hK hqs hgen
    have hr2 : ReducedCases (minimalParabolicMax S hP) K S 2 := he f hf hr ▸ hr
    cases hr2 with
    | exchanged hc _ =>
      obtain ⟨t,_,ht,_⟩ := hc.exchanged_product
      exact (ht (normal_iff_map_conj_eq.mp hnorm t⁻¹).symm).elim
    | bender hc hm =>
      rcases hm with hm | hm
      · exact Or.inl ⟨hnorm,hc,Or.inl hm⟩
      · exact (not_unitary_two_of_six_maximal hM hm).elim
    | diagram hc hm => exact Or.inl ⟨hnorm,hc,Or.inr hm⟩
  · rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen hnorm with
      ⟨f,hf,hm⟩ | ⟨p,hp,_,h7,hm⟩
    · have hc := source_exchanged_clauses (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        hX S hP hs hK hqs hgen hnorm
      have hr : ReducedCases (minimalParabolicMax S hP) K S f := .exchanged hc hm
      have hf2 := he f (by omega) hr
      subst f
      exact Or.inr ⟨hnorm,hc,hm⟩
    · let : Fact p.Prime := ⟨hp⟩
      exact (Nat.not_le_of_gt hn (paired_prime_parameter_le_one
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hnorm (p := p)
          (by omega) hm)).elim
/-- The exchanged field-four source model, with a literal overlap quotient,
recognizes H/O₂(H). All quotient maps are from the original H. -/
private theorem exchanged_wreath
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S)
    (hm : ExchangedModel (minimalParabolicMax S hP) K 2)
    (hM : IsPGroup 6 (minimalParabolicMax S hP))
    (heM : Nonempty ((minimalParabolicMax S hP ⧸ pCore 2 (minimalParabolicMax S hP)) ≃*
      WreathTwoResidual.Actor)) :
    Nonempty ((X ⧸ pCore 2 X) ≃* Theory.SpecificGroups.SymmetricFive.WreathComponents.W) := by
  have hk : minimalParabolicCore S hP = pCore 2 X := hc.kernel_eq
  obtain ⟨er⟩ := star_residual_of_exchanged_two hX S hP hs K hK hgen hc hm
  let eq := QuotientGroup.quotientMulEquivOfEq hk
  let er' : pResidual 2 (X ⧸ pCore 2 X) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (((eq.symm.subgroupMap (pResidual 2 (X ⧸ pCore 2 X))).trans
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 eq.symm.toMonoidHom
        eq.symm.surjective))).trans er)
  obtain ⟨a,ha⟩ := wreath_embedding_of_pair_residual
    (pCore_quotient_pCore_eq_bot (G := X) 2) er'
  let q := QuotientGroup.mk' (pCore 2 X)
  let M := minimalParabolicMax S hP
  let Q := M.map q
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hqM : IsPGroup 2 (q.subgroupMap M).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hq.comap_subtype
  obtain ⟨b⟩ := heM
  have hQ : Nonempty ((Q ⧸ pCore 2 Q) ≃* WreathTwoResidual.Actor) :=
    ⟨((q.subgroupMap M).pCoreQuotientEquiv (q.subgroupMap_surjective M) hqM).symm.trans b⟩
  exact wreath_of_pair_and_overlap er' (S.mapSurjective (QuotientGroup.mk'_surjective _)) Q
    (hM.map q) (map_mono (minimalParabolicMax_spec S hP).2) hQ a ha

/-- Source 10.2.3's E.2.2 recognition on the literal two-core quotient.
The maximal overlap quotient excludes every normal field-four row; the
exchanged row gives the full symmetric-five wreath group. -/
private theorem wreath_quotient_of_overlap {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hn : 1 < generationParameter X)
    (hM : IsPGroup 6 (minimalParabolicMax S hP))
    (heM : Nonempty ((minimalParabolicMax S hP ⧸ pCore 2 (minimalParabolicMax S hP)) ≃*
      WreathTwoResidual.Actor)) :
    Nonempty ((X ⧸ pCore 2 X) ≃* Theory.SpecificGroups.SymmetricFive.WreathComponents.W) := by
  have hs : ¬ Group.IsSolvable X := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,_,hgen,hnorm|hex⟩ := component_cases_two hX S hP hn hM
  · obtain ⟨hKn,hc,hm⟩ := hnorm
    let := hKn
    exact (normal_fieldFour_false S hP hs K hK hgen hc hM
      (twoThreeCoreQuotient_of_wreath heM.some) hm).elim
  · exact exchanged_wreath hX S hP hs K hK hgen hex.2.1 hex.2.2 hM heM


/-- The whole quotient is recognized on its original carrier, with only
Hall faithfulness retained from the exact source contract. -/
theorem hstar_quotient {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHC : H ≤ centralizer ({d.first*d.second} : Set G)) (hf : HallFaithful D H) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Theory.SpecificGroups.SymmetricFive.WreathComponents.W) := by
  have hn : 1 < generationParameter H := by rw [s.generation H hH]; decide
  have hP := source_hstar_minimal_parabolic_of_generation_gt_one D hH hn
  exact wreath_quotient_of_overlap
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2) hP hn
    (maximal_isSixGroup hmany D s d hH hHC hf hP)
    (maximal_twoCore_quotient hmany D s d hH hHC hf hP)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender.Parabolic
