module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Overlap
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.KnownSimple
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# The original H-star component has field exponent two

The proved generation upper bounds exclude the odd E.2.2 rows. In each
remaining row, retain its marked component and construct its Cartan witness
at that row's exponent f. Hall faithfulness makes the cyclic group of order
2^f-1 a three-group; reduction modulo eight forces f=2. This argument does
not assume equality of generation parameters through a solvable kernel.

The original overlap is a {2,3}-group. The order-fifteen torus in the unitary
field-four Borel excludes that row. The exchanged row has an actual PSL₂(4)
Borel marking and hence an actual A₅ component isomorphism. Normality and the
original Sylow and maximal-overgroup markings are retained in the alternatives.
Source: Aschbacher--Smith E.2.2 and 10.2.3(3), printed pp.215--216,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem mersenne_three_power_bound {n k : ℕ} (h : 2 ^ n - 1 = 3 ^ k) : n ≤ 2 := by
  by_contra hn
  have hn3 : 3 ≤ n := by omega
  have hdiv : 8 ∣ 2 ^ n := by
    simpa using pow_dvd_pow (2 : ℕ) hn3
  have hpowers : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with ih | ih <;> simp [ih]
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
  have he : 2 ^ n = 3 ^ k + 1 := by omega
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  rw [he, Nat.add_mod] at hm
  rcases hpowers k with hpow | hpow <;> omega

theorem hstar_cartan_exponent_eq_two
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    {f : ℕ} (hf : 2 ≤ f)
    (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) (hstar_minimal D s hH) f) : f = 2 := by
  have he := source_hstar_parabolicMax_eq_overlap D hH (hstar_minimal D s hH)
  have hBM := he ▸ d.hall_le
  have hHall := he ▸ d.hall
  have hp := d.witness.permutes
  rw [d.sylow_eq] at hp
  have hm := congrArg (Set.image H.subtype) hp
  change H.subtype '' ((d.witness.abelianGroup : Set H) *
    ((T : Subgroup G).subgroupOf H : Set H)) =
      H.subtype '' (((T : Subgroup G).subgroupOf H : Set H) *
        (d.witness.abelianGroup : Set H)) at hm
  have hperm : (d.witness.abelianGroup.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (d.witness.abelianGroup.map H.subtype : Set G) := by
    simpa only [Set.image_mul, ← Subgroup.coe_map,
      map_subgroupOf_eq_of_le hH.1.1.2, Sylow.coe_coe] using hm
  have hthree := MovingHall.linear_three_hall_isThreeGroup D
    (Bender.survivor_nonnormal s) hH hBM hHall
    (Bender.survivor_hall_faithful hfaith hmany s hH _ hBM hHall d.witness.abelian hperm)
    s.quotient
  obtain ⟨k,hk⟩ := (hthree.to_le d.witness.cyclic_le).exists_card_eq
  have hle := mersenne_three_power_bound (d.witness.card.symm.trans hk)
  omega

private theorem normal_marked_bounds
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    (hn : 1 < generationParameter X) (K : Subgroup X) (hK : K.IsCComponent)
    [K.Normal] (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (S : Subgroup X) = ⊤) :
    ∃ f : ℕ, 2 ≤ f ∧ generationParameter X ≤ f ∧
      ReducedCases (minimalParabolicMax S hP) K S f := by
  have hA := ChapterA.Section02.theoremA_knownSimple (G := X)
  have hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  have hc := source_single_clauses S hP hs K hK hqs hgen
  rcases source_normal_geometric_cases hA hC hX S hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact (single_odd_linear_false_of_parameter_gt_one hA hX S hP hs K hK hgen h2 hn).elim
  · obtain ⟨p,hp,ho,_,huni|hlin⟩ := h3
    · exact (normal_odd_three_false_of_parameter_gt_one hA hX S hP hs K hK hgen hp ho
        (Or.inr huni.2) hn).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
      exact (normal_odd_three_false_of_parameter_gt_one hA hX S hP hs K hK hgen hp ho
        (Or.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) hn).elim
  · cases hb with
    | linear f hf hm =>
      exact ⟨f,hf,normal_classical_parameter_le hA hX S hP hs K hK hgen (.inl ⟨hf,hm⟩),
        .bender hc (.inl (source_linear_borel_model S hP hs K hK hgen hf hm))⟩
    | unitary f hf hm =>
      exact ⟨f,hf,normal_classical_parameter_le hA hX S hP hs K hK hgen (.inr (.inl ⟨hf,hm⟩)),
        .bender hc (.inr (source_unitary_borel_model S hP hs K hK hgen hf hm))⟩
    | suzuki m hm he =>
      obtain ⟨_,hu⟩ := normal_suzuki_generation S hP hs K hK hgen hm he
      exact ⟨2*m+1,by omega,hu,
        .bender hc (.inl (source_suzuki_borel_model S hP hs K hK hgen hm he))⟩
  · obtain ⟨f,hf,hm⟩ := hl
    have hu := normal_classical_parameter_le hA hX S hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))
    exact ⟨f,by omega,hu,.diagram hc (source_binary_linear_three_model S hP hs K hK hgen hf hm)⟩
  · obtain ⟨f,hf,hm⟩ := hsp
    exact ⟨f,hf,normal_symplectic_parameter_le hA hX S hP hs K hK hgen hf hm,
      .diagram hc (source_binary_symplectic_model S hP hs K hK hgen hf hm)⟩
  · exact ((Nat.not_le_of_gt hn) (normal_binary_six_parameter_le S hP hs K hK hgen hbi)).elim

theorem hstar_component_cases_two
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤ ∧
      let M := minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)
      (K.Normal ∧ SingleClauses M K (T.subtype hH.1.1.2) ∧
        (BenderModel M K 2 ∨ DiagramModel M K (T.subtype hH.1.1.2) 2)) ∨
      (¬ K.Normal ∧ ExchangedClauses M K (T.subtype hH.1.1.2) ∧
        ExchangedModel M K 2) := by
  have hX := Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1
  let S := T.subtype hH.1.1.2
  have hP := hstar_minimal D s hH
  have hn : 1 < generationParameter H := by rw [s.generation H hH]; decide
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hX S hP hs
  have he (f : ℕ) (hf : 2 ≤ f) (hr : ReducedCases (minimalParabolicMax S hP) K S f) : f = 2 := by
    obtain ⟨d⟩ := hr.intrinsic_at S hP (by omega) hK hqs
    exact hstar_cartan_exponent_eq_two D hfaith hmany s hH hf d
  refine ⟨K,hK,hqs,hgen,?_⟩
  by_cases hnorm : K.Normal
  · let := hnorm
    obtain ⟨f,hf,_,hr⟩ := normal_marked_bounds hX S hP hs hn K hK hqs hgen
    have hr2 : ReducedCases (minimalParabolicMax S hP) K S 2 := he f hf hr ▸ hr
    cases hr2 with
    | exchanged hc _ =>
      obtain ⟨t,_,ht,_⟩ := hc.exchanged_product
      exact (ht (normal_iff_map_conj_eq.mp hnorm t⁻¹).symm).elim
    | bender hc hm => exact Or.inl ⟨hnorm,hc,Or.inl hm⟩
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
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hnorm (p := p) (by omega) hm)).elim

/-- The exchanged exponent-two row is the actual binary field-four Borel,
with its original marking; the Suzuki row is excluded arithmetically. -/
theorem exchanged_two_linear_marking {X : Type*} [Group X]
    {M K : Subgroup X} (hm : ExchangedModel M K 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 4 ∧ ModelBorelPair M K (BenderSuzuki.Converse.PBorel F) := by
  rcases hm with ⟨F,hF,hfin,hchar,_,hc,he⟩ | ⟨m,hm,hf,_⟩
  · exact ⟨F,hF,hfin,hchar,hc,he⟩
  · omega

/-- In the exchanged row the same source component is genuinely A₅. -/
theorem exchanged_two_component_equiv_alternatingFive {X : Type*} [Group X]
    {M K : Subgroup X} (hm : ExchangedModel M K 2) :
    Nonempty (sourceImage M K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,hF,hfin,hchar,hcard,e,_⟩ := exchanged_two_linear_marking hm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  let eF : F ≃+* GaloisField 2 2 := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard,
      GaloisField.card 2 2 (by decide)]
    rfl)
  exact ⟨(e.trans (Atlas.fieldEquivPSL 2 eF)).trans
    Atlas.Comparisons.Exceptional.psl2FourEquivAlt5⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem not_unitary_two_of_six_maximal {X : Type*} [Group X] [Finite X]
    {M K : Subgroup X} (hM : IsPGroup 6 M) (hm : UnitaryModel M K 2) : False := by
  obtain ⟨F,hF,hfin,hchar,J,hJ,_,hcard,hconj,_,e,he⟩ := hm
  have hc : IsPGroup 6 (componentOverlap M K) :=
    ((hM.to_le inf_le_left).map (QuotientGroup.mk' (sourceKernel M))).comap_subtype
  have hB : IsPGroup 6 (unitaryBorel J hJ) := he ▸ hc.map e.toMonoidHom
  have htorus : IsPGroup 6 (BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projectiveTorus J hJ) :=
    hB.to_le le_sup_right
  have htcard : Nat.card (BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projectiveTorus J hJ) = 15 := by
    simpa using BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projective_card J hJ hcard hconj
  have hf := (isPGroup_iff_primeFactors_card_subset (by decide : 6 ≠ 0)).mp htorus
  rw [htcard] at hf
  have hfive := hf (show 5 ∈ (15 : ℕ).primeFactors from Nat.mem_primeFactors.mpr ⟨by decide,by decide,by decide⟩)
  norm_num at hfive

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem hstar_not_unitary_two
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (K : Subgroup H) :
    ¬ UnitaryModel (minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)) K 2 := by
  have hM : IsPGroup 6 (D.maximalLocal.subgroupOf H) := by
    have hh := (overlap_isSixGroup D hfaith hmany s hH).comap_subtype (K := H)
    have he : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
    exact he ▸ hh
  rw [← source_hstar_parabolicMax_eq_overlap D hH (hstar_minimal D s hH)] at hM
  exact not_unitary_two_of_six_maximal hM

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
