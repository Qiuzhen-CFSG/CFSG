module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Consumer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The controlled Thompson index in the nonquasisimple supplement argument

For the literal canonical radical X and radical Sylow subgroup R, the original
faithful module gives two-rank at least three. The actual XR is solvable,
3-prime, has R as Sylow two-subgroup, and has F*(XR) = O2(XR). These establish
the source setup for GLS G.26.18 without substituting a different radical.

The remaining GLS factorization is a named explicit input. The existing
Frattini-image argument and source irreducibility turn it into normalization
of J0(R) or Omega1 Z(J1(R)). Uniqueness over XT then controls the full
normalizer of Jj(R), with j at most one and strictly below the two-rank.
The last theorem applies that index to the literal common-action consumer.

Source: Aschbacher--Smith, proof of 13.1.9, printed pp.870--871; GLS,
*The Classification of the Finite Simple Groups*, Number 2, G.26.18(a),
printed pp.152--153. The GLS factorization and the earlier canonical-star
and quotient-classification inputs remain with their existing source owners.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
open Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual normalizer-moved module lies in the literal radical Sylow subgroup. -/
theorem controlledIndex_moved_le_radical (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    normalizerMoved L ≤ radicalSylowCentralizer T L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨hUe,_,hUQ,hMU⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  have hMQT : (normalizer (L : Set G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype hTL)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTL] using hh
  apply le_trans _ (join_core_le_radicalSylowCentralizer T hTL)
  exact le_pCoreIn_of_normalizes hUe.isPGroup
    ((hUQ.trans hMQT).trans le_sup_right)
    ((sup_le L.le_normalizer hTL).trans hMU.ge)

/-- The original faithful module gives rank at least three, so both source
Thompson indices are strictly below the rank. -/
theorem controlledIndex_radical_rank (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    3 ≤ twoRank (radicalSylowCentralizer T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨he,hne,_,_⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  have hc := (normalizerMoved_commutator_and_card hL.1.1 hne).2
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (radicalSylowCentralizer T L)
  have hm := hA.2.2 (normalizerMoved L) (controlledIndex_moved_le_radical h hL hn) he
  rw [elementaryAbelianMaxSubgroups_card_eq _ _ hA,maxOrder_eq_two_pow_rank] at hm
  have hp : 2 ^ 3 ≤ 2 ^ twoRank (radicalSylowCentralizer T L) := hc.trans hm
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp

/-- The two-core of the literal canonical radical is inside the source R. -/
theorem controlledIndex_XiP_core_le (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) :
    (XiP p L).pCoreIn 2 ≤ radicalSylowCentralizer T L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  exact ((pCoreIn_mono_of_normalizes (XiP_le p L)
    (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L))).trans
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer hTL))).trans
    (join_core_le_radicalSylowCentralizer T hTL)

/-- R is Sylow in the literal XR, rather than in a join with O₂(XT). -/
theorem controlledIndex_XR_sylow (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime] (ho : Odd p) :
    IsSylowIn 2 (radicalSylowCentralizer T L)
      (XiP p L ⊔ radicalSylowCentralizer T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  apply IsPGroup.exists_sylow_sup_of_coprime_index _ _
    (T.isPGroup'.to_le (radicalSylowCentralizer_le _ _))
    ((radicalSylowCentralizer_le _ _).trans (XiP_invariant p hTL)) (pCore 2 (XiP p L))
  · rw [index_eq_card]
    obtain ⟨n, hn⟩ := (XiP_quotient_isPGroup p ho L).exists_card_eq
    rw [hn]
    exact Nat.prime_two.coprime_iff_not_dvd.mp ((Nat.coprime_two_left.mpr ho).pow_right n)
  · exact controlledIndex_XiP_core_le h hL hn p

/-- Solvability of the exact XR used in G.26.18. -/
theorem controlledIndex_XR_solvable (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime] (ho : Odd p) :
    Group.IsSolvable (XiP p L ⊔ radicalSylowCentralizer T L : Subgroup G) := by
  let X := XiP p L
  let R := radicalSylowCentralizer T L
  let W := X ⊔ R
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : Group.IsSolvable X := XiP_solvable p ho L
  let : Group.IsNilpotent R := (T.isPGroup'.to_le (radicalSylowCentralizer_le _ _)).isNilpotent
  let : (X.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer ((radicalSylowCentralizer_le _ _).trans (XiP_invariant p hTL)))
  let : Group.IsSolvable (X.subgroupOf W) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show X ≤ W from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show X ≤ W from le_sup_left)).injective
  let : Group.IsSolvable (R.subgroupOf W) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show R ≤ W from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show R ≤ W from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (X.subgroupOf W) (R.subgroupOf W)
    (by rw [← subgroupOf_sup le_sup_left le_sup_right]; exact subgroupOf_self W)

/-- Normality in XT transfers characteristic two to the literal XR. -/
theorem controlledIndex_XR_generalizedFitting (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    generalizedFitting (XiP p L ⊔ radicalSylowCentralizer T L : Subgroup G) =
      pCore 2 (XiP p L ⊔ radicalSylowCentralizer T L : Subgroup G) := by
  let X := XiP p L
  let R := radicalSylowCentralizer T L
  let W := X ⊔ R
  let K := X ⊔ (T : Subgroup G)
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hx := (XiP_mem_XiPlus_source h.simpleQTKE T hL.1.1 hn ho hd).1
  have hHe : K ∈ He G := lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
    ⟨hx.join_mem_H,fun _ ht => Subgroup.mem_sup_right ht⟩
  have hWK : W ≤ K := sup_le_sup_left (radicalSylowCentralizer_le _ _) X
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (le_inf hx.invariant (sylow_normalizes_radicalSylowCentralizer hTL)).trans
      (normalizer_inf_normalizer_le_normalizer_sup X R)
  let : (W.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (le_sup_left.trans W.le_normalizer) hTW)
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hWK)).mp
    (normal_core_selfCentralizing (mem_He_iff.mp hHe) (W.subgroupOf K))

/-- The literal XR is a 3′-group at every supported canonical prime. -/
theorem controlledIndex_XR_three_coprime (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    Nat.Coprime 3 (Nat.card (XiP p L ⊔ radicalSylowCentralizer T L : Subgroup G)) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hp3 := (XiP_oddQuotient_of_A36 h36 hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn ho hd).1
  let X := XiP p L
  let R := radicalSylowCentralizer T L
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  obtain ⟨b, hb⟩ := (XiP_quotient_isPGroup p ho L).exists_card_eq
  obtain ⟨c, hc⟩ := (T.isPGroup'.to_le (radicalSylowCentralizer_le T L)).exists_card_eq
  have hXcard : Nat.card X = 2 ^ a * p ^ b := by
    rw [← (pCore 2 X).card_mul_index,index_eq_card,ha,hb]
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes X R
    ((radicalSylowCentralizer_le _ _).trans (XiP_invariant p hTL))
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hdiv
  have hdprod : 3 ∣ Nat.card X * Nat.card R := by
    rw [hm]
    exact dvd_mul_of_dvd_right hdiv _
  rw [hXcard,hc] at hdprod
  have hthreep : Nat.Coprime 3 p := Nat.prime_three.coprime_iff_not_dvd.mpr (by
    intro hd3
    have he := (Nat.dvd_prime (Fact.out : p.Prime)).mp hd3
    omega)
  have hcop : Nat.Coprime 3 (2 ^ a * p ^ b * 2 ^ c) :=
    ((by decide : Nat.Coprime 3 2).pow_right a |>.mul_right (hthreep.pow_right b)).mul_right
      ((by decide : Nat.Coprime 3 2).pow_right c)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop) hdprod


open scoped Pointwise

/-- The precise remaining G.26.18 factorization, on the literal XR. This is
an input to the selection theorem, not an asserted source theorem. -/
def ControlledIndexFactorization (X R : Subgroup G) : Prop :=
  ((X ⊔ R : Subgroup G) : Set G) =
    (((X ⊔ R) ⊓ normalizer (thompsonJ R 0 : Set G) : Subgroup G) : Set G) *
    (((X ⊔ R) ⊓ normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set G) :
      Subgroup G) : Set G)

/-- The weaker sufficient normality choice resulting from the factorization. -/
def ControlledIndexNormalityChoice (X R : Subgroup G) : Prop :=
  X ≤ normalizer (thompsonJ R 0 : Set G) ∨
    X ≤ normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set G)

omit [Finite G] in
private theorem controlledIndex_normalizer_omega (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (omegaOneCenterAmbient R : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change R.map (MulAut.conj g).toMonoidHom = R at hg
  change (omegaOneCenterAmbient R).map (MulAut.conj g).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,hg]

private theorem controlledIndex_thompson_ne_bot (R : Subgroup G)
    {j : ℕ} (hj : j < twoRank R) : thompsonJ R j ≠ ⊥ := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  have hAJ : A ≤ thompsonJ R 0 := by
    rw [thompsonJ_zero]
    exact le_sSup hA
  have hc : 1 < Nat.card A := by
    rw [elementaryAbelianMaxSubgroups_card_eq R A hA,maxOrder_eq_two_pow_rank]
    exact one_lt_pow₀ (by decide : 1 < 2) (by omega)
  intro he
  have hAbot : A = ⊥ := bot_unique
    ((hAJ.trans (lemma_B_2_3_1 R (Nat.zero_le j) hj)).trans he.le)
  rw [hAbot,Subgroup.card_bot] at hc
  omega

private theorem controlledIndex_omega_ne_bot (R : Subgroup G)
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥) : omegaOneCenterAmbient R ≠ ⊥ := by
  have hi := omegaCenterIn_ne_bot R hR hne
  intro he
  apply hi
  apply Subgroup.map_injective (f := R.subtype) R.subtype_injective
  simpa [omegaOneCenterAmbient,RadicalNormalizers.omegaCenterIn] using he

/-- The actual source irreducibility turns the exact GLS factorization into
one of its two normality alternatives. -/
theorem controlledIndex_normality_of_factorization (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hf : ControlledIndexFactorization (XiP p L) (radicalSylowCentralizer T L)) :
    ControlledIndexNormalityChoice (XiP p L) (radicalSylowCentralizer T L) := by
  let X := XiP p L
  let R := radicalSylowCentralizer T L
  let E := omegaOneCenterAmbient (thompsonJ R 1)
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hx := (XiP_mem_XiPlus_source h.simpleQTKE T hL.1.1 hn ho hd).1
  let := XiP_quotient_nontrivial_of_fittingPrime p ho hd
  have hRX : R ≤ normalizer (X : Set G) :=
    (radicalSylowCentralizer_le _ _).trans hx.invariant
  have hTR := sylow_normalizes_radicalSylowCentralizer hTL
  have hTJ := hTR.trans (normalizer_le_thompson R 0)
  have hTE := hTR.trans ((normalizer_le_thompson R 1).trans
    (controlledIndex_normalizer_omega _))
  have hRJ := R.le_normalizer.trans (normalizer_le_thompson R 0)
  have hRE := R.le_normalizer.trans ((normalizer_le_thompson R 1).trans
    (controlledIndex_normalizer_omega _))
  have hcore := controlledIndex_XiP_core_le h hL hn p
  have hnonzero := factorization_intersection_not_le X R (twoFrattini X)
    (normalizer (thompsonJ R 0 : Set G)) (normalizer (E : Set G)) hRX
    (hRX.trans (normalizer_le_normalizer_twoFrattini X)) (twoFrattini_le X)
    ((XiP_inf_twoGroup_le_core p ho L R
      (T.isPGroup'.to_le (radicalSylowCentralizer_le _ _))).trans (twoCore_le_twoFrattini X))
    (not_le_twoFrattini X) hRJ hRE hf
  rcases hnonzero with hJ | hE
  · exact Or.inl (le_normalizer_of_irreducible X (T : Subgroup G) (thompsonJ R 0)
      hx.invariant hTJ (hcore.trans hRJ) hx.irreducible hJ)
  · exact Or.inr (le_normalizer_of_irreducible X (T : Subgroup G) E
      hx.invariant hTE (hcore.trans hRE) hx.irreducible hE)

/-- The source's unique maximal overgroup of XT controls J₀(R) or J₁(R).
Both indices are valid by the original faithful-module rank bound. -/
theorem controlledIndex_of_normality_choice (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hc : ControlledIndexNormalityChoice (XiP p L) (radicalSylowCentralizer T L)) :
    ∃ j : ℕ, j ≤ 1 ∧ j < twoRank (radicalSylowCentralizer T L) ∧
      thompsonJ (radicalSylowCentralizer T L) 0 ≤
        thompsonJ (radicalSylowCentralizer T L) j ∧
      normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
        normalizer (L : Set G) := by
  let R := radicalSylowCentralizer T L
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hRp : IsPGroup 2 R := T.isPGroup'.to_le (radicalSylowCentralizer_le _ _)
  have hr := controlledIndex_radical_rank h hL hn
  have hrR : 3 ≤ twoRank R := hr
  have hTR := sylow_normalizes_radicalSylowCentralizer hTL
  have hstanding := canonical_standing_of_star h hmany hL hn ho hd
    (hs L hL hn p Fact.out ho hd)
  have hu := hstanding.2.2.2.1
  rcases hc with hJ | hE
  · refine ⟨0,by omega,by omega,le_rfl,?_⟩
    exact normalizer_le_of_unique_maximalTwoLocal hu
      (hRp.to_le (thompsonJ_le R 0))
      (controlledIndex_thompson_ne_bot R (by omega))
      (sup_le hJ (hTR.trans (normalizer_le_thompson R 0)))
  · refine ⟨1,le_rfl,by omega,lemma_B_2_3_1 R (by omega) (by omega),?_⟩
    apply (controlledIndex_normalizer_omega (thompsonJ R 1)).trans
    exact normalizer_le_of_unique_maximalTwoLocal hu
      (omegaOneCenterAmbient_elementaryAbelian _).isPGroup
      (controlledIndex_omega_ne_bot _ (hRp.to_le (thompsonJ_le R 1))
        (controlledIndex_thompson_ne_bot R (by omega)))
      (sup_le hE (hTR.trans ((normalizer_le_thompson R 1).trans
        (controlledIndex_normalizer_omega _))))

/-- Conditional source selection, with precisely G.26.18 still to discharge. -/
theorem controlledIndex_of_factorization (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hf : ControlledIndexFactorization (XiP p L) (radicalSylowCentralizer T L)) :
    ∃ j : ℕ, j ≤ 1 ∧ j < twoRank (radicalSylowCentralizer T L) ∧
      thompsonJ (radicalSylowCentralizer T L) 0 ≤
        thompsonJ (radicalSylowCentralizer T L) j ∧
      normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
        normalizer (L : Set G) :=
  controlledIndex_of_normality_choice h hmany hs hL hn p ho hd
    (controlledIndex_normality_of_factorization h hL hn p ho hd hf)

/-- Application to the literal common-action consumer. Its other source
hypotheses are unchanged, and the factorization remains explicitly conditional. -/
theorem candidate_common_action_of_controlled_factorization (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C)
    (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hf : ControlledIndexFactorization (XiP p L) (radicalSylowCentralizer T L)) :
    ∃ j : ℕ, j ≤ 1 ∧ j < twoRank (radicalSylowCentralizer T L) ∧
      normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
        normalizer (L : Set G) ∧
      ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
        ⁅⁅omegaClosure T L Y j,canonicalSupplement T L⁆,thompsonCommutator T L Y j⁆ ≠ ⊥ ∧
        ∃ n : (commonModule T L Y j).Normal,
          letI := n
          ∃ e : IsElementaryAbelian 2 (commonModule T L Y j),
          letI := e
          CommonActionProperties (T : Subgroup G) L Y j := by
  obtain ⟨j,hj,hr,_,hN⟩ := controlledIndex_of_factorization h hmany hs hL hn p ho hd hf
  exact ⟨j,hj,hr,hN,candidate_common_action h hmany hs hrig hclass
    hL hn hH hTH hne hC hAC hN⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
