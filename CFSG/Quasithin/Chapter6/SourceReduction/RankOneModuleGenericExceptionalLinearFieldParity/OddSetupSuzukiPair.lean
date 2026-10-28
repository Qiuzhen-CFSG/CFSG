module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import Theory.SpecificGroups.Suzuki.SylowSupplement

/-!
# The genuine linear–Suzuki pair in the Cartan-exclusion argument

Let K be the exceptional PSL₃(4) residual and R the ambient image of the
solvable residual of C_G(K/O₂(K)). In the nonsolvable branch, the concrete
Suzuki quotient gives T = O₂(RT)(T ∩ R). Its Borel therefore normalizes T,
and Baumann control places that Borel in N_G(L).

If the left Cartan normalizes K, the opposite Borel normalizes R. Uniqueness
of the maximal two-local over LT and R's escape from N_G(L) make the generated
two-core trivial. Both literal parabolics have characteristic two. These
facts establish every genuine F.1.1 clause, as well as quasithinness and the
extra Borel-normality premise of F.1.12. The same source parabolics form a
faithful local rank-one triple in their generated group.

The ambient Sylow cannot lie in C_G(K/O₂(K)): its image in the centerless
PSL₃(4) quotient would be trivial, contradicting the quotient's two-rank.
Thus the independent F.1.12 Suzuki Sylow-containment theorem will exclude
the Cartan containment and give kernel solvability in odd degree. The last
two declarations keep that recognition theorem explicit; they do not prove
F.1.12 or unconditional parity. Final discharge remains with
qt-d-1222-linear-field-parity.

Source: Aschbacher–Smith, 5.1.16(2) and 5.1.17, printed pp.639–640;
F.1.1, F.1.9–12, printed pp.259–264 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
open ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

private theorem suzuki_borel_normalizes_ambient_sylow
    (R : Subgroup G) (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {m : ℕ} (hm : 0 < m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    borel R (T : Subgroup G) ≤ normalizer (T : Set G) := by
  have hn := normal_of_core_decomposition R (T : Subgroup G)
    (BenderSuzuki.MatrixGroups.suzuki_quotient_sylow_factorization R T hTR hm e)
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    (show (T : Subgroup G) ≤ (T : Subgroup G) ⊔ borel R (T : Subgroup G) from le_sup_left)).mp hn)

/-- The nonsolvable kernel's genuine Suzuki Borel normalizes T and hence L. -/
theorem quotientCentralizerResidual_borel_control
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    borel (quotientCentralizerResidual (residual H)) (T : Subgroup G) ≤
      normalizer (T : Set G) ⊓ normalizer (L : Set G) := by
  obtain ⟨he,_,m,hm,⟨e⟩⟩ := nonsolvable_quotientCentralizer_geometry h hH hK hm hns
  have hTR : (T : Subgroup G) ≤ normalizer (quotientCentralizerResidual (residual H) : Set G) := by
    rw [he]
    exact hH.1.1.2.trans (le_normalizer_residual H)
  have hB := suzuki_borel_normalizes_ambient_sylow _ hTR (by omega) e
  exact le_inf hB (hB.trans ((Stellmacher.normalizer_le_normalizer_baumann _).trans
    (baumann_normalizer_le_of_nonfaithful_residual h hH hK hnf)))

/-- Assuming the Cartan containment to be excluded, the actual Suzuki residual
and L satisfy every genuine F.1.1 clause, on the full ambient Sylow T. -/
theorem quotientCentralizerResidual_hypothesisF11
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hA : A ≤ normalizer (residual H : Set G))
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    HypothesisF11 ![L,quotientCentralizerResidual (residual H)] (T : Subgroup G) := by
  let R := quotientCentralizerResidual (residual H)
  let N := normalizer (residual H : Set G)
  obtain ⟨he,hout,m,hmpos,⟨e⟩⟩ := nonsolvable_quotientCentralizer_geometry h hH hK hm hns
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (le_normalizer_residual H)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := hTN.trans he.ge
  have hBR := quotientCentralizerResidual_borel_control h hH hK hnf hm hns
  have hBL : borel L (T : Subgroup G) ≤ normalizer (R : Set G) := by
    change localBorel T L ≤ _
    rw [← c.left_sup_intersection h.sylow_normalizes]
    exact sup_le (inf_le_left.trans hTR) (hA.trans he.ge)
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN)
      (le_componentOrbit _ _)
  rw [horbit] at hmax
  have hLstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop,?_⟩
    intro J hJ hLJ
    exact le_antisymm (h.local_mem.1.2 hJ hLJ) hLJ
  have hu := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hLstar).normalizer_unique
  have horbitL : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl h.sylow_normalizes)
      (le_componentOrbit _ _)
  rw [horbitL] at hu
  refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,?_,?_⟩
  · intro i; fin_cases i
    · exact h.sylow_normalizes
    · exact hTR
  · intro i; fin_cases i
    · obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
      exact ⟨P,by change (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L; rw [hP,subgroupOf_map_subtype]⟩
    · obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T R hTR
      exact ⟨P,by change (P : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R; rw [hP,subgroupOf_map_subtype]⟩
  · intro i; fin_cases i
    · exact .linear n (by have := h.exponent; omega) h.linear
    · exact .suzuki m ⟨e⟩
  · intro i; fin_cases i
    · exact hBR.trans inf_le_right
    · exact hBL
  · change pCore 2 (L ⊔ R ⊔ (T : Subgroup G) : Subgroup G) = ⊥
    have heq : L ⊔ R ⊔ (T : Subgroup G) = (L ⊔ (T : Subgroup G)) ⊔ R := by ac_rfl
    rw [heq]
    exact twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ _ _ hu hout
  · intro i; fin_cases i
    · apply generalizedFitting_eq_pCore_of_sylow_overgroup T _ (normalizer (L : Set G))
        (le_sup_right.trans le_sup_left)
      · exact sup_le (sup_le L.le_normalizer h.sylow_normalizes) (hBR.trans inf_le_right)
      · exact h.qtke.evenCharacteristic T _ h.maximal h.sylow_normalizes
    · apply generalizedFitting_eq_pCore_of_sylow_overgroup T _ N
        (le_sup_right.trans le_sup_left)
      · exact sup_le (sup_le (R.le_normalizer.trans he.le) hTN) (hBL.trans he.le)
      · exact h.qtke.evenCharacteristic T N hmax hTN


/-- The full ambient Sylow cannot centralize the PSL₃(4) quotient. In
particular it cannot lie in the residual of that quotient-centralizer. -/
theorem sylow_not_le_linear_quotientCentralizer
    (K : Subgroup G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ¬ (T : Subgroup G) ≤ quotientCentralizer K := by
  intro hTC
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply (center _).eq_bot_iff_forall.mpr
    intro x hx
    apply e.injective
    rw [map_one]
    have he : e x ∈ center PSL(3,F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    simpa only [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F),mem_bot] using he
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let q := QuotientGroup.mk' (pCore 2 K)
  have hPK : (P : Subgroup K) ≤ pCore 2 K := by
    intro k hk
    rw [hP] at hk
    obtain ⟨a,ha,he⟩ := hTC hk
    have he' : a = ⟨k,K.le_normalizer k.property⟩ := Subtype.ext he
    have hinner : MulAut.conj (q k) = 1 := by
      rw [← normalizerQuotientAction_inner K (pCore 2 K)]
      exact he' ▸ ha
    have hqk : q k = 1 := (MulAut.conj_injective_of_center_eq_bot hz)
      (hinner.trans (map_one MulAut.conj).symm)
    exact (QuotientGroup.eq_one_iff k).mp hqk
  let S := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hS : (S : Subgroup (K ⧸ pCore 2 K)) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hPK)
  have hodd : ¬ 2 ∣ Nat.card (K ⧸ pCore 2 K) := by
    have hs := S.not_dvd_index
    rwa [hS,index_bot] at hs
  have hr := PrimeRank.eq_zero_iff_not_dvd_card.mpr hodd
  rw [primeRank_congr 2 e,Matrix.PSL3Even.two_rank F (n := 2) (by decide) hF] at hr
  omega

/-- All inputs to the Suzuki row of F.1.12 hold on the original pair;
its predicted Sylow containment is impossible in the literal centralizer. -/
theorem quotientCentralizerResidual_F112_inputs
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hA : A ≤ normalizer (residual H : Set G))
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let R := quotientCentralizerResidual (residual H)
    HypothesisF11 ![L,R] (T : Subgroup G) ∧
      IsQuasithin (generated ![L,R] (T : Subgroup G)) ∧
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal ∧
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
      ¬ (T : Subgroup G) ≤ R := by
  let R := quotientCentralizerResidual (residual H)
  have hf := quotientCentralizerResidual_hypothesisF11 h hH hK hnf hm c hA hns
  refine ⟨hf,h.qtke.quasithin.subgroup _,?_,?_,?_⟩
  · exact (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le (T : Subgroup G).le_normalizer
        ((quotientCentralizerResidual_borel_control h hH hK hnf hm hns).trans inf_le_left))
  · exact (nonsolvable_quotientCentralizer_geometry h hH hK hm hns).2.2
  · intro hTR
    exact sylow_not_le_linear_quotientCentralizer (residual H)
      (hH.1.1.2.trans (le_normalizer_residual H)) (linear_residual_quotient hm)
      (hTR.trans (map_subtype_le _))

/-- The same literal parabolics form the faithful rank-one triple in the
generated group; its complete overlap is retained. -/
theorem quotientCentralizerResidual_faithfulTriple
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hA : A ≤ normalizer (residual H : Set G))
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let pair := ![L,quotientCentralizerResidual (residual H)]
    LocallyRankOneTriple
      (fun i => (parabolic pair (T : Subgroup G) i).subgroupOf (generated pair (T : Subgroup G)))
      ((commonBorel pair (T : Subgroup G)).subgroupOf (generated pair (T : Subgroup G))) :=
  (quotientCentralizerResidual_hypothesisF11 h hH hK hnf hm c hA hns).generatedLocallyRankOneTriple

/-- The final Cartan-exclusion step in 5.1.16(2), conditional only on the
independent Suzuki containment consequence of F.1.12 for this linear factor. -/
theorem cartan_not_normalizes_of_suzuki_pair_containment
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hrec : ∀ R : Subgroup G,
      HypothesisF11 ![L,R] (T : Subgroup G) →
      IsQuasithin (generated ![L,R] (T : Subgroup G)) →
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal →
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ≤ R)
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    ¬ A ≤ normalizer (residual H : Set G) := by
  intro hA
  obtain ⟨hf,hq,hn,hs,hnot⟩ :=
    quotientCentralizerResidual_F112_inputs h hH hK hnf hm c hA hns
  exact hnot (hrec _ hf hq hn hs)

/-- The odd-degree Cartan containment and the preceding exclusion imply
solvability of the literal quotient-action kernel. Only F.1.12 recognition
is retained as an independent premise. -/
theorem quotientCentralizerKernel_solvable_of_odd_and_suzuki_containment
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hrec : ∀ R : Subgroup G,
      HypothesisF11 ![L,R] (T : Subgroup G) →
      IsQuasithin (generated ![L,R] (T : Subgroup G)) →
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal →
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ≤ R) :
    Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker := by
  by_contra hns
  exact (cartan_not_normalizes_of_suzuki_pair_containment h hH hK hnf hm c hrec hns)
    (cartan_normalizes_residual_of_odd h hH c hodd hK hnf)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
