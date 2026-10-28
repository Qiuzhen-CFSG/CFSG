module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.Setup
public import Theory.GroupTheory.SylowCoreQuotientProduct
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCoreSupplement
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound

/-!
# The literal odd-degree quotient and its residual factor

The action of H=O²(H)T on the centerless residual quotient has kernel O₂(H).
The actual residual image is F*(H/O₂(H)), and the inner and full automorphism
rank calculations give binary rank exactly four. In odd degree D_L acts
trivially on this residual quotient, so D_L meets H trivially. Its proved
central image then yields the original product

  HD_L/O₂(HD_L) ≃ (H/O₂(H)) × D_L.

The equivalence is evaluated on the original subgroup representatives.
Oddness of D_L gives binary rank four and places every representative of
an involution modulo O₂(HD_L) in H. The final theorem applies this to the
literal LargeDisplacement contract; it does not require order-two lifts.
The natural/TI construction and the displacement lower bound remain with
qt-d-1222-linear-field-parity.

Source: Aschbacher–Smith 5.1.17, printed p.641 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

private theorem model_centerless {X : Type*} [Group X]
    (hm : ClassicalGroup.IsPSL X 3 4) : center X = ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  apply (center X).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have hh : e x ∈ center PSL(3,F) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
  simpa only [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F), mem_bot] using hh

omit [Finite G] in
private theorem residual_model
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H)) 3 4 := by
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  exact hm.of_mulEquiv (QuotientGroup.congr (pCore 2 (pResidual 2 H))
    (pCore 2 (residual H)) e (pCore_map_iso 2 e)).symm

omit [Finite G] in
private theorem supplement_kernel (K X : Subgroup G)
    (hgen : K ⊔ (T : Subgroup G) = X) (hXN : X ≤ normalizer (K : Set G))
    (hz : center (K ⧸ pCore 2 K) = ⊥) :
    ((normalizerQuotientAction K (pCore 2 K)).comp (inclusion hXN)).ker = pCore 2 X := by
  subst X
  exact pCoreJoinAction_kernel 2 (le_sup_right.trans hXN) T.isPGroup' hz

/-- The actual residual image is the generalized Fitting subgroup of H/O₂(H). -/
theorem residual_coreQuotient_generalizedFitting
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    generalizedFitting (H ⧸ pCore 2 H) =
      (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) := by
  have hqs : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    exact IsQuasisimple.of_mulEquiv e.symm
  let := hqs
  exact generalizedFitting_coreQuotient_eq_of_two_supplement (pResidual 2 H)
    (T.subtype hTH) (T.subtype hTH).isPGroup' (pResidual_sup_sylow_eq_top (T.subtype hTH))

/-- The generalized Fitting subgroup retains the supplied PSL₃(4) model. -/
theorem residual_coreQuotient_fitting_model
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ClassicalGroup.IsPSL (generalizedFitting (H ⧸ pCore 2 H)) 3 4 := by
  have hg := residual_coreQuotient_generalizedFitting hTH hm
  exact hm.of_mulEquiv ((coreQuotientEquivImage 2 (pResidual 2 H)).trans
    (MulEquiv.subgroupCongr hg.symm)).symm

/-- The residual–Sylow extension has binary rank exactly four modulo its two-core. -/
theorem residual_sylow_extension_two_rank
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    primeRank 2 (H ⧸ pCore 2 H) = 4 := by
  let K := residual H
  let hTK := hTH.trans (le_normalizer_residual H)
  have hmK := residual_model hm
  have hz := model_centerless hmK
  let J := K ⊔ (T : Subgroup G)
  let e := pCoreJoinQuotientEquivRange 2 hTK T.isPGroup' hz
  have heq : J = H := residual_sup_sylow T H hTH
  have hr : primeRank 2 (H ⧸ pCore 2 H) = primeRank 2 (pCoreJoinAction 2 hTK).range := by
    exact (congrArg (fun X : Subgroup G => primeRank 2 (X ⧸ pCore 2 X)) heq).symm.trans
      (primeRank_congr 2 e)
  rw [hr]
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hmK
  have hi : primeRank 2 (MulAut.innerSubgroup (K ⧸ pCore 2 K)) = 4 := by
    let ei : (K ⧸ pCore 2 K) ≃* MulAut.innerSubgroup (K ⧸ pCore 2 K) :=
      MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
    rw [← primeRank_congr 2 ei, primeRank_congr 2 f]
    exact Matrix.PSL3Even.two_rank F (n := 2) (by decide) hF
  apply le_antisymm
  · apply (primeRank_subgroup_le 2 _).trans
    rw [primeRank_congr 2 (MulAut.congr f)]
    exact le_of_eq (Matrix.PSL3Even.automorphism_two_rank_eq F (n := 2) (by decide) hF)
  · rw [← hi]
    exact primeRank_mono 2 (inner_le_pCoreJoinAction_range 2 hTK)

/-- Trivial residual action puts the Cartan intersection with H in O₂(H); oddness kills it. -/
theorem cartan_disjoint_outside_of_odd
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    Disjoint H A := by
  have hk := supplement_kernel (residual H) H (residual_sup_sylow T H hH.1.1.2)
    (le_normalizer_residual H) (model_centerless (residual_model hm))
  have ha := cartan_residual_action_trivial_of_odd h hH c hodd hK hnf hm
  have hAQ : Disjoint A (H.pCoreIn 2) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 H).exists_card_eq
    rw [hk]
    exact ((cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd).of_dvd_right
      (by decide : 2 ∣ 6)).pow_right k
  rw [Subgroup.disjoint_def]
  intro x hxH hxA
  apply Subgroup.disjoint_def.mp hAQ hxA
  obtain ⟨a,ha0,he⟩ := ha hxA
  have he' : a = inclusion (le_normalizer_residual H) ⟨x,hxH⟩ := Subtype.ext he
  have hm0 : (⟨x,hxH⟩ : H) ∈ pCore 2 H := by
    rw [← hk]
    change normalizerQuotientAction (residual H) (pCore 2 (residual H))
      (inclusion (le_normalizer_residual H) ⟨x,hxH⟩) = 1
    exact he' ▸ ha0
  exact mem_map_of_mem H.subtype hm0

/-- The Cartan preserves both factors of H=O²(H)T in odd degree. -/
theorem cartan_normalizes_outside_of_odd
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    A ≤ normalizer (H : Set G) := by
  rw [← residual_sup_sylow T H hH.1.1.2]
  exact (le_inf (cartan_normalizes_residual_of_odd h hH c hodd hK hnf)
    (cartan_normalizes_sylow_of_odd c h.sylow_normalizes h.linear hodd)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The source quotient product, keeping the actual H and Cartan on every representative. -/
theorem odd_join_quotient_product
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ∃ e : ((H ⧸ pCore 2 H) × A) ≃*
        ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)),
      ∀ (x : H) (a : A),
        e (QuotientGroup.mk' (pCore 2 H) x, a) =
          QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
            ⟨(x : G) * (a : G), mul_mem_sup x.property a.property⟩ :=
  exists_pCoreQuotient_product_of_sylow_le hH.1.1.2
    (cartan_normalizes_outside_of_odd h hH c hodd hK hnf)
    (cartan_disjoint_outside_of_odd h hH c hodd hK hnf hm)
    (cartan_image_central_of_odd h hH c hodd hK hnf hm)

/-- The precise binary rank needed in the parity seed is four. -/
theorem odd_join_quotient_two_rank
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    primeRank 2 ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) = 4 := by
  obtain ⟨e,_⟩ := odd_join_quotient_product h hH c hodd hK hnf hm
  rw [← primeRank_congr 2 e, primeRank_prod_eq_add,
    residual_sylow_extension_two_rank hH.1.1.2 hm]
  have hzero : primeRank 2 A = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr
    (Nat.prime_two.coprime_iff_not_dvd.mp
      (((cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd).of_dvd_right
        (by decide : 2 ∣ 6)).symm))
  omega

/-- Adjoining the odd-degree Cartan preserves the literal embedded two-core. -/
theorem odd_join_twoCore
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    (H ⊔ A).pCoreIn 2 = H.pCoreIn 2 :=
  pCoreIn_sup_eq_of_sylow_le hH.1.1.2 (cartan_normalizes_outside_of_odd h hH c hodd hK hnf)

/-- Every involution modulo O₂(HD_L) already has its chosen representative in H. -/
theorem odd_join_involution_lift_mem_outside
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {y : G} (hy : y ∈ H ⊔ A) (hy2 : y ^ 2 ∈ (H ⊔ A).pCoreIn 2) : y ∈ H := by
  have hA : Odd (Nat.card A) := Nat.coprime_two_right.mp
    ((cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd).of_dvd_right
      (by decide : 2 ∣ 6))
  exact mem_left_of_square_mem_join_twoCore hH.1.1.2
    (cartan_normalizes_outside_of_odd h hH c hodd hK hnf)
    (cartan_disjoint_outside_of_odd h hH c hodd hK hnf hm) hA
    (cartan_image_central_of_odd h hH c hodd hK hnf hm) hy hy2

/-- The displacement contract can be checked on H, with the same module and quotient. -/
theorem largeDisplacement_iff_on_outside_of_odd
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (V : Subgroup G) :
    LargeDisplacement (setup T L V H A) ↔
      ∀ y ∈ H, y ^ 2 ∈ H.pCoreIn 2 → y ∉ H.pCoreIn 2 →
        9 ≤ displacement (setup T L V H A) y := by
  have hc := odd_join_twoCore h hH c hodd hK hnf
  change (∀ y ∈ H ⊔ A, y ^ 2 ∈ (H ⊔ A).pCoreIn 2 → y ∉ (H ⊔ A).pCoreIn 2 → _) ↔ _
  rw [hc]
  constructor
  · intro hb y hy hy2 hy0
    exact hb y ((le_sup_left : H ≤ H ⊔ A) hy) hy2 hy0
  · intro hb y hy hy2 hy0
    exact hb y (odd_join_involution_lift_mem_outside h hH c hodd hK hnf hm hy
      (hc.symm ▸ hy2)) hy2 hy0

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
