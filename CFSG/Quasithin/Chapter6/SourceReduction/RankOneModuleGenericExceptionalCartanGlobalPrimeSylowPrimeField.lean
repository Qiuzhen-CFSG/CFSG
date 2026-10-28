module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowTwentyFive
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.SpecificGroups.PSL2.PrimeFourSolvable
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer

/-!
# Odd-prime PSL₂ containers at the smaller changed Sylow

A proper containing component with an odd-prime PSL₂ quotient forces the
actual image of the selected right factor to be A₅. The original mixed
join of the escaping actor, source Sylow and right Hall intersection is
solvable. Its quotient contains the actual A₄ right Borel: the restricted
quotient map has two-group kernel, so it reflects Sylow normalizers.
Dickson's subgroup theorem then excludes the quintic actor.

For the remaining cubic actor, the intrinsic right quotient is PSL₂(4),
so the original Hall intersection has order three and centralizes the
actor. Their elementary abelian join has an action image of rank at most
one in the odd-prime PSL₂ container. The marked Hall subgroup fills this
image, forcing normalization of the perfect right factor, a contradiction.

The final theorem applies the exclusion to the same source pair and
changed-Sylow witness as the preceding sieve, retaining all earlier model
exclusions. It does not assert marked zero-core recognition, the remaining
containing-model cases, larger-Sylow assembly or higher-field reduction.
Those remain with the original local-to-global owner; h513 is unchanged.
Source: Aschbacher–Smith A.3.12(8), 5.1.13 and 5.2.2,
printed pp.47–50, 636–638, 648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The proper prime-field container identifies the actual quotient image
as A₅ and retains the exceptional prime congruences. -/
theorem LocalData.source_overcomponent_prime_field_image
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n q : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hq : q.Prime) (ho : Odd q) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q) :
    Chapter1.Section02.A312ExceptionalPrime q ∧
      Nonempty (((R.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≃*
        alternatingGroup (Fin 5)) := by
  let π := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map π
  let Kbar := (K.subgroupOf X).map π
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hl : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map π)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hlt := d.right_image_lt h hH ⟨S,hS⟩ hRX hKX hRK hK
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  exact ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
    P hl (hK.map_quotient (pCore 2 X)) hlt.le hlt.ne hq ho (hm.of_mulEquiv eK)

private theorem five_borel_marking
    {Y : Type*} [Group Y] [Finite Y] (e : Y ≃* alternatingGroup (Fin 5)) (P : Sylow 2 Y) :
    Nonempty (alternatingGroup (Fin 4) ≃* normalizer (P : Set Y)) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
  let : MulAction.IsPretransitive (alternatingGroup (Fin 5)) (Fin 5) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) (4 : Fin 5) i
  let a : alternatingGroup (Fin 4) ≃* normalizer (Q : Set (alternatingGroup (Fin 5))) :=
    BinaryPermutation.AlternatingFiveBorel.marking.trans
      ((MulAction.stabilizerEquivStabilizer hg.symm).trans (MulEquiv.subgroupCongr hi.symm))
  exact ⟨a.trans (((e.subgroupMap (normalizer (P : Set Y))).trans
    (MulEquiv.subgroupCongr (map_equiv_normalizer_eq (P : Subgroup Y) e))).symm)⟩

/-- The original prime must be cubic in every proper odd-prime PSL₂ container.
The quintic exclusion uses the actual right Borel in the solvable mixed join. -/
theorem LocalData.source_overcomponent_prime_field_actor
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p q : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hq : q.Prime) (ho : Odd q) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q) :
    p = 3 := by
  rcases hd.prime with hp | hp
  · exact hp
  subst p
  exfalso
  let X := generated L H D R ⊔ normalizingSylow T R
  let π := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map π
  let Kbar := (K.subgroupOf X).map π
  let Dbar := (D.subgroupOf X).map π
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hSX : Global.sourceS L H ≤ X :=
    (d.sourceS_le_normalizingSylow h hH).trans le_sup_right
  obtain ⟨hexc,⟨eR⟩⟩ := d.source_overcomponent_prime_field_image h hH hSyl hRX hKX hRK hK hq ho hm
  have hq3 : 3 < q := by
    have h2 := hq.two_le
    have hodd := ho.not_two_dvd_nat
    have h5 := hexc.2.2.1
    by_contra hn
    have he : q = 3 := by omega
    norm_num [he] at h5
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact q.Prime := ⟨hq⟩
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hRKbar : Rbar ≤ Kbar := map_mono (comap_mono hRK.le)
  obtain ⟨hc,hdis,_⟩ := d.right_quotient_prime_orbit h hH c hd hz hRX hDX hSyl
  have hdC : Disjoint Dbar (centralizer (Kbar : Set (X ⧸ pCore 2 X))) :=
    hdis.mono_right ((centralizer_le hRKbar).trans
      (centralizer_le_normalizer (Rbar : Set (X ⧸ pCore 2 X))))
  let Y := (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)
  have hYX : Y ≤ X := sup_le (sup_le hDX hSX) (inf_le_right.trans hRX)
  have hds := d.actor_join_solvable h hH c hd
  let : Group.IsSolvable (D ⊔ normalizingSylow T R : Subgroup G) := hds
  let : Group.IsSolvable (D ⊔ Global.sourceS L H : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (sup_le_sup_left (d.sourceS_le_normalizingSylow h hH) D))
  have hBodd : Odd (Nat.card B) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  let : Group.IsSolvable (B ⊓ R : Subgroup G) := odd_order_theorem _
    (hBodd.of_dvd_nat (card_dvd_of_le inf_le_left))
  let : Group.IsSolvable Y := Group.isSolvable_sup_of_normalizes _ _
    (inf_le_left.trans (le_sup_right.trans d.TB_normalizes_left))
  let Ybar := (Y.subgroupOf X).map π
  let : Group.IsSolvable (Y.subgroupOf X) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hYX).toMonoidHom) (subgroupOfEquivOfLe hYX).injective
  let : Group.IsSolvable Ybar := Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
  have hDY : Dbar ≤ Ybar := map_mono (comap_mono (le_sup_left.trans le_sup_left))
  obtain ⟨P,hP⟩ := d.right_sylow
  let r : R →* Rbar := (π.subgroupMap (R.subgroupOf X)).comp
    (subgroupOfEquivOfLe hRX).symm.toMonoidHom
  have hr : Function.Surjective r :=
    (π.subgroupMap_surjective _).comp (subgroupOfEquivOfLe hRX).symm.surjective
  have hk : IsPGroup 2 r.ker := by
    change IsPGroup 2 (((π.subgroupMap (R.subgroupOf X)).comp
      (subgroupOfEquivOfLe hRX).symm.toMonoidHom).ker)
    rw [← MonoidHom.comap_ker,ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype.comap_of_injective _
      (subgroupOfEquivOfLe hRX).symm.injective
  let Pbar := P.mapSurjective hr
  have hn : (normalizer (Pbar : Set Rbar)).comap r = normalizer (P : Set R) := by
    change (normalizer (Pbar : Subgroup Rbar)).comap r = normalizer (P : Subgroup R)
    rw [comap_normalizer_eq_of_surjective _ hr]
    change normalizer (((P : Subgroup R).map r).comap r : Set R) = _
    rw [comap_map_eq_self (hk.le_sylow_of_normal P)]
  obtain ⟨a⟩ := five_borel_marking eR Pbar
  let j : alternatingGroup (Fin 4) →* Kbar :=
    (inclusion hRKbar).comp ((normalizer (Pbar : Set Rbar)).subtype.comp a.toMonoidHom)
  have hj : Function.Injective j :=
    (inclusion_injective hRKbar).comp (Subtype.val_injective.comp a.injective)
  apply Theory.PSL2.PrimeFourSolvable.no_five_actor ho hq3 hF Kbar Dbar Ybar
    (eK.trans e) hc hdC hDY j hj
  intro x
  obtain ⟨y,hy⟩ := hr (a x)
  have hyN : y ∈ normalizer (P : Set R) := by
    rw [←hn]
    change r y ∈ normalizer (Pbar : Set Rbar)
    rw [hy]
    exact (a x).property
  have hyB : (y : G) ∈ ChapterF.Source.borel R (Global.sourceS L H) := by
    change y ∈ (ChapterF.Source.borel R (Global.sourceS L H)).subgroupOf R
    rw [ChapterF.Source.borel_subgroupOf_eq_sylowNormalizer R (Global.sourceS L H) P hP]
    exact hyN
  have hyY : (y : G) ∈ Y := by
    rw [d.right_borel] at hyB
    have hbY : (Global.sourceS L H ⊓ R) ⊔ (B ⊓ R) ≤ Y :=
      sup_le (inf_le_left.trans (le_sup_right.trans le_sup_left)) le_sup_right
    exact hbY hyB
  have hh : π (⟨y,hRX y.property⟩ : X) ∈ Ybar :=
    mem_map_of_mem π (show (⟨y,hRX y.property⟩ : X) ∈ Y.subgroupOf X from hyY)
  have he : π (⟨y,hRX y.property⟩ : X) = ((a x : Rbar) : X ⧸ pCore 2 X) :=
    congrArg Subtype.val hy
  exact he ▸ hh

/-- Every proper odd-prime PSL₂ container is excluded at the smaller changed
Sylow. The original cubic Hall intersection accounts for the whole cubic
action image, forcing the forbidden normalization of the selected factor. -/
theorem LocalData.source_overcomponent_not_odd_prime_field
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p q : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hq : q.Prime) (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q := by
  intro hm
  have hp := d.source_overcomponent_prime_field_actor h hH c hd hz hSyl hRK hKX hK hKn hq ho hm
  subst p
  have hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
    by_contra hnot
    exact d.source_overcomponent_not_primePSL2 h hH hSyl
      (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hnot hq ho hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let X := generated L H D R ⊔ normalizingSylow T R
  let := Chapter1.mem_L_isPerfect (d.right_mem_local_family h hH)
  have hXK : X ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKX).mp hKn
  have hDK : D ≤ normalizer (K : Set G) :=
    (le_sup_left.trans le_sup_left).trans hXK
  obtain ⟨S,hS⟩ := hSyl
  have hQ : K.pCoreIn 2 ≤ normalizer (R : Set G) :=
    (pCoreIn_mono_of_normalizes hKX hXK).trans
      ((hS ▸ pCoreIn_le_sylow X S).trans inf_le_right)
  have hC : Nat.card (B ⊓ R : Subgroup G) = 3 := by
    simpa using d.right_cartan_card c (m := 2) hA5
  have hCD : B ⊓ R ≤ centralizer (D : Set G) :=
    inf_le_left.trans (c.centralizes_prime_actor h hd)
  let : IsCyclic D := isCyclic_of_prime_card hd.card
  let : IsCyclic (B ⊓ R : Subgroup G) := isCyclic_of_prime_card hC
  let : IsElementaryAbelian 3 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => by simpa only [hd.card] using (pow_card_eq_one' (x := x))) }
  let : IsElementaryAbelian 3 (B ⊓ R : Subgroup G) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => by simpa only [hC] using (pow_card_eq_one' (x := x))) }
  let : IsElementaryAbelian 3 (D ⊔ (B ⊓ R) : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hCD
  have hA : D ⊔ (B ⊓ R) ≤ normalizer (K : Set G) :=
    sup_le hDK ((inf_le_right.trans hRK.le).trans K.le_normalizer)
  let : Fact q.Prime := ⟨hq⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  have hr : primeRank 3 K ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_congr 3 (e.trans (GorensteinWalter.psl2RingEquiv eF))]
    exact Theory.PSL2.primeField_odd_rank (by decide)
  have hn := Theory.PSL2.primeField_cartan_normalizes_perfect_subgroup
    R K (D ⊔ (B ⊓ R)) (B ⊓ R) hRK.le hA le_sup_right inf_le_right hQ hC hr hq ho hF e
  exact d.prime_actor_not_normalizes_right h hH c hd hz (le_sup_left.trans hn)

/-- Apply the odd-prime exclusion to the same constructed source pair and
changed Sylow, retaining the earlier model exclusions. -/
theorem source_prime_pair_odd_containing_exclusions
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
              ¬ (IsAlternating (K ⧸ pCore 2 K) 5 ∨ IsAlternating (K ⧸ pCore 2 K) 6 ∨
                IsAlternatingCover (K ⧸ pCore 2 K) 6) ∧
              (∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
                IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨ IsSU (K ⧸ pCore 2 K) 3 (2 ^ k))) ∧
              ¬ RankTwoTheoremC (K ⧸ pCore 2 K) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) ∧
              ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∧
              (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 →
                ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7)) ∧
              (∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_containing_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,_⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,
      fun _ hq ho => d.source_overcomponent_not_odd_prime_field h hH c hd hz hSyl
        hRK hKX hK hKn hq ho⟩
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
