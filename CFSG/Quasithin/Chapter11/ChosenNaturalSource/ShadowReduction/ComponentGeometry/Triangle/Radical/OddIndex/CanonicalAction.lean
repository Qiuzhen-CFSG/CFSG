module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.PlaneAction
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.Fitting.Equiv
public import Theory.Quasithin.Rank

/-!
# Canonical odd-core actions in the noncentral component case

The genuine noncentral branch of A.3.6 identifies the kernel of every
full-core Frattini action with the Fitting subgroup. Consequently the
centralizer of each active prime core in any nonsolvable seed is solvable,
so the seed acts nontrivially. The scalar-plane calculation and Burnside
kernel then make the mutual commutator centralize every prime core, hence
all of F(K), with arbitrary homocyclic exponents retained.

Self-centralization of F*(K) = F(K), applied inside the normal join KR,
detects the two-core. Passing through the literal ambient two-core quotient
preserves component membership, nonsolvability of the seed and its core
commutator. No action of the full simple ambient group or Fitting-index
bound is assumed. CanonicalSource applies this to the original flag.
The earlier-source discharge remains with the component and natural-shadow
assembly owners. The independent index APIs remain conditional and are not
needed for the original 11.4.1(3) conclusions.

Source: Aschbacher–Smith, A.3.6, pp.43–45, and 11.4.1(3), pp.775–776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual embedded prime core has centralizer in K contained in F(K). -/
theorem canonical_core_centralizer_le_fitting
    (K : Subgroup G) {p : ℕ}
    (hk : (FittingActions.coreFrattiniAction p K).ker = fittingSubgroup K) :
    K ⊓ centralizer ((pCore p K).map K.subtype : Set G) ≤
      (fittingSubgroup K).map K.subtype := by
  rintro x ⟨hxK,hxC⟩
  let k : K := ⟨x,hxK⟩
  have ha : FittingActions.coreAction p K k = 1 := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change x * (y : K) * x⁻¹ = y
    rw [← hxC y (mem_map_of_mem K.subtype y.property)]
    simp only [mul_assoc,mul_inv_cancel,mul_one]
  have hf : k ∈ fittingSubgroup K := by
    rw [← hk]
    change quotientAut _ (FittingActions.coreAction p K k) = 1
    rw [ha,map_one]
  exact mem_map_of_mem K.subtype hf

/-- The centralizer in the seed is solvable, using the canonical full-core action kernel. -/
theorem canonical_seed_centralizer_solvable
    (A K : Subgroup G) (hAK : A ≤ K) {p : ℕ}
    (hk : (FittingActions.coreFrattiniAction p K).ker = fittingSubgroup K) :
    Group.IsSolvable ((centralizer ((pCore p K).map K.subtype : Set G)).subgroupOf A) := by
  let C := (centralizer ((pCore p K).map K.subtype : Set G)).subgroupOf A
  let F := (fittingSubgroup K).map K.subtype
  let : Group.IsSolvable F := Group.isSolvable_of_surjective
    (f := K.subtype.subgroupMap (fittingSubgroup K))
    (K.subtype.subgroupMap_surjective (fittingSubgroup K))
  let a : C →* F := ((A.subtype.comp C.subtype).codRestrict F (by
    intro x
    exact canonical_core_centralizer_le_fitting K hk ⟨hAK x.val.property,x.property⟩))
  exact Group.isSolvable_of_isSolvable_injective (f := a) (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : F => (z : G)) he)

private theorem canonical_core_frattini_card
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hs : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    Nat.card (pCore p K ⧸ frattini (pCore p K)) ≤ p ^ 2 := by
  rcases hs with hn | hn
  · obtain ⟨_, _, hc⟩ := CFSG.Quasithin.Chapter1.RadicalStructure.natural_core hn hd
    exact hc ▸ Nat.card_le_card_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  · rw [Nat.card_congr (FittingActions.coreOmegaEquiv (Or.inr hn) hd).toEquiv,
      (CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent.frattini_shape hn hd).2]

/-- A.3.6 discharges all prime-core action hypotheses, and the prime cores generate F(K). -/
theorem commutator_centralizes_canonical_fitting
    {κ : GroupClass} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (A K R X : Subgroup G) [K.Normal] [Group.IsPerfect A]
    (hK : K.IsCComponent) (hn : ¬ fittingSubgroup K ≤ center K)
    (hAK : A ≤ K) (hA : ¬ Group.IsSolvable A)
    (hR : IsPGroup 2 R) (hXR : X ≤ normalizer (R : Set G))
    (hc : ⁅R,A⁆ ≤ A.pCoreIn 2) :
    ⁅R,X⁆ ≤ centralizer ((fittingSubgroup K).map K.subtype : Set G) := by
  obtain ⟨hs,hscommon⟩ := ChapterA.Section03.NoncentralFitting.structure_of_noncentral hG hO hK hn
  have hcon : A36Conclusion K := ⟨hs.elim A36Alternative.natural A36Alternative.nilpotent,hscommon⟩
  have ha := (FittingActions.strengthened_frattini_actions hG hO hK hcon).2
    (ChapterA.Section03.NoncentralFitting.not_quasisimple_of_noncentral_fitting hn)
  have heach (p : ℕ) [Fact p.Prime] :
      ⁅R,X⁆ ≤ centralizer ((pCore p K).map K.subtype : Set G) := by
    by_cases hd : p ∣ Nat.card (fittingSubgroup K)
    · let P := (pCore p K).map K.subtype
      let : P.Normal := ConjAct.normal_of_characteristic_of_normal
      let e : pCore p K ≃* P := (pCore p K).equivMapOfInjective K.subtype K.subtype_injective
      have hdP : Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
        rw [← Nat.card_congr (QuotientGroup.congr _ _ e (frattini_map_equiv e)).toEquiv]
        exact canonical_core_frattini_card hs hd
      obtain ⟨hp,hker,_⟩ := ha.2.2 p hd
      let a : G →* MulAut P := MulAut.conjNormal
      have hak : a.ker = centralizer (P : Set G) := MulAut.conjNormal_ker_eq_centralizer P
      have hsolv : Group.IsSolvable (a.comp A.subtype).ker := by
        change Group.IsSolvable (a.ker.subgroupOf A)
        rw [hak]
        exact canonical_seed_centralizer_solvable A K hAK hker
      have hne : a.comp A.subtype ≠ 1 := by
        intro he
        rw [he,MonoidHom.ker_one] at hsolv
        let := hsolv
        exact hA (Group.isSolvable_of_surjective (f := (topEquiv (G := A)).toMonoidHom)
          topEquiv.surjective)
      rw [← hak]
      exact commutator_le_odd_core_action_ker
        ((Fact.out : p.Prime).odd_of_ne_two (by omega))
        (pCore_isPGroup.map K.subtype) hdP A R X hR hXR a hne hc
    · have he : pCore p K = ⊥ := card_eq_one.mp
        ((pCore_isPGroup (p := p) (G := K)).card_eq_or_dvd.resolve_right
          (fun hdP => hd (hdP.trans (card_dvd_of_le (pCore_le_fitting K p)))))
      rw [he,Subgroup.map_bot]
      intro x _ y hy
      have hy1 : y = 1 := mem_bot.mp hy
      simp only [hy1,one_mul,mul_one]
  rw [le_centralizer_iff]
  rw [fitting_eq_sup_pCore,Subgroup.map_iSup]
  exact iSup_le (fun p => le_centralizer_iff.mp (heach p.val.val))

/-- In the two-reduced local overgroup, the normal join KR detects the vanishing commutator. -/
theorem commutator_eq_bot_of_noncentral_component
    {κ : GroupClass} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (A K R X : Subgroup G) [K.Normal] [(K ⊔ R).Normal] [Group.IsPerfect A]
    (hK : K.IsCComponent) (hn : ¬ fittingSubgroup K ≤ center K)
    (hAK : A ≤ K) (hA : ¬ Group.IsSolvable A)
    (hR : IsPGroup 2 R) (hXR : X ≤ normalizer (R : Set G))
    (hc : ⁅R,A⁆ ≤ A.pCoreIn 2) : ⁅R,X⁆ = ⊥ := by
  let J := K ⊔ R
  let B := K.subgroupOf J
  let F := (fittingSubgroup K).map K.subtype
  let : F.Normal := ConjAct.normal_of_characteristic_of_normal
  have hFK : F ≤ K := map_subtype_le _
  have hFJ : F ≤ J := hFK.trans le_sup_left
  have hC : K ⊓ centralizer (F : Set G) ≤ F := by
    rintro x ⟨hxK,hxC⟩
    have hk : (⟨x,hxK⟩ : K) ∈ centralizer (fittingSubgroup K : Set K) := by
      intro y hy
      exact Subtype.ext (hxC y (mem_map_of_mem K.subtype hy))
    rw [← ChapterA.Section03.NoncentralFitting.generalizedFitting_eq_fitting hK hn] at hk
    refine ⟨⟨x,hxK⟩,?_,rfl⟩
    rw [← ChapterA.Section03.NoncentralFitting.generalizedFitting_eq_fitting hK hn]
    exact centralizer_generalizedFitting_le K hk
  have hq : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    (R.subgroupOf J) hR.comap_subtype (by
      rw [← subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),
        subgroupOf_self])
  have hcB : B ⊓ centralizer (F.subgroupOf J : Set J) ≤ F.subgroupOf J := by
    rintro x ⟨hxK,hxC⟩
    apply hC
    refine ⟨hxK,?_⟩
    intro y hy
    exact congrArg Subtype.val (hxC ⟨y,hFJ hy⟩ hy)
  have hcomm := commutator_centralizes_canonical_fitting hG hO A K R X hK hn hAK hA hR hXR hc
  have hCR : ⁅R,X⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hXR
  have hCJ : ⁅R,X⁆ ≤ J := hCR.trans le_sup_right
  have hh := two_subgroup_le_core_of_controlled_centralizer B (F.subgroupOf J)
    ((⁅R,X⁆).subgroupOf J) hq hcB (hR.to_le hCR).comap_subtype (by
      intro x hx y hy
      exact Subtype.ext (hcomm hx y hy))
  have hm := map_mono (f := J.subtype) hh
  rw [map_subgroupOf_eq_of_le hCJ] at hm
  have hcore : (pCore 2 J).map J.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map J.subtype⟩
  exact bot_unique ((hm.trans hcore).trans_eq hO)

/-- The literal ambient two-core quotient gives the commutator bound without an action callback. -/
theorem commutator_le_core_of_noncentral_component
    {κ : GroupClass} (hG : IsSQTK κ G)
    (A K R X : Subgroup G) [K.Normal] [(K ⊔ R).Normal] [Group.IsPerfect A]
    (hK : K.IsCComponent)
    (hn : ¬ fittingSubgroup (K ⧸ pCore 2 K) ≤ center (K ⧸ pCore 2 K))
    (hAK : A ≤ K) (hA : ¬ Group.IsSolvable A)
    (hR : IsPGroup 2 R) (hXR : X ≤ normalizer (R : Set G))
    (hc : ⁅R,A⁆ ≤ A.pCoreIn 2) : ⁅R,X⁆ ≤ pCore 2 G := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let B := K.map q
  let e : (K ⧸ pCore 2 K) ≃* B := coreQuotientEquivImage 2 K
  have hBnc : ¬ fittingSubgroup B ≤ center B := by
    intro hz
    apply hn
    intro z hzF
    have hez : e z ∈ center B := hz (by
      rw [← map_fitting_equiv e]
      exact mem_map_of_mem e.toMonoidHom hzF)
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hez (e y)
  have hQ : IsSQTK κ Q := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let : B.Normal := Normal.map inferInstance q hq
  let : (B ⊔ R.map q).Normal := by
    change (K.map q ⊔ R.map q).Normal
    rw [← Subgroup.map_sup]
    exact Normal.map inferInstance q hq
  let : Group.IsPerfect (A.map q) := Group.IsPerfect.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hAbar : ¬ Group.IsSolvable (A.map q) := by
    intro hs
    let := hs
    let u := q.subgroupMap A
    have hu : IsPGroup 2 u.ker := by
      rw [ker_subgroupMap]
      exact hker.comap_subtype
    let : Group.IsNilpotent u.ker := hu.isNilpotent
    exact hA (Group.isSolvable_of_ker_le_range u.ker.subtype u (by rw [range_subtype]))
  have hcbar : ⁅R.map q,A.map q⁆ ≤ (A.map q).pCoreIn 2 := by
    rw [← map_commutator,← map_pCoreIn_of_ker_isPGroup q hker A]
    exact map_mono hc
  have he := commutator_eq_bot_of_noncentral_component hQ
    (pCore_quotient_pCore_eq_bot 2) (A.map q) B (R.map q) (X.map q)
    (hK.map_quotient (pCore 2 G)) hBnc (map_mono hAK) hAbar (hR.map q)
    ((map_mono hXR).trans (R.le_normalizer_map q)) hcbar
  have hh : ⁅R,X⁆ ≤ q.ker := (Subgroup.map_eq_bot_iff (⁅R,X⁆)).mp (by
    rw [map_commutator]
    exact he)
  simpa only [q,QuotientGroup.ker_mk'] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
