module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionThreeModels
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.NormalQuotientActionSylowSupplement

/-!
# The binary centralizer obstruction in the chosen-seed argument

Two disjoint binary planes give commuting cubic elements in SL₄(2), one
inverted and one fixed by a specified involution. The same configuration
embeds in every larger binary special linear group. Applied to the actual
surjection from the normalizer, A.1.31 bounds the centralizer of the inverted
pair by three-rank one. The second cubic already uses that rank, so the
full component centralizer has order prime to three. This retains the rank
bound on the source of the surjection; arbitrary quotients need not preserve it.

If the centralizer order divides 36, it is consequently a normal two-group.
The trivial two-core kills it, and the binary outer two-group makes the
component and the original Sylow subgroup generate the whole action image.
The literal Chapter12 application is SeedAlternativesMovedExhaustionBinaryCentralizer.
Multiplicity two and its centralizer embedding remain with qt-baumann-fsu.

Source: Aschbacher--Smith D.3.9(1), printed p.200, and A.1.31(1), pp.27--28,
used by D.3.13 and 3.2.5, pp.202,580--581; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {P H : Type*} [Group P] [Finite P] [Group H] [Finite H]

private theorem centralizer_three_free_of_inverted_pair
    (f : P →* H) (hf : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (K : Subgroup H) (hz : center K = ⊥)
    (a b t : K) (ha : orderOf a = 3) (hb : orderOf b = 3) (ht : orderOf t = 2)
    (hi : t * a * t⁻¹ = a⁻¹) (hab : Commute a b) (htb : Commute t b) :
    ¬ 3 ∣ Nat.card (centralizer (K : Set H)) := by
  let J := zpowers (a : H)
  let K₀ := J ⊔ zpowers (t : H)
  let B := zpowers (b : H)
  let C := centralizer (K : Set H)
  have ha' : orderOf (a : H) = 3 := (orderOf_coe a).trans ha
  have hb' : orderOf (b : H) = 3 := (orderOf_coe b).trans hb
  have ht' : orderOf (t : H) = 2 := (orderOf_coe t).trans ht
  have hi' : (t : H) * a * (t : H)⁻¹ = (a : H)⁻¹ := congrArg Subtype.val hi
  have hJ : IsPGroup 3 J := IsPGroup.of_card (n := 1) (by
    simpa only [J,Nat.card_zpowers,pow_one] using ha')
  have htn : (t : H) ∈ normalizer (J : Set H) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers ((t : H) * a * (t : H)⁻¹) = J
    rw [hi',zpowers_inv]
  have htc : (t : H) ∉ centralizer (J : Set H) := by
    intro hh
    have he : (a : H) = (a : H)⁻¹ := by
      calc
        (a : H) = (t : H) * a * (t : H)⁻¹ := by
          rw [←hh a (mem_zpowers (a : H)),mul_inv_cancel_right]
        _ = (a : H)⁻¹ := hi'
    have hs : (a : H)^2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun x => (a : H) * x) he).trans (mul_inv_cancel _)
    have hd := orderOf_dvd_of_pow_eq_one hs
    rw [ha'] at hd
    norm_num at hd
  have hr₀ := component_centralizer_three_rank_le_one_of_inverted_subgroup
    f hf hr K₀ J le_sup_left hJ t ((show zpowers (t : H) ≤ K₀ from le_sup_right) (mem_zpowers (t : H))) ht' htn htc
  have hK₀ : K₀ ≤ K := sup_le (zpowers_le.mpr a.property) (zpowers_le.mpr t.property)
  have hBC : B ≤ centralizer (K₀ : Set H) := by
    apply le_centralizer_iff.mpr
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_iff]
      rintro x ⟨n,rfl⟩
      exact ((hab.map K.subtype).symm.zpow_left n).eq
    · rw [mem_centralizer_iff]
      rintro x ⟨n,rfl⟩
      exact ((htb.map K.subtype).symm.zpow_left n).eq
  have hCC : C ≤ centralizer (K₀ : Set H) := centralizer_le hK₀
  have hBK : B ≤ K := zpowers_le.mpr b.property
  have hdis : Disjoint B C := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hx,hc⟩
    have hh : (⟨x,hBK hx⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (hc k k.property)
    rw [hz,mem_bot] at hh
    exact congrArg Subtype.val hh
  have he := B.primeRank_sup_eq_add_of_disjoint_commuting C hdis
    (hBK.trans (le_centralizer_iff.mp le_rfl)) 3
  have hh := (primeRank_mono 3 (sup_le hBC hCC)).trans hr₀
  have hbpos : primeRank 3 B ≠ 0 := by
    intro he
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp he (by
      change 3 ∣ Nat.card (zpowers (b : H))
      rw [Nat.card_zpowers,hb'])
  apply PrimeRank.eq_zero_iff_not_dvd_card.mp
  change primeRank 3 C = 0
  omega

private def cubicFour : SL(4,ZMod 2) :=
  ⟨!![0,1,0,0;1,1,0,0;0,0,1,0;0,0,0,1],by decide⟩
private def secondFour : SL(4,ZMod 2) :=
  ⟨!![1,0,0,0;0,1,0,0;0,0,0,1;0,0,1,1],by decide⟩
private def inverterFour : SL(4,ZMod 2) :=
  ⟨!![1,1,0,0;0,1,0,0;0,0,1,0;0,0,0,1],by decide⟩

private theorem four_pair :
    orderOf cubicFour = 3 ∧ orderOf secondFour = 3 ∧ orderOf inverterFour = 2 ∧
      inverterFour * cubicFour * inverterFour⁻¹ = cubicFour⁻¹ ∧
      Commute cubicFour secondFour ∧ Commute inverterFour secondFour := by
  refine ⟨orderOf_eq_prime (by decide : cubicFour^3=1) (by decide : cubicFour≠1),
    orderOf_eq_prime (by decide : secondFour^3=1) (by decide : secondFour≠1),
    orderOf_eq_prime (by decide : inverterFour^2=1) (by decide : inverterFour≠1),?_,?_,?_⟩
  · decide
  · unfold Commute SemiconjBy; decide
  · unfold Commute SemiconjBy; decide

private def extendFour (r : ℕ) : SL(4,ZMod 2) →* SL(4+r,ZMod 2) where
  toFun g := ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin r) (Fin r) (ZMod 2))),by
      rw [Matrix.det_reindex_self,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]
      exact g.property⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 1) = 1
    rw [Matrix.fromBlocks_one]
    exact (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv).map_one
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (g.val*h.val) 0 0 1) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.val 0 0 1) *
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks h.val 0 0 1)
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv]
    congr 1
    simp [Matrix.fromBlocks_multiply]

private theorem extendFour_injective (r : ℕ) : Function.Injective (extendFour r) := by
  intro g h he
  have hm := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective (congrArg Subtype.val he)
  apply Subtype.ext
  exact congrArg (fun M => M.submatrix Sum.inl Sum.inl) hm

/-- The actual centralizer of a binary linear component has order prime to
three, with the rank bound on the original cover. -/
theorem binary_component_centralizer_three_free
    (f : P →* H) (hf : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (K : Subgroup H) {d : ℕ} (hd : 4 ≤ d) (e : K ≃* SL(d,ZMod 2)) :
    ¬ 3 ∣ Nat.card (centralizer (K : Set H)) := by
  have hz : center K = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr e ⟨k,hk⟩).property
    change e k ∈ center SL(d,ZMod 2) at hh
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega),mem_bot] at hh
    exact e.injective (hh.trans e.map_one.symm)
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hd
  let j : SL(4,ZMod 2) →* K := e.symm.toMonoidHom.comp (extendFour r)
  have hj : Function.Injective j := e.symm.injective.comp (extendFour_injective r)
  obtain ⟨ha,hb,ht,hi,hab,htb⟩ := four_pair
  apply centralizer_three_free_of_inverted_pair f hf hr K hz
    (j cubicFour) (j secondFour) (j inverterFour)
    ((orderOf_injective j hj _).trans ha) ((orderOf_injective j hj _).trans hb)
    ((orderOf_injective j hj _).trans ht)
  · simpa only [map_mul,map_inv] using congrArg j hi
  · exact hab.map j
  · exact htb.map j

/-- The final binary centralizer step of D.3.9. The order bound is the
one supplied by two natural copies and two dual copies. -/
theorem binary_sylow_supplement_of_centralizer_card_dvd
    (f : P →* H) (hf : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (K : Subgroup H) [K.Normal] {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : K ≃* SL(d,ZMod 2)) (hcore : pCore 2 H = ⊥)
    (hcard : Nat.card (centralizer (K : Set H)) ∣ 36) (S : Sylow 2 H) :
    K ⊔ (S : Subgroup H) = ⊤ := by
  let C := centralizer (K : Set H)
  have h3 := binary_component_centralizer_three_free f hf hr K (by omega) e
  have hcop : (Nat.card C).Coprime 9 :=
    ((Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm.pow_right 2)
  have hCtwo : IsPGroup 2 C := IsPGroup.of_card_dvd_pow (n := 2)
    (hcop.dvd_of_dvd_mul_right (show Nat.card C ∣ 4 * 9 from hcard))
  have hC : C = ⊥ := bot_unique
    ((show C ≤ pCore 2 H from le_sSup ⟨inferInstance,hCtwo⟩).trans hcore.le)
  have hout : IsPGroup 2 (MulAut.Outer K) :=
    (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup hd).of_equiv (MulAut.outerCongr e).symm
  have hquot : IsPGroup 2 (H ⧸ K) :=
    hout.of_injective (MulAut.outerAction K) (MulAut.outerAction_injective K hC)
  simpa only [sup_comm] using S.sup_eq_top_of_quotient_isPGroup K hquot

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
