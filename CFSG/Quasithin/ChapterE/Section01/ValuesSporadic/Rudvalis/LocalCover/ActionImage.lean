module
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalModels
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank

/-!
# The actual Rudvalis local action images in two-extensions

For a subgroup normalized by a two-group, its join acts on its intrinsic
 two-core quotient. Centerlessness identifies the action kernel with the
 two-core of the join. For the max4 model the inner PSL₃(2) is simple and
 faithful, with index two in its automorphism group. For the max6 model,
 completeness of S₅ identifies the action image with S₅ and supplies its
 faithful normal A₅. Pullback through the literal quotient equivalence
 retains normality, centralizer vanishing and the two-group quotient.

The two concrete quotient identifications remain the explicit input
 `LocalQuotientModels`; no outer automorphism assertion about Ru is used.
 Source: Aschbacher–Smith E.1.14(5), printed p.214, citing Asc82a, Lemma 4.9;
 GLS3 Table 5.3r, printed p.279. These results feed `Rudvalis.LocalCover`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Rudvalis.LocalCover

private theorem not_commutative_of_center_bot {A : Type*} [Group A] [Nontrivial A]
    (hc : center A = ⊥) : ¬ IsMulCommutative A := by
  intro ha
  have ht := center_eq_top_iff.mpr ha
  rw [hc] at ht
  exact bot_ne_top ht

private theorem not_commutative_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hb : ¬ IsMulCommutative B) : ¬ IsMulCommutative A := by
  intro ha
  apply hb
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.symm.injective
  simpa only [map_mul] using (isMulCommutative_iff.mp ha) (e.symm x) (e.symm y)

/-- Pull back a faithful simple normal subgroup along a faithful action whose
image contains it. Normality and the quotient are in the actual acting group. -/
private theorem faithfulSimple_pullback {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (N : Subgroup B) [N.Normal]
    [IsSimpleGroup N] (ha : ¬ IsMulCommutative N)
    (hC : centralizer (N : Set B) = ⊥) (hq : IsPGroup 2 (B ⧸ N))
    (hN : N ≤ f.range) :
    ∃ L : Subgroup A, IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      centralizer (L : Set A) = ⊥ ∧ HasTwoGroupQuotient L := by
  let L := N.comap f
  let e : L ≃* N := (equivMapOfInjective L f hf).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hN))
  let : IsSimpleGroup L := e.isSimpleGroup
  refine ⟨L, inferInstance, not_commutative_equiv e ha, ?_, inferInstance, ?_⟩
  · apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply hf
    rw [map_one]
    apply mem_bot.mp
    rw [← hC]
    apply mem_centralizer_iff.mpr
    intro n hn
    obtain ⟨y, hy⟩ := hN hn
    have hyL : y ∈ L := by change f y ∈ N; rwa [hy]
    have hh := congrArg f ((mem_centralizer_iff.mp hx) y hyL)
    simpa only [map_mul, hy] using hh
  · let q := QuotientGroup.map L N f le_rfl
    apply hq.of_injective q
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_map]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])

private theorem psl_inner_quotient : IsPGroup 2 (MulAut.Outer Matrix.PSL3Two.PSL) := by
  let e : Matrix.PSL3Two.PSL ≃* MulAut.innerSubgroup Matrix.PSL3Two.PSL :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot)
  have hc : Nat.card (MulAut.innerSubgroup Matrix.PSL3Two.PSL) = 168 :=
    (Nat.card_congr e.toEquiv).symm.trans Matrix.PSL3Two.card_PSL
  have h := (MulAut.innerSubgroup Matrix.PSL3Two.PSL).card_mul_index
  rw [hc, Matrix.PSL3Two.Automorphisms.card_aut] at h
  apply IsPGroup.of_card (n := 1)
  change (MulAut.innerSubgroup Matrix.PSL3Two.PSL).index = 2 ^ 1
  omega

private theorem psl_action_image (J : Subgroup (MulAut Matrix.PSL3Two.PSL))
    (hJ : MulAut.innerSubgroup Matrix.PSL3Two.PSL ≤ J) :
    ∃ L : Subgroup J, IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      centralizer (L : Set J) = ⊥ ∧ HasTwoGroupQuotient L := by
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  let e : Matrix.PSL3Two.PSL ≃* MulAut.innerSubgroup Matrix.PSL3Two.PSL :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot)
  let : IsSimpleGroup (MulAut.innerSubgroup Matrix.PSL3Two.PSL) := e.symm.isSimpleGroup
  exact faithfulSimple_pullback J.subtype J.subtype_injective _
    (not_commutative_equiv e.symm
      (not_commutative_of_center_bot Matrix.PSL3Two.Automorphisms.center_psl_eq_bot))
    (MulAut.centralizer_innerSubgroup_eq_bot
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot) psl_inner_quotient
    (by rwa [range_subtype])

private theorem alternating_center : center (alternatingGroup (Fin 5)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (alternatingGroup (Fin 5)))
      inferInstance with h | h
  · exact h
  · have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp (center_eq_top_iff.mp h)
    norm_num at hh

private theorem symmetric_conj_surjective :
    Function.Surjective (MulAut.conj : Equiv.Perm (Fin 5) →* MulAut (Equiv.Perm (Fin 5))) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let e := Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv
  intro α
  obtain ⟨g, hg⟩ := MulAut.automorphismTower_inner_of_isSimpleGroup alternating_center
    (MulAut.congr e α)
  refine ⟨e.symm g, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hg]
  ext x
  simp [MulAut.congr_apply]

private noncomputable def symmetricConjEquiv :
    Equiv.Perm (Fin 5) ≃* MulAut (Equiv.Perm (Fin 5)) :=
  MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot
      Theory.SpecificGroups.SymmetricFive.center_eq_bot, symmetric_conj_surjective⟩

private theorem symmetric_action_image (J : Subgroup (MulAut (Equiv.Perm (Fin 5))))
    (hJ : MulAut.innerSubgroup (Equiv.Perm (Fin 5)) ≤ J) :
    ∃ L : Subgroup J, IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      centralizer (L : Set J) = ⊥ ∧ HasTwoGroupQuotient L := by
  have htop : J = ⊤ := by
    apply top_unique
    rw [← MonoidHom.range_eq_top.mpr symmetric_conj_surjective]
    exact hJ
  let e : J ≃* Equiv.Perm (Fin 5) :=
    (MulEquiv.subgroupCongr htop).trans (topEquiv.trans symmetricConjEquiv.symm)
  let N := alternatingGroup (Fin 5)
  let : IsSimpleGroup N := alternatingGroup.isSimpleGroup (by simp)
  have hn : ¬ IsMulCommutative N := not_commutative_of_center_bot alternating_center
  have hq : IsPGroup 2 (Equiv.Perm (Fin 5) ⧸ N) := by
    apply IsPGroup.of_card (n := 1)
    exact alternatingGroup.index_eq_two
  have hc : centralizer (N : Set (Equiv.Perm (Fin 5))) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient N hn hq
      Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot
  exact faithfulSimple_pullback e.toMonoidHom e.injective N hn hc hq
    (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)

private theorem local_quotient_of_action {G M : Type*} [Group G] [Finite G]
    [Group M] [Finite M] {K U : Subgroup G}
    (hUK : U ≤ normalizer (K : Set G)) (hU : IsPGroup 2 U)
    (e : (K ⧸ pCore 2 K) ≃* M) (hc : center M = ⊥)
    (hr : primeRank 2 (MulAut M) ≤ 2)
    (hstruct : ∀ J : Subgroup (MulAut M), MulAut.innerSubgroup M ≤ J →
      ∃ N : Subgroup J, IsSimpleGroup N ∧ ¬ IsMulCommutative N ∧
        centralizer (N : Set J) = ⊥ ∧ HasTwoGroupQuotient N) :
    HasRankTwoLocalQuotient (K ⊔ U : Subgroup G) := by
  have hcK : center (K ⧸ pCore 2 K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    have hx' := (centerCongr e ⟨x, hx⟩).property
    exact mem_bot.mp (hc.le hx')
  let a := pCoreJoinAction 2 hUK
  let J := a.range.map (MulAut.congr e).toMonoidHom
  have hJ : MulAut.innerSubgroup M ≤ J := by
    rw [← MulAut.map_innerSubgroup_congr e]
    exact map_mono (inner_le_pCoreJoinAction_range 2 hUK)
  let f : ((K ⊔ U : Subgroup G) ⧸ pCore 2 (K ⊔ U : Subgroup G)) ≃* J :=
    (pCoreJoinQuotientEquivRange 2 hUK hU hcK).trans
      ((MulAut.congr e).subgroupMap a.range)
  obtain ⟨N, hs, hn, hC, hN, hq⟩ := hstruct J hJ
  let := hs
  let := hN
  refine ⟨?_, faithfulSimple_pullback f.toMonoidHom f.injective N hn hC hq ?_⟩
  · exact (primeRank_equiv 2 f).le.trans
      ((primeRank_le_of_injective 2 J.subtype J.subtype_injective).trans hr)
  · rw [MonoidHom.range_eq_top.mpr f.surjective]
    exact le_top

/-- A normal copy of the max4 local, supplemented by any two-subgroup, has
 the required faithful simple subgroup in its literal two-core quotient. -/
theorem hasRankTwoLocalQuotient_join_max4 {G : Type*} [Group G] [Finite G]
    (hmodels : LocalQuotientModels) {K U : Subgroup G}
    (hUK : U ≤ normalizer (K : Set G)) (hU : IsPGroup 2 U)
    (e : K ≃* _root_.Rudvalis.SylowOvergroups.max4) :
    HasRankTwoLocalQuotient (K ⊔ U : Subgroup G) := by
  obtain ⟨q⟩ := hmodels.1
  let f := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans q
  exact local_quotient_of_action hUK hU f
    Matrix.PSL3Two.Automorphisms.center_psl_eq_bot
    (Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)).le
    psl_action_image

/-- The max6 local gives a faithful normal A₅, with two-group quotient,
 after adjoining any normalizing two-subgroup. -/
theorem hasRankTwoLocalQuotient_join_max6 {G : Type*} [Group G] [Finite G]
    (hmodels : LocalQuotientModels) {K U : Subgroup G}
    (hUK : U ≤ normalizer (K : Set G)) (hU : IsPGroup 2 U)
    (e : K ≃* _root_.Rudvalis.SylowOvergroups.max6) :
    HasRankTwoLocalQuotient (K ⊔ U : Subgroup G) := by
  obtain ⟨q⟩ := hmodels.2
  let f := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans q
  exact local_quotient_of_action hUK hU f
    Theory.SpecificGroups.SymmetricFive.center_eq_bot
    Theory.SpecificGroups.SymmetricFive.automorphism_primeRank_two_le
    symmetric_action_image

end CFSG.Quasithin.ChapterE.Rudvalis.LocalCover
