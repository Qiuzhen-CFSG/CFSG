module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.TableComparison
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.SourceFF
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks

/-!
# Excluding the projective cubic actor in the ordinary-root argument

A centerless quasisimple faithful FF actor has a faithful irreducible section:
a nontrivial perfect action survives on a section, whose central kernel is
trivial, and fixed codimension cannot increase. On that same section, the
proved linear and unitary recognition theorems exclude the signed projective
three-dimensional families at their diagonal congruences. In odd characteristic,
the defining-prime rank forces field exponent one. In characteristic two,
the linear recognition retains the original field degree and would give a
nontrivial cubic center; unitary recognition has ratio two.

Apply this to the original K_Z action and its literal W offender. The exact
A.3.18/star-to-action comparison already proved in CoreQuotient then excludes
the cubic exception. Every prime dividing the original Cartan order has rank
one in K_Z and at most one in its actual action image. The even-degree table
comparison consequently gives equality with the embedded J image, both
terminal subgroup conclusions, and the original root contradiction without
an extra classification or rank premise. Odd-degree table comparisons remain
with the ordinary-root assembly.

Source: Aschbacher–Smith 4.3.6, printed p.615; A.3.18, pp.51–53;
B.4.2, B.5.1 and B.5.6(1), pp.86,99–105; K.2 and K.3, pp.453–457.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open ChapterB.QuasisimpleSource
open Chapter1.Section02.LocalModels ChapterA.Section03.OddPrime.SourceModels

private theorem faithful_irreducible_ff_section
    {H X : Type*} [Group H] [Finite H] [IsQuasisimple H]
    [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (hz : center H = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      IsIrreducible N.quotientRepresentation ∧
      Function.Injective N.quotientRepresentation ∧ IsFFModule N.quotientRepresentation := by
  let : Group.IsPerfect (⊤ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup H) ≃* H).symm.toMonoidHom) topEquiv.symm.surjective
  have hn : ¬ (⊤ : Subgroup H) ≤ ρ.ker := by
    intro ht
    have hb := (MonoidHom.ker_eq_bot_iff ρ).mpr hf
    obtain ⟨A,hA⟩ := hff
    exact hA.1.1 (bot_unique ((le_top.trans ht).trans_eq hb))
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup H) hn
  have hk : N.quotientRepresentation.ker = ⊥ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top N.quotientRepresentation.ker with hk | ht
    · exact bot_unique (hk.trans_eq hz)
    · exact (hn ht.ge).elim
  refine ⟨U,N,hi,(MonoidHom.ker_eq_bot_iff _).mp hk,?_⟩
  obtain ⟨A,hA⟩ := hff
  refine ⟨A,hA.1,?_⟩
  have hu := fixedCodim_subrepresentation_le ρ U A
  have hn := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
  have ha := hA.2
  omega

private noncomputable def topCenterQuotientEquiv
    {H : Type*} [Group H] (hz : center H = ⊥) :
    ((⊤ : Subgroup H) ⧸ center (⊤ : Subgroup H)) ≃* H :=
  (ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.centralQuotientEquiv
    (topEquiv : (⊤ : Subgroup H) ≃* H)).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem no_signed_projective_irreducible_ff
    {H X : Type*} [Group H] [Finite H] [IsQuasisimple H]
    [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hz : center H = ⊥) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hff : IsFFModule ρ) (u : Bool) (q : ℕ) (hq : SignedCongruence u q)
    (hm : IsPSLSign H u 3 q) : False := by
  let : IsSimpleGroup (H ⧸ center H) := IsQuasisimple.simple
  let : Nontrivial H := (QuotientGroup.mk'_surjective (center H)).nontrivial
  let : IsQuasisimple (⊤ : Subgroup H) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hiTop : IsIrreducible (ρ.comp (⊤ : Subgroup H).subtype) :=
    (irreducible_comp_surjective_iff _ (topEquiv : (⊤ : Subgroup H) ≃* H).surjective ρ).mpr hi
  have hfit : generalizedFitting H = ⊤ := generalizedFitting_eq_top_of_quasisimple
  have hs := ChapterB.SourceClassification.source_hypotheses hsq hfit inferInstance hf hiTop hff
  cases u with
  | false =>
    change ClassicalGroup.IsPSL H 3 q at hm
    change q % 3 = 1 at hq
    have hmTop := hm.of_mulEquiv (topCenterQuotientEquiv hz)
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hpow : IsPrimePow q := by
      rw [←hcard,Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card F
    obtain ⟨p,r,hp,hr,hpr⟩ := (isPrimePow_nat_iff q).mp hpow
    have hcard' : Nat.card F = p^r := hcard.trans hpr.symm
    let : Fact p.Prime := ⟨hp⟩
    let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := r) (by
      simpa only [←Nat.card_eq_fintype_card] using hcard')
    by_cases hp2 : p = 2
    · subst p
      obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
      obtain ⟨B,hB,⟨a⟩,_⟩ := ChapterK.Linear.SourceFF.source_of_bestOffender ρ
        hsq hfit.symm inferInstance hf hiTop r hr (hpr ▸ hmTop) A hA
      have hzB : center SL(3,B.Carrier) = ⊥ := by
        apply (eq_bot_iff_card _).mpr
        rw [← Nat.card_congr (centerCongr
          ((topEquiv : (⊤ : Subgroup H) ≃* H).symm.trans a.groupEquiv)).toEquiv,hz]
        simp
      have hnot := (Matrix.SL3.center_eq_bot_iff_card_mod_three B.Carrier).mp hzB
      apply hnot
      rw [B.card_eq,hB,hpr]
      exact hq
    · have hbound : primeRank p PSL(3,F) ≤ 2 := by
        rw [←primeRank_congr p e]
        exact hsq.stronglyQuasithin p hp (hp.odd_of_ne_two hp2)
      have hr1 := ChapterA.Section02.psl3_fieldExponent_eq_one hcard' hr hbound
      have hpq : p = q := by simpa [hr1] using hpr
      exact ChapterB.SourceClassification.not_ff_odd_psl3 hs hp
        (hp.odd_of_ne_two hp2) (hpq ▸ hmTop) hff
  | true =>
    change ClassicalGroup.IsPSU H 3 q at hm
    change q % 3 = 2 at hq
    have hmTop := hm.of_mulEquiv (topCenterQuotientEquiv hz)
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hpow2 : IsPrimePow (q^2) := by
      rw [←hcard,Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card F
    have hpow : IsPrimePow q := (isPrimePow_pow_iff (by decide : 2 ≠ 0)).mp hpow2
    obtain ⟨p,r,hp,hr,hpr⟩ := (isPrimePow_nat_iff q).mp hpow
    let : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst p
      by_cases hr1 : r = 1
      · have he : q = 2 := by simpa [hr1] using hpr.symm
        let : Group.IsSolvable (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
          BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable J
            (he ▸ hcard) (he ▸ hconj)
        exact Group.IsPerfect.not_isSolvable H (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
      · exact ChapterB.SourceClassification.not_ff_unitary hs (by omega : 2 ≤ r)
          (hpr ▸ hmTop) hff
    · have hbound : primeRank p (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
        rw [←primeRank_congr p e]
        exact hsq.stronglyQuasithin p hp (hp.odd_of_ne_two hp2)
      have hr1 := ChapterA.Section02.psu3_fieldExponent_eq_one J hp2
        (hpr ▸ hcard) hr (hpr ▸ hconj) hbound
      have hpq : p = q := by simpa [hr1] using hpr
      have hp3 := ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_unitaryRestriction
        ρ (⊤ : Subgroup H) ⟨hsq,hfit.symm,inferInstance,hf,hiTop⟩ hp
        (hp.odd_of_ne_two hp2) (hpq ▸ hmTop) hs.smallCubic
      omega

/-- A faithful binary FF action of a centerless SQTK quasisimple group excludes
both signed projective cubic families at their diagonal congruence. -/
theorem no_signed_projective_ff
    {H X : Type*} [Group H] [Finite H] [IsQuasisimple H]
    [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hz : center H = ⊥) (hf : Function.Injective ρ) (hff : IsFFModule ρ)
    (u : Bool) (q : ℕ) (hq : SignedCongruence u q) (hm : IsPSLSign H u 3 q) : False := by
  obtain ⟨U,N,hi,hfaith,hffN⟩ := faithful_irreducible_ff_section ρ hz hf hff
  exact no_signed_projective_irreducible_ff N.quotientRepresentation hsq hz hfaith hi hffN u q hq hm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- Exclude the actual projective cubic actor, using its original faithful action
and the whole marked module offender. -/
theorem not_high_three_rank (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) : ¬ 1 < primeRank 3 KZ := by
  intro hhigh
  let := hr.elementary
  let σ := (representation m hr).comp (image m KZ).subtype
  have hKN := hK.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hz,_,u,q,hq,hm⟩ := secondary_image_projective_of_high_three_rank m hn h hr hUN hcore
    KZ hK hJK hcomp hquasi hnormal hd hhigh
  let := secondary_image_quasisimple m hn hr hUN hcore KZ hKN hJK hquasi hnormal
  have hsq := secondary_image_sqtk m hn h hr hUN hcore KZ hKN hJK hquasi hnormal
  have hBK := image_mono m ((m.fullModule_le_second hn).trans hJK)
  have hff : IsFFModule σ := ⟨(image m c.ordinaryModule).subgroupOf (image m KZ),
    ((fullModule_isBestOffender m hn hr hUN hcore hQ).subgroupOf
      (representation m hr) hBK).isOffender _⟩
  have hf : Function.Injective σ :=
    (representation_injective m hr).comp (image m KZ).subtype_injective
  exact no_signed_projective_ff σ hsq hz hf hff u q hq hm


/-- All Cartan primes have rank one in the original secondary component.
The cubic diagonal exception is now discharged, with no classification callback. -/
theorem secondary_primeRank_eq_one (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p KZ = 1 := by
  by_cases hp3 : p = 3
  · subst p
    exact le_antisymm (Nat.le_of_not_gt
      (not_high_three_rank m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal hd))
      (one_le_secondary_primeRank m hn KZ hJK 3 hp hd)
  · exact primeRank_eq_one_of_ne_three m hn h KZ hK hJK hcomp hquasi hnormal p hp ho hd hp3

/-- The same Cartan bound on the actual action image. Odd-prime cyclic Sylows
justify passage through the original action projection. -/
theorem secondary_image_primeRank_le_one (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p (image m KZ) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p KZ := Classical.choice inferInstance
  have hb := (secondary_primeRank_eq_one m hn h hr hUN hcore hQ KZ hK hJK hcomp
    hquasi hnormal p hp ho hd).le
  have hKN := hK.trans (Subgroup.centralizer_le_normalizer _)
  exact P.primeRank_le_one_of_surjective (P.isCyclic_of_odd_of_primeRank_le_one ho hb)
    (secondaryProjection m KZ hKN) (secondaryProjection_surjective m KZ hKN)

/-- Even degree now gives equality of the two actual embedded action images
without an additional cubic-rank premise. -/
theorem image_eq_of_even (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    image m KZ = image m m.second := by
  apply image_eq_of_even_threeRank m hn he h hr hUN hcore hQ KZ
    (hK.trans (Subgroup.centralizer_le_normalizer _)) hJK hquasi hnormal
  exact secondary_image_primeRank_le_one m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
    3 Nat.prime_three (by decide) ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he)

/-- The even-degree branch establishes both literal terminal conclusions. -/
theorem module_and_containment_of_even (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore := by
  exact module_and_containment_of_image_eq m hn hr hUN hcore hseed hQ KZ
    (hK.trans (Subgroup.centralizer_le_normalizer _)) hKZ hquasi hnormal
    (image_eq_of_even m hn he h hr hUN hcore hQ KZ hK
      ((le_conjugateSpanBy _ _).trans_eq hKZ) hcomp hquasi hnormal)

/-- Apply the completed even-degree comparison to the original root contradiction. -/
theorem false_of_even
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) : False := by
  obtain ⟨hU,hle⟩ := module_and_containment_of_even m hn he h hr hUN hcore hseed hQ
    KZ hK hcomp hKZ hquasi hnormal
  exact c.ordinary_false_of_root_module D hn m KZ hT hseed hU hQ hKZ hle hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
