module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalization
public import Theory.GroupAction.ComponentRankAction.OuterTwo
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationLinear
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognitionComplete

/-!
# Established Cartan-container cases for the original old residual

A centerless quasisimple containing quotient with two-group outer
automorphisms gives Cartan normalization in every possible three-rank.
The existing small-image theorem handles rank one. In rank two, the
component is the entire cubic-generated subgroup after the ambient two-core
quotient. The original cubic Cartan is therefore absorbed into the component,
contradicting its marked intersection of order three.

The final source consumer also applies the projective-three normalization
proof and the original A₅ residual recognition theorem. It retains a proper
normal containing component only when its quotient lies outside both these
established families. No residual-model premise or Cartan-normalization
callback is used. The remaining A.3.14/A.3.18 model sieve and the odd-core
and unitary-five branches are not asserted by this reduction.

Source: Aschbacher--Smith, Proposition 9.3.1, second reduction, printed
p.732 of the combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalization

private theorem cubic_le_rank_two_component
    {X : Type*} [Group X] [Finite X] (J A : Subgroup X)
    (hJ : J.IsCComponent) [J.Normal] (hA : IsPGroup 3 A)
    (hX : primeRank 3 X ≤ 2)
    [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : center (J ⧸ pCore 2 J) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)))
    (hr : 2 ≤ primeRank 3 J) : A ≤ J := by
  let := pCore_isNilpotent (p := 2) (G := X)
  let q := QuotientGroup.mk' (pCore 2 X)
  let I := J.map q
  let e : (J ⧸ pCore 2 J) ≃* I := cComponentTwoCoreQuotientEquiv hJ
  let : IsQuasisimple I := IsQuasisimple.of_mulEquiv e
  have hI : IsComponent (X ⧸ pCore 2 X) I :=
    ⟨(hJ.map_quotient (pCore 2 X)).subnormal,inferInstance⟩
  have hzI : center I = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [←Nat.card_congr (centerCongr e).toEquiv,hz,card_bot]
  have hrI : 2 ≤ primeRank 3 I := by
    rw [←primeRank_congr 3 e,
      primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hr
  have hbar : primeRank 3 (X ⧸ pCore 2 X) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hX
  have hoI : IsPGroup 2 (MulAut.Outer I) := ho.of_equiv (MulAut.outerCongr e)
  let ec : I ⧸ center I ≃* I :=
    (QuotientGroup.quotientMulEquivOfEq hzI).trans QuotientGroup.quotientBot
  have hclosure := (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup hI
      (by rw [hzI]; simp) hrI hbar ec (by decide) hoI).2
  have hAI : A.map q ≤ I := by
    rw [hclosure]
    intro x hx
    obtain ⟨n,hn⟩ := (hA.map q) ⟨x,hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  have hAJQ : A ≤ J ⊔ pCore 2 X := by
    simpa only [I,q,comap_map_eq,QuotientGroup.ker_mk'] using map_le_iff_le_comap.mp hAI
  let r := QuotientGroup.mk' J
  have hAr : A.map r ≤ (pCore 2 X).map r := by
    have hh := map_mono (f := r) hAJQ
    simpa only [r,Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq] using hh
  have hb : A.map r = ⊥ := disjoint_self.mp
    ((hA.map r).disjoint_of_coprime (((pCore_isPGroup (p := 2) (G := X)).map r).to_le hAr)
      (by decide))
  simpa only [r,QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp hb

end CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalization

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- A normal original container with centerless quasisimple quotient and
two-group outer automorphisms normalizes the literal old residual. -/
theorem cartan_normalizes_old_residual_of_centerless_outer_two_container
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hJC : J ≤ centralizer (m.tensorLine : Set G))
    [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : center (J ⧸ pCore 2 J) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J))) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  by_cases hr : primeRank 3 J ≤ 1
  · exact m.cartan_normalizes_old_residual_of_rank_one hH eK A B J
      hJU hJ hKJ (hBC ▸ inf_le_left) hBK hB3 hAU hr hz ho
  let N := normalizer (m.tensorLine : Set G)
  let I := J.subgroupOf N
  let d : I ≃* J := subgroupOfEquivOfLe hJU
  let dq : (I ⧸ pCore 2 I) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let : IsQuasisimple (I ⧸ pCore 2 I) := IsQuasisimple.of_mulEquiv dq.symm
  have hzI : center (I ⧸ pCore 2 I) = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [Nat.card_congr (centerCongr dq).toEquiv,hz,card_bot]
  have hoI := ho.of_equiv (MulAut.outerCongr dq).symm
  have hrI : 2 ≤ primeRank 3 I := by
    rw [primeRank_congr 3 d]
    omega
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  let := hnJ
  have hAI : A.subgroupOf N ≤ I :=
    SourceOldResidualCartanNormalization.cubic_le_rank_two_component I (A.subgroupOf N)
      hJ (IsElementaryAbelian.isPGroup 3 A).comap_subtype
      (hN.stronglyQuasithin 3 (by decide) (by decide)) hzI hoI hrI
  have hAJ : A ≤ J := by
    intro a ha
    exact hAI (show (⟨a,hAU ha⟩ : N) ∈ A.subgroupOf N from ha)
  have hBA : B = A := hBC.trans (inf_eq_left.mpr (hAJ.trans hJC))
  rw [hBA,hA9] at hB3
  omega

/-- The actual nonzero-core source inputs construct either Cartan normalization
or a proper container outside the established outer-two and PSL₃(4) cases.
The original A₅ quotient is supplied by source residual recognition. -/
theorem nonzero_core_cartan_normalization_remaining_cases
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      ¬ (IsQuasisimple (J ⧸ pCore 2 J) ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
        IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J))) ∧
      ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 := by
  by_cases hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)
  · exact Or.inl hAK
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  obtain ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,_⟩ :=
    (m.nonzero_core_cartan_normalization_reduction hH eK A B
      hAB hA9 hAe hB3 hBK hBC hcore).resolve_left hAK
  let := hAe
  refine Or.inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,?_,?_⟩
  · rintro ⟨hq,hz,ho⟩
    let := hq
    exact hAK (m.cartan_normalizes_old_residual_of_centerless_outer_two_container hH eK
      A B J hA9 hB3 (hAB.trans m.borel_normalizes_tensorLine) hBK hBC
      hJU hJ hnJ hKJ.le hJC hz ho)
  · rintro ⟨F,_,_,hF,⟨eJ⟩⟩
    exact hAK (m.cartan_normalizes_old_residual_of_projective_three_container
      hH eK A J hAB hJU hJ hnJ hKJ hF eJ)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

