module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeFive
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportResidual
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.CanonicalRank

/-!
# Canonical five-factors and normality of the original point residual

The minimal large-prime reduction and its literal quotient action give a
normal elementary five-core with a four-dimensional canonical support.
The normal small-support subgroup is therefore the whole five-core by
minimality. Independence of the canonical factors and the original SQTK
five-rank bound limit this family to one or two members. Every two-perfect
actor fixes each factor and centralizes it, since Aut(C5) is a two-group.

In the original minimal local overgroup I, this applies to the actual L₁
image. The prime supplement and point parabolic generate I/O₂(I), so L₁'s
image is normal. Normality lifts through the literal two-core: it lies in
T, which already normalizes the two-perfect L₁. Thus L₁ is normal in I,
its actual quotient image has order three, and [U_I,L₁] = U_I. The final
application retains the original normal five-core lift, its exact quotient
kernel, the original reflection and its fixed complement.

This establishes the point-normality step of the five-core argument for
arbitrary original members of H_z. The full normal dihedral factor product
and the ambient five-core exclusion remain; no identification of I with
the full point normalizer or vanishing of its five-core is asserted.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, using D.2.12–13,
pp.183–185; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam
universe u

private theorem twoPerfect_centralizes_five
    {D : Type*} [Group D] [Finite D] (P C : Subgroup D)
    (hP : IsPPerfect 2 P) (hC : Nat.card C = 5)
    (hn : P ≤ normalizer (C : Set D)) : P ≤ centralizer (C : Set D) := by
  let : MulDistribMulAction P C := conjMulDistribMulActionOfLeNormalizer P C hn
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic C := isCyclic_of_prime_card hC
  have ha : IsPGroup 2 (MulAut C) := by
    apply IsPGroup.of_card (n := 2)
    rw [IsCyclic.card_mulAut,hC]
    decide
  have hh := hP.hom_eq_one_of_isPGroup ha (MulDistribMulAction.toMulAut P C)
  intro x hx c hc
  have he := congrArg (fun f : P →* MulAut C => (f ⟨x,hx⟩ ⟨c,hc⟩ : D)) hh
  change x * c * x⁻¹ = c at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A minimal five-core containing a four-dimensional canonical support is
exactly the product of its one or two canonical order-five factors.
Every two-perfect subgroup centralizes this whole core. -/
theorem minimal_five_core_canonical_structure
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (X : Subgroup D) (hcore : X = pCore 5 D) (hrank : primeRank 5 X ≤ 2)
    (hmin : ∀ N : Subgroup D, N.Normal → N ≤ X → N = ⊥ ∨ N = X)
    (R : Subgroup D) (hc : Nat.card (⁅X,R⁆ : Subgroup D) = 5)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅X,R⁆) = 4) :
    let := BinaryGroupAction.action ρ
    smallSupportGroup D (Multiplicative W) 2 = X ∧
      0 < Nat.card (smallSupportFactors D (Multiplicative W) 2) ∧
      Nat.card (smallSupportFactors D (Multiplicative W) 2) ≤ 2 ∧
      ∀ P : Subgroup D, IsPPerfect 2 P → P ≤ centralizer (X : Set D) := by
  classical
  let := BinaryGroupAction.action ρ
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul D (Multiplicative W) := BinaryGroupAction.faithful ρ hf
  let : X.Normal := hcore.symm ▸ inferInstance
  let C := smallSupportFactors D (Multiplicative W) 2
  let K := smallSupportGroup D (Multiplicative W) 2
  have hCX (N : Subgroup D) (hN : N ∈ C) : N ≤ X := by
    rw [hcore]
    exact IsPGroup.le_pCore_of_le_fitting (IsPGroup.of_card (n := 1) (by simpa using hN.2.1)) hN.1
  have hKX : K ≤ X := sSup_le hCX
  have hD : ⁅X,R⁆ ∈ C := by
    refine ⟨(commutator_le_left X R).trans (hcore.le.trans (pCore_le_fitting D 5)),hc,?_⟩
    rw [BinaryGroupAction.commutator_card,hd]
  have hKne : K ≠ ⊥ := by
    intro hz
    have he : ⁅X,R⁆ = ⊥ := bot_unique ((le_sSup hD).trans hz.le)
    rw [he,card_bot] at hc
    norm_num at hc
  have hgen : K = X := (hmin K inferInstance hKX).resolve_left hKne
  let : Fintype C := Fintype.ofFinite C
  have hbound : Nat.card C ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact (Chapter13.Section08.SolvableExclusion.Five.canonicalFive_count_le_subgroup_rank
      (fun N : C => N.val) (fun N => N.property) Subtype.val_injective X
      (fun N => hCX N N.property)).trans hrank
  refine ⟨hgen,?_,hbound,?_⟩
  · let : Nonempty C := ⟨⟨⁅X,R⁆,hD⟩⟩
    exact Nat.card_pos
  · intro P hP
    rw [←hgen]
    apply le_centralizer_iff.mpr
    apply sSup_le
    intro N hN
    apply le_centralizer_iff.mp
    exact twoPerfect_centralizes_five P N hP hN.2.1
      (smallSupportFactors_twoPerfect_normalizes hbound P hP N hN)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem local_point_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I) :
    (pResidual 2 ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I)).map
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).subtype = (F.Li L 1).subgroupOf I := by
  apply map_injective I.subtype_injective
  rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hBI,residual_group h structural,
    map_subgroupOf_eq_of_le (le_sup_left.trans hBI)]

/-- Normality of the point residual's literal image lifts in every actual
member of H_z, retaining its original two-core kernel. -/
theorem local_point_normal_of_star_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hn : (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).Normal) :
    ((F.Li L 1).subgroupOf I).Normal := by
  let A := (F.Li L 1).subgroupOf I
  let q := QuotientGroup.mk' (pCore 2 I)
  have hp : IsPPerfect 2 A := by
    rw [show A = (F.Li L 1).subgroupOf I from rfl,←local_point_residual h structural I hBI]
    exact isPPerfect_embedded_pResidual 2 _
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkn : q.ker ≤ normalizer (A : Set I) := by
    rw [QuotientGroup.ker_mk']
    apply le_trans (pCore_isPGroup.le_sylow_of_normal (T.subtype (le_sup_right.trans hBI)))
    change ((T : Subgroup G).subgroupOf I) ≤ normalizer ((F.Li L 1).subgroupOf I : Set I)
    rw [←subgroupOf_normalizer_eq (le_sup_left.trans hBI)]
    exact fun _ hx => T_normalizes_L₁ h structural hx
  have he := comap_normalizer_map_of_pPerfect q A hp hk hkn
  let : (A.map q).Normal := hn
  rw [normalizer_eq_top,comap_top] at he
  exact normalizer_eq_top_iff.mp he.symm

/-- Centralization of the minimal prime supplement makes the original point
residual normal in its full local overgroup, not only in the quotient. -/
theorem local_point_normal_of_centralized_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (X : Subgroup (HStar I))
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤)
    (hc : ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
      centralizer (X : Set (HStar I))) : ((F.Li L 1).subgroupOf I).Normal := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let A := (F.Li L 1).subgroupOf I
  let q := QuotientGroup.mk' (pCore 2 I)
  have hnB : B ≤ normalizer (F.Li L 1 : Set G) :=
    sup_le (F.Li L 1).le_normalizer (T_normalizes_L₁ h structural)
  have hn : B.subgroupOf I ≤ normalizer (A : Set I) := by
    rw [←subgroupOf_normalizer_eq (le_sup_left.trans hBI)]
    exact fun _ hx => hnB hx
  apply local_point_normal_of_star_normal h structural I hBI
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  exact sup_le ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
    ((map_mono hn).trans (le_normalizer_map q))

/-- Relative normality identifies the literal point image with its cubic
quotient in any original local overgroup. -/
theorem local_point_star_card_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal) :
    Nat.card (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 3 := by
  let A := (F.Li L 1).subgroupOf I
  let := hn
  let e := (subgroupOfEquivOfLe hLI).symm
  let E := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (coreQuotientEquivImage 2 A)
  exact (Nat.card_congr E.toEquiv).symm.trans (pointResidual_core_quotient_card h structural)

/-- A nontrivial five-core in any original local overgroup yields a minimal
normal lift with normal point residual. The canonical factors belong to the
same literal quotient action, and no point-normality premise is added. -/
theorem local_minimal_five_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X.Normal ∧ IsElementaryAbelian 5 X ∧ X = pCore 5 (HStar I) ∧
      (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      (∀ N : Subgroup (HStar I), N.Normal → N ≤ X → N = ⊥ ∨ N = X) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      Nat.card (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 3 ∧
      ⁅F.UH I,F.Li L 1⁆ = F.UH I ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          ∃ (A : Subgroup I) (R : Subgroup (HStar I)),
            A ≤ (F.Ri L 1).subgroupOf I ∧
            IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
            A.map (QuotientGroup.mk' (pCore 2 I)) ⊓ centralizer (X : Set (HStar I)) = ⊥ ∧
            R ≤ X ⊔ A.map (QuotientGroup.mk' (pCore 2 I)) ∧
            IsElementaryTwo R ∧ Nat.card R = 2 ∧
            IsCubic a.representation R ∧ fixedCodim a.representation R = 2 ∧
            Nat.card (⁅X,R⁆ : Subgroup (HStar I)) = 5 ∧
            Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⁅X,R⁆) = 4 ∧
            IsCompl (subspaceCommutator a.representation ⊤ ⁅X,R⁆)
              (fixedSpace a.representation (⁅X,R⁆ ⊔ R)) ∧
          let := BinaryGroupAction.action a.representation
          smallSupportGroup (HStar I)
            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2 = X ∧
          0 < Nat.card (smallSupportFactors (HStar I)
            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ∧
          Nat.card (smallSupportFactors (HStar I)
            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≤ 2 ∧
          ∀ P : Subgroup (HStar I), IsPPerfect 2 P → P ≤ centralizer (X : Set (HStar I)) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,hcub,hfixed,
      hcomm,hmove,hcompl⟩ := local_minimal_five_reflection h hab structural previous J hJ hne
  let := hXn
  let := hXp
  let := hU
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hrI : primeRank 5 I ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 5 (inclusion hI.2.1) (inclusion_injective hI.2.1)).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 5 Nat.prime_five (by decide))
  have hrX : primeRank 5 X ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 5 X.subtype X.subtype_injective).trans
      ((primeRank_quotient_le_of_isTwoGroup 5 (by decide) (pCore 2 I) pCore_isPGroup).trans hrI)
  have hcan := minimal_five_core_canonical_structure a.representation a.faithful X hcore hrX
    hmin R hcomm hmove
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hBI : B ≤ I :=
    sup_le (fun _ hx => hI.1.2 (Or.inl hx)) (fun _ hx => hI.1.2 (Or.inr hx))
  have hLI : F.Li L 1 ≤ I := le_sup_left.trans hBI
  have hp : IsPPerfect 2 ((F.Li L 1).subgroupOf I) := by
    rw [←local_point_residual h structural I hBI]
    exact isPPerfect_embedded_pResidual 2 _
  have hpm : IsPPerfect 2 (((F.Li L 1).subgroupOf I).map q) :=
    hp.of_surjective _ (q.subgroupMap_surjective _)
  have hgenI : Y ⊔ B.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBI,←MonoidHom.range_eq_map,range_subtype]
    exact hgen.symm
  have hgenStar : X ⊔ (B.subgroupOf I).map q = ⊤ := by
    have hh := congrArg (map q) hgenI
    rw [Subgroup.map_sup,hYm,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hn := local_point_normal_of_centralized_supplement h structural I hBI X hgenStar
    (hcan.2.2.2 _ hpm)
  have hm : ⁅F.UH I,F.Li L 1⁆ = F.UH I := by
    let := h.chosen.elementary
    exact (conjugateSpanBy_eq_commutator_of_seed V I (F.Li L 1) (F.Li L 1)
      hLI ((normal_subgroupOf_iff_le_normalizer hLI).mp hn) le_rfl
      (seed_commutator h F)).symm
  exact ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,hYm,hYk,he,
    hout,hgen,hs,hn,local_point_star_card_of_normal h structural I hLI hn,hm,hU,a,
    A,R,hAR,hA,hfaith,hR,hRE,hRc,hcub,hfixed,hcomm,hmove,hcompl,hcan⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
