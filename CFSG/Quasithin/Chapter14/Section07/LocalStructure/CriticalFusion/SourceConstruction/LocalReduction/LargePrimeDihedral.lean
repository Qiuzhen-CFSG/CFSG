module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimePointNormal
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDihedral
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion.Linear

/-!
# The normal dihedral product in the original minimal five-core obstruction

The original minimal local overgroup I retains its normal two-perfect lift Y,
its exact O₂(Y) quotient kernel, normal point residual L₁, and its actual
faithful action on U_I/V₁. The order-five reflection commutator is a canonical
factor. Odd-order splitting identifies its fixed complement, so the reflection
extends it to D10. Minimal normality makes all canonical factors conjugate;
the supported dihedral construction therefore yields one or two independent
D10 factors, permuted by the full I/O₂(I), on the actual four-spaces.

Their normal product contains the whole five-core and generates the literal
quotient together with L₁T. The actual normal cubic L₁ image centralizes this
product by coprime normality. All factor supports, normalizers, multiplication
coordinates and concrete D10 models are available from the constructed family.
No identification with the full point normalizer is used.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, using D.2.12–17,
pp.183–187; refs/quasithin.pdf. The reciprocal critical geometry, the s=1
and s=2 ambient exclusions, and hence five-core vanishing remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original local witness supplies the normal dihedral product, without
assuming factorization or a new ambient-recognition premise. -/
theorem local_minimal_five_dihedral
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
          (∀ P : Subgroup (HStar I), IsPPerfect 2 P → P ≤ centralizer (X : Set (HStar I))) ∧
          ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
              (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
            (i : smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
            i.val = ⁅X,R⁆ ∧ f.factor i = ⁅X,R⁆ ⊔ R ∧
            X ≤ f.product ∧
            ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
              centralizer (f.product : Set (HStar I)) ∧
            f.product ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
              (QuotientGroup.mk' (pCore 2 I)) = ⊤ := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,
      hcub,hfixed,hcomm,hmove,hcompl,hcan⟩ :=
    local_minimal_five_point_normal h hab structural previous J hJ hne
  let := hXn
  let := hU
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let := BinaryGroupAction.action a.representation
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I) (Multiplicative W) :=
    BinaryGroupAction.faithful a.representation a.faithful
  have hC : ⁅X,R⁆ ∈ smallSupportFactors (HStar I) (Multiplicative W) 2 := by
    refine ⟨(commutator_le_left X R).trans (hcore.le.trans (pCore_le_fitting _ 5)),hcomm,?_⟩
    rw [BinaryGroupAction.commutator_card,hmove]
  let i : smallSupportFactors (HStar I) (Multiplicative W) 2 := ⟨⁅X,R⁆,hC⟩
  have hfixedC : fixedSpace a.representation (⁅X,R⁆ ⊔ R) =
      fixedSpace a.representation ⁅X,R⁆ := by
    apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone _ le_sup_left)
    have hc := (ElementaryCore.SupportExclusion.moved_split a.representation ⁅X,R⁆
      (by rw [hcomm]; decide)).symm
    have h₁ := Submodule.finrank_add_eq_of_isCompl hcompl
    have h₂ := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hfix : FixedPoints.subgroup (⁅X,R⁆ : Subgroup (HStar I)) (Multiplicative W) ≤
      FixedPoints.subgroup R (Multiplicative W) := by
    rw [BinaryGroupAction.fixedPoints_eq,BinaryGroupAction.fixedPoints_eq]
    apply BinaryGroupAction.submoduleEquivSubgroup.monotone
    rw [←hfixedC]
    exact fixedSpace_antitone _ le_sup_right
  obtain ⟨f,hfi⟩ := canonical_five_dihedral_family X hcan.1 hmin i R hRc
    (normalizer_commutator_ge_right X R) hfix
  have hXD : X ≤ f.product := hcan.1 ▸ f.core_le_product
  let P := ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
  let : P.Normal := Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hPD : P ≤ centralizer (f.product : Set (HStar I)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_disjoint
    apply disjoint_of_coprime_natCard
    rw [show Nat.card P = 3 from hpoint,f.product_card]
    exact Nat.Coprime.pow_right _ (by decide)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hBI : B ≤ I :=
    sup_le (fun _ hx => hI.1.2 (Or.inl hx)) (fun _ hx => hI.1.2 (Or.inr hx))
  have hgenI : Y ⊔ B.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBI,←MonoidHom.range_eq_map,range_subtype]
    exact hgen.symm
  have hgenStar : X ⊔ (B.subgroupOf I).map q = ⊤ := by
    have hh := congrArg (map q) hgenI
    rw [Subgroup.map_sup,hYm,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hfull : f.product ⊔ (B.subgroupOf I).map q = ⊤ :=
    top_unique (hgenStar ▸ sup_le_sup_right hXD _)
  exact ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,hYm,hYk,he,
    hout,hgen,hs,hn,hpoint,hm,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,hcub,hfixed,
    hcomm,hmove,hcompl,hcan.1,hcan.2.1,hcan.2.2.1,hcan.2.2.2,f,i,rfl,hfi,hXD,hPD,hfull⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
