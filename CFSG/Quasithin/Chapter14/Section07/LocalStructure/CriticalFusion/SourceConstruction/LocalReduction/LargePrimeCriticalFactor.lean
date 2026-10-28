module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCriticalActor

/-!
# The selected critical reflection in an actual dihedral factor

The original minimal five-core witness supplies the normal lift and its
exact O₂ kernel, the normal point cubic, the literal quotient action and
the selected endpoint. The preceding actor calculation gives an order-two
image, displacement two and a four-dimensional order-five support. Its
fixed complement makes it a supported reflection. Minimality conjugates
this reflection into a normal family of one or two genuine D10 factors.

The selected actor belongs to one specified factor, with the original
support, full quotient generation and cubic centralization retained.
Reciprocal endpoint selection returns every I-normalized label and has
both literal denominator ranks equal to one. The common-center lift and
the two ambient exclusions on pp.1044–1045 remain; five-core vanishing
and the final residual alternatives are not asserted here.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, using F.9.17 and
D.2.12–17; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original minimal five-core obstruction has a selected order-two
critical actor in one of its actual D10 factors, and a reciprocal selected
endpoint with both denominator ranks equal to one. No actor or factor
recognition premise is assumed. -/
theorem local_minimal_five_critical_factor
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
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      Nat.card (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 3 ∧
      ⁅F.UH I,F.Li L 1⁆ = F.UH I ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          (∀ t : HStar I, fixedCodim a.representation (zpowers t) ≠ 1) ∧
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            3 ≤ hf.b ∧ Odd hf.b ∧
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              A ≤ centralizer (((F.Li L 1).subgroupOf I).map
                (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) ∧
              A ⊓ centralizer (X : Set (HStar I)) = ⊥ ∧
              rank A = 1 ∧ Nat.card A = 2 ∧ fixedCodim a.representation A = 2 ∧
              Nat.card (⁅X,A⁆ : Subgroup (HStar I)) = 5 ∧
              Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⁅X,A⁆) = 4 ∧
              IsCompl (subspaceCommutator a.representation ⊤ ⁅X,A⁆)
                (fixedSpace a.representation (⁅X,A⁆ ⊔ A)) ∧
              Nat.log 2 ((commutatorPreimage (F.UH I) (c.endpoint.conjugate (F.UH I))
                (c.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 ∧
              let := BinaryGroupAction.action a.representation
              smallSupportGroup (HStar I)
                (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2 = X ∧
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                i.val = ⁅X,A⁆ ∧ f.factor i = ⁅X,A⁆ ⊔ A ∧ X ≤ f.product ∧
                ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
                  centralizer (f.product : Set (HStar I)) ∧
                f.product ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
                  (QuotientGroup.mk' (pCore 2 I)) = ⊤ ∧
                0 < Nat.card (smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ∧
                Nat.card (smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≤ 2 ∧
                ∃ r : SelectedQuadraticEndpoint hf a,
                  (∀ D : Subgroup G, I ≤ normalizer (D : Set G) →
                    r.endpoint.conjugate (c.endpoint.conjugate D) = D) ∧
                  r.endpoint.representative * c.endpoint.representative ∈ I ∧
                  rank (actorImage I (r.endpoint.conjugate (F.UH I))) = 1 ∧
                  Nat.log 2 ((commutatorPreimage (F.UH I) (r.endpoint.conjugate (F.UH I))
                    (r.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,B,R,hBR,hB,hfaith,hR,hRE,hRc,
      hcub,hfixed,hcomm,hmove,hcompl,hcan,hpos,hcount,hcentral,f₀,i₀,hi₀,hfi₀,hXD₀,hPD₀,hfull₀,
      hno,hf,hb,ho,c,houtc,r₀,hprod₀,hlabels₀⟩ :=
    local_minimal_five_critical_geometry h hab structural previous J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := hXn
  let := hXp
  let E := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hEI : E ≤ I :=
    sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  have hgenI : Y ⊔ E.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hEI,←MonoidHom.range_eq_map,range_subtype]
    exact hgen.symm
  have hgenStar : X ⊔ (E.subgroupOf I).map q = ⊤ := by
    have hh := congrArg (map q) hgenI
    rw [Subgroup.map_sup,hYm,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  obtain ⟨hAP,hAX⟩ := local_critical_actor_control h structural previous I hI hn hf c.endpoint hb X hgenStar
  obtain ⟨hr,hAc,hAd,hCX,hW,hcomp,hden,hreverse⟩ :=
    local_five_critical_rank_one h structural previous I hI hn a hf c hb X hcard hgenStar
  let A := actorImage I (c.endpoint.conjugate (F.UH I))
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let := BinaryGroupAction.action a.representation
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I) (Multiplicative W) :=
    BinaryGroupAction.faithful a.representation a.faithful
  have hC : ⁅X,A⁆ ∈ smallSupportFactors (HStar I) (Multiplicative W) 2 := by
    refine ⟨(commutator_le_left X A).trans (hcore.le.trans (pCore_le_fitting _ 5)),hCX,?_⟩
    rw [BinaryGroupAction.commutator_card,hW]
  let i : smallSupportFactors (HStar I) (Multiplicative W) 2 := ⟨⁅X,A⁆,hC⟩
  have hfixedC : fixedSpace a.representation (⁅X,A⁆ ⊔ A) =
      fixedSpace a.representation ⁅X,A⁆ := by
    apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone _ le_sup_left)
    have hc := (ElementaryCore.SupportExclusion.moved_split a.representation ⁅X,A⁆
      (by rw [hCX]; decide)).symm
    have h₁ := Submodule.finrank_add_eq_of_isCompl hcomp
    have h₂ := Submodule.finrank_add_eq_of_isCompl hc
    exact Nat.add_left_cancel (h₁.trans h₂.symm)
  have hfix : FixedPoints.subgroup (⁅X,A⁆ : Subgroup (HStar I)) (Multiplicative W) ≤
      FixedPoints.subgroup A (Multiplicative W) := by
    rw [BinaryGroupAction.fixedPoints_eq,BinaryGroupAction.fixedPoints_eq]
    apply BinaryGroupAction.submoduleEquivSubgroup.monotone
    rw [←hfixedC]
    exact fixedSpace_antitone _ le_sup_right
  obtain ⟨f,hfi⟩ := canonical_five_dihedral_family X hcan hmin i A hAc
    (normalizer_commutator_ge_right X A) hfix
  have hXD : X ≤ f.product := hcan ▸ f.core_le_product
  let P := ((F.Li L 1).subgroupOf I).map q
  let : P.Normal := Normal.map hn q (QuotientGroup.mk'_surjective _)
  have hPD : P ≤ centralizer (f.product : Set (HStar I)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_disjoint
    apply disjoint_of_coprime_natCard
    rw [show Nat.card P = 3 from hpoint,f.product_card]
    exact Nat.Coprime.pow_right _ (by decide)
  have hfull : f.product ⊔ (E.subgroupOf I).map q = ⊤ :=
    top_unique (hgenStar ▸ sup_le_sup_right hXD _)
  exact ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,hYm,hYk,he,
    hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,hr,hAc,hAd,hCX,hW,hcomp,
    hden,hcan,f,i,rfl,hfi,hXD,hPD,hfull,hpos,hcount,hreverse⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
