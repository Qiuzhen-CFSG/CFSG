module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedCore
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedBorel
public import Theory.GroupTheory.IrreducibleSectionCore.Ambient
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowFixedDimension

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed

/-!
# Excluding the tensor marking on the original exchanged actor

The F.9 commutator section in the original `U_H/V₁` has binary dimension
four and is fixed by the Sylow subgroup lying in the edge core `R₁`. In the
tensor model for the exchanged `SL₂(4) × SL₂(4)` actor, that Sylow fixes at
most a binary two-space. The contradiction below is on the literal original
quotient, with its original action through `H/O₂(H)`; both the group and
module coordinates identifying the tensor model remain explicit inputs.

Source: Aschbacher--Smith, proof of 12.6.33, printed p.838.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)

include hz hTV hTz hbound hH in
theorem SourceHypothesis.original_edge_core_fixes_perpendicular
    :
    ⁅(D.fullSetup hZ T z).V₅,(D.fullSetup hZ T z).R₁⁆ ≤
      (D.fullSetup hZ T z).V₁ := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  exact ambient_irreducible_section_core E.V₁ E.V₅ (E.L₁ ⊔ (T : Subgroup G))
    h.point_lt.le (E.V₅_le.trans (S.chosen.le_sylow.trans le_sup_right))
    (h.local_le.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    h.local_normalizes ((IsElementaryAbelian.isPGroup 2 V).to_le E.V₅_le)
    h.irreducible

variable [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

local instance tensor_source_span_elementary (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    IsElementaryAbelian 2 (Chapter13.Section08.Source.UH J E.V₅) :=
  inferInstanceAs (IsElementaryAbelian 2 (E.UH J))

local instance tensor_source_span_normal (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    (E.V₁.subgroupOf (Chapter13.Section08.Source.UH J E.V₅)).Normal :=
  inferInstanceAs ((E.V₁.subgroupOf (E.UH J)).Normal)

include hz hTV hTz hbound hH in
/-- The actual perpendicular image, rather than an unspecified isomorphic
four-space, is fixed by the original edge core. -/
theorem SourceHypothesis.original_perpendicular_fixed_four_space :
    Module.finrank (ZMod 2)
      (sourceSeedSpace H (D.fullSetup hZ T z).V₅ (D.fullSetup hZ T z).V₁) = 4 ∧
    sourceSeedSpace H (D.fullSetup hZ T z).V₅ (D.fullSetup hZ T z).V₁ ≤
      fixedSpace a.representation (actorImage H (D.fullSetup hZ T z).R₁) := by
  let E := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let c : BinaryConjugationSection H (E.UH H) E.V₁ (a.representation.comp q) := {
    section_le := a.le_local
    kernel_le := a.kernel_le
    normalized := a.normalizes
    coordinates := (MulEquiv.multiplicativeAdditive _).symm.toMonoidHom.comp
      (QuotientGroup.mk' (E.V₁.subgroupOf (E.UH H)))
    onto := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
      (QuotientGroup.mk'_surjective _)
    kernel_eq := by ext u; exact QuotientGroup.eq_one_iff u
    equivariant := fun g u => (a.conjugation g u).symm }
  change Module.finrank (ZMod 2) (c.imageSpace E.V₅) = 4 ∧
    c.imageSpace E.V₅ ≤ fixedSpace a.representation (actorImage H E.R₁)
  refine ⟨c.imageSpace_finrank_of_index E.V₅
    (le_conjugateSpanBy _ _) 4 ?_,?_⟩
  · have hc := card_eq_card_quotient_mul_card_subgroup (E.V₁.subgroupOf E.V₅)
    rw [Nat.card_congr (subgroupOfEquivOfLe E.V₁_le_V₅).toEquiv,
      E.point_card hz,E.perpendicular_card hz] at hc
    change 2 ^ 5 = E.V₁.relIndex E.V₅ * 2 at hc
    omega
  · intro v hv x
    obtain ⟨r,hr,he⟩ := x.property
    change q r = x.val at he
    change a.representation x.val v = v
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le E.R₁ E.V₅
      (by
        rw [commutator_comm]
        exact S.original_edge_core_fixes_perpendicular D hZ z hz hTV hTz hbound hH) r hr v hv

include hz hTV hTz hbound hH in
/-- A binary four-space in the original quotient is fixed by R₁-star. -/
theorem SourceHypothesis.original_edge_core_fixed_four_space :
    ∃ W : Submodule (ZMod 2) (Additive ((D.fullSetup hZ T z).UH H ⧸
        ((D.fullSetup hZ T z).V₁).subgroupOf ((D.fullSetup hZ T z).UH H))),
      Module.finrank (ZMod 2) W = 4 ∧
      W ≤ fixedSpace a.representation (actorImage H (D.fullSetup hZ T z).R₁) :=
  ⟨_,S.original_perpendicular_fixed_four_space D hZ z hz hTV hTz hbound hH a⟩

variable (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {K : Subgroup G} (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔
    (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
theorem SourceHypothesis.original_abelian_exchanged_tensor_impossible
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    (eK : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
      ClassicalOrthogonal.FourPlusMatrix.Binary.G)
    (eU : (Additive ((D.fullSetup hZ T z).UH H ⧸
        ((D.fullSetup hZ T z).V₁).subgroupOf ((D.fullSetup hZ T z).UH H))) ≃ₗ[ZMod 2]
      ClassicalOrthogonal.FourPlusMatrix.Binary.V)
    (he : ∀ (k : actorImage H (conjugateSpanBy K (T : Subgroup G))) u,
      eU (a.representation k.val u) =
        ClassicalOrthogonal.FourPlusMatrix.Binary.action (eK k) (eU u)) : False := by
  obtain ⟨t,ht,hTH,htn,hOH,e,P,hcoords,hP,hstar,hsol,hLB,hBM,hnB,
      heven,hBrank,hOT,hBeq,hMeq⟩ :=
    S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn (n := 2) (by decide) hm
  have hcore := S.original_abelian_exchanged_sylow_le_edge_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn (n := 2) (by decide) hm
  obtain ⟨W,hdim,hfix⟩ := S.original_edge_core_fixed_four_space
    D hZ z hz hTV hTz hbound hH a
  have hb := ClassicalOrthogonal.FourPlusMatrix.Binary.finrank_le_two_of_equivariant_sylow_fixed
    (a.representation.comp (actorImage H (conjugateSpanBy K (T : Subgroup G))).subtype)
    eK.toMonoidHom eK.surjective eU he P W (by
      intro k hk u hu
      apply hfix hu ⟨k.val,?_⟩
      apply (map_mono (comap_mono hcore))
      change k.val ∈ actorImage H
        ((T : Subgroup G) ⊓ conjugateSpanBy K (T : Subgroup G))
      rw [←hP]
      exact mem_map_of_mem _ hk)
  omega

end CFSG.Quasithin.Chapter12.Section06
