module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCommonSpace

/-!
# The original minimal five-core witness with its common three-space

The original local construction supplies the minimal I, normal two-perfect
lift with its exact O₂ kernel, actual quotient action, selected critical
actor and specified dihedral factor. The new commutator geometry is applied
to that same selection. Both point residuals normalize C = [U,Uᶜ], whose
order is eight and whose two distinct fixed lines are exactly the original
point and its conjugate. Its quotient image and selected factor support use
the original coordinate map and retain the full central preimage.

No commutator geometry, lifted normalization or fixed-line premise is added.
The remaining A4/S4 and ambient arguments on pp.1044–1045, five-core
vanishing and the later residual classification remain local obligations.
The genuine earlier Structural1222/Theorem12213 inputs are unchanged.
Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G]


variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- The common three-space and its actual point-residual action for the same
minimal five-core obstruction, selected actor and specified dihedral factor.
This discharges the commutator-geometry step on p.1044 without assuming it. -/
theorem local_minimal_five_common_space
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
                    (r.endpoint.conjugate (F.Vi 1))).relIndex (F.UH I)) = 1 ∧
                  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
                  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
                  F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                  F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                  C ≤ F.UH I ∧ C ≤ c.endpoint.conjugate (F.UH I) ∧
                  IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                  s.image C = subspaceCommutator a.representation ⊤ A ∧
                  Module.finrank (ZMod 2) (s.image C) = 2 ∧
                  C = Chapter14.Section06.OddNormalizer.supportPreimage a (s.image C) ∧
                  F.Li L 1 ≤ normalizer (C : Set G) ∧
                  F.Li L 1 ≤ centralizer (F.Vi 1 : Set G) ∧
                  C ≤ Chapter14.Section06.OddNormalizer.supportPreimage a
                    (subspaceCommutator a.representation ⊤ i.val) ∧
                  c.endpoint.conjugate (F.Li L 1) ≤ normalizer (C : Set G) ∧
                  c.endpoint.conjugate (F.Li L 1) ≤
                    centralizer (c.endpoint.conjugate (F.Vi 1) : Set G) ∧
                  C ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1 ∧
                  C ⊓ centralizer (c.endpoint.conjugate (F.Li L 1) : Set G) =
                    c.endpoint.conjugate (F.Vi 1) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,
      hr,hAc,hAd,hCX,hW,hcomp,hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,
      r,hlabels,hprod,hrr,hrd⟩ :=
    local_minimal_five_critical_factor h hab structural previous J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  obtain ⟨hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre⟩ :=
    local_selected_common_space hf a c r hb hno hlabels hAc hAd hden hrr hrd
  have hpre' : ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ =
      Chapter14.Section06.OddNormalizer.supportPreimage a
        (subspaceCommutator a.representation ⊤ (actorImage I (c.endpoint.conjugate (F.UH I)))) :=
    hpre.trans (congrArg (Chapter14.Section06.OddNormalizer.supportPreimage a) himage)
  obtain ⟨hLC,hLZ,hCS⟩ := local_common_space_point_action I a hf c X
    (F.Li_one_le_of_mem_Hz hI) (le_centralizer_iff.mp hAP) hpre' hcomp
  rw [←hi] at hCS
  let := hXn
  let E := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hEI : E ≤ I := sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  have hgenI : Y ⊔ E.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hEI,←MonoidHom.range_eq_map,range_subtype]
    exact hgen.symm
  have hgenStar : X ⊔ (E.subgroupOf I).map q = ⊤ := by
    have hh := congrArg (map q) hgenI
    rw [Subgroup.map_sup,hYm,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  obtain ⟨hoppN,hoppZ⟩ := local_common_space_opposite_point_action h structural previous
    I hI hn a hf c r hb X hgenStar hlabels hopp
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  have hfixed := local_common_space_fixed_line h structural I (F.Li_one_le_of_mem_Hz hI)
    hn a hf C hbase hCU
  let g := c.endpoint.representative
  have hbackZ : F.Vi 1 ≤ C.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hopp
    change ((F.Vi 1).conjBy g).conjBy g⁻¹ ≤ _ at hh
    rwa [conjBy_inv] at hh
  have hbackU : C.map (MulAut.conj g⁻¹).toMonoidHom ≤ F.UH I := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hCB
    change _ ≤ ((F.UH I).conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hfixedBack := local_common_space_fixed_line h structural I (F.Li_one_le_of_mem_Hz hI)
    hn a hf (C.map (MulAut.conj g⁻¹).toMonoidHom) hbackZ hbackU
  have hfixedOpp := congrArg (map (MulAut.conj g).toMonoidHom) hfixedBack
  rw [map_inf _ _ _ (MulAut.conj g).injective,Theory.GroupTheory.map_centralizer_equiv] at hfixedOpp
  change (C.conjBy g⁻¹).conjBy g ⊓ centralizer (c.endpoint.conjugate (F.Li L 1) : Set G) =
    c.endpoint.conjugate (F.Vi 1) at hfixedOpp
  rw [conjBy_inv'] at hfixedOpp
  exact ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,hYm,hYk,he,
    hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,hr,hAc,hAd,hCX,hW,hcomp,
    hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,r,hlabels,hprod,hrr,hrd,
    hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre,hLC,hLZ,hCS,hoppN,hoppZ,hfixed,hfixedOpp⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
