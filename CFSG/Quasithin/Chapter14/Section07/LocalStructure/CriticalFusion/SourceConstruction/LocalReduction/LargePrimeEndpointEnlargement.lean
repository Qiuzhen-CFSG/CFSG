module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeEndpointPairing
public import Theory.GroupAction.ElementaryEightPointResidual.Enlargement
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.CComponent.SimpleImage
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The full common-space action or the simultaneous cubic branch

Apply the order-twelve enlargement to the original selected minimal I,
actor, dihedral factor and common eight-group C. Its two endpoint residuals
have distinct fixed lines, so one A₄ image already forces all of Aut(C).
The remaining alternative explicitly centralizes C with both original
local two-cores. Neither noncentralization is added as a premise.

In the full-action branch the literal N_G(C)/C_G(C) action quotient is
PSL₃(2), and the intersections N_G(C) ∩ N_G(Z) for the two original
point lines have the full point stabilizer images, each S₄. The quotient uses the normalizer
homomorphism kernel, identified by `normalizerMonoidHom_ker`. All previous
source, support, pairing and compatible Sylow data are retained.

The full-action branch also constructs an actual C-component covering the
action and its centralizer supplement. Apply A.3.9 and 1.2.1(1) at the
normalizer's actual two-core quotient; simplicity of the action image then
forces one C-component to cover it. Its two-core quotient is not
identified with this action quotient: the full cover and the subsequent
ambient normalizer argument remain open, as does the simultaneous cubic
branch. This disjunction does not assert the source
five-core exclusion or any of the final four recognition inputs.
Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

open Theory.GroupAction.ElementaryEightPointResidual
open Representation.BinaryOffender ChapterD
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08.SourceCompletion
/-- In the full-action branch, the original simple-QTKE hypothesis supplies
an actual C-component covering Aut(C), retaining the full centralizer kernel. -/
theorem common_eight_component_of_full_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (C : Subgroup G) [IsElementaryAbelian 2 C] (hc : Nat.card C = 8)
    (hfull : conjugationImage (normalizer (C : Set G)) C = ⊤) :
    ∃ D : Subgroup (normalizer (C : Set G)), D.IsCComponent ∧
      D.map C.normalizerMonoidHom = ⊤ ∧
      D.map (normalizer (C : Set G)).subtype ⊔ centralizer (C : Set G) =
        normalizer (C : Set G) ∧
      Nonempty ((D ⧸ (C.normalizerMonoidHom.comp D.subtype).ker) ≃*
        Matrix.PSL3Two.PSL) := by
  let N := normalizer (C : Set G)
  have hcore : C ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 C) C.le_normalizer le_rfl
  have hN : N ∈ Chapter1.H G := by
    intro he
    have hb : C = ⊥ := le_bot_iff.mp (he ▸ hcore)
    rw [hb,card_bot] at hc
    omega
  have hgen : cComponentLayer N = solvableResidual N :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hN)
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hc
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  let : IsSimpleGroup (MulAut C) := e.isSimpleGroup
  let : Group.IsPerfect (MulAut C) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hs : Function.Surjective C.normalizerMonoidHom :=
    MonoidHom.range_eq_top.mp ((conjugationImage_normalizer C).symm.trans hfull)
  obtain ⟨D,hD,hm⟩ := exists_cComponent_surjects_of_layer_eq_residual hgen C.normalizerMonoidHom hs
  have hsup := sup_ker_eq_top_of_map_eq_top C.normalizerMonoidHom hm
  have hsupG := congrArg (map N.subtype) hsup
  rw [Subgroup.map_sup,normalizerMonoidHom_ker,
    map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer (C : Set G)),
    ←MonoidHom.range_eq_map,Subgroup.range_subtype] at hsupG
  have hDsurj : Function.Surjective (C.normalizerMonoidHom.comp D.subtype) := by
    intro a
    obtain ⟨x,hx,rfl⟩ := hm.ge (mem_top a)
    exact ⟨⟨x,hx⟩,rfl⟩
  exact ⟨D,hD,hm,hsupG,⟨(QuotientGroup.quotientKerEquivOfSurjective
    (C.normalizerMonoidHom.comp D.subtype) hDsurj).trans e⟩⟩

/-- The same original witness has full normalizer action unless both local cores centralize C. -/
theorem local_minimal_five_full_action_or_cubic_pair
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
                    c.endpoint.conjugate (F.Vi 1) ∧
                  ((Nat.card (conjugationImage (F.Li L 1) C) = 3 ∨
                    (Nat.card (conjugationImage (F.Li L 1) C) = 12 ∧
                      Nonempty (conjugationImage (F.Li L 1) C ≃* alternatingGroup (Fin 4)))) ∧
                    (Nat.card (conjugationImage (F.Li L 1) C) = 3 ↔
                      (F.Li L 1).pCoreIn 2 ≤ centralizer (C : Set G))) ∧
                  ((Nat.card (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C) = 3 ∨
                    (Nat.card (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C) = 12 ∧
                      Nonempty (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C ≃*
                        alternatingGroup (Fin 4)))) ∧
                    (Nat.card (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C) = 3 ↔
                      (c.endpoint.conjugate (F.Li L 1)).pCoreIn 2 ≤ centralizer (C : Set G))) ∧
                  (F.Li L 1).pCoreIn 2 ⊔
                    (I.pCoreIn 2 ⊓ centralizer (F.UH I : Set G)) = I.pCoreIn 2 ∧
                  (c.endpoint.conjugate (F.Li L 1)).pCoreIn 2 ⊔
                    ((c.endpoint.conjugate I).pCoreIn 2 ⊓
                      centralizer (c.endpoint.conjugate (F.UH I) : Set G)) =
                    (c.endpoint.conjugate I).pCoreIn 2 ∧
                  (centralizer (C : Set G)).relIndex ((F.Li L 1).pCoreIn 2) =
                    (centralizer (C : Set G)).relIndex (I.pCoreIn 2) ∧
                  (centralizer (C : Set G)).relIndex (I.pCoreIn 2) =
                    ((F.UH I) ⊓ centralizer (I.pCoreIn 2 : Set G)).relIndex C ∧
                  (Nat.card (conjugationImage (F.Li L 1) C) = 3 ↔
                    I.pCoreIn 2 ≤ centralizer (C : Set G)) ∧
                  (Nat.card (conjugationImage (c.endpoint.conjugate (F.Li L 1)) C) = 3 ↔
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∧
                  ((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                    (conjugationImage (normalizer (C : Set G)) C = ⊤ ∧
                      Nonempty (((normalizer (C : Set G)) ⧸ C.normalizerMonoidHom.ker) ≃*
                        Matrix.PSL3Two.PSL) ∧
                      (∃ D : Subgroup (normalizer (C : Set G)), D.IsCComponent ∧
                        D.map C.normalizerMonoidHom = ⊤ ∧
                        D.map (normalizer (C : Set G)).subtype ⊔ centralizer (C : Set G) =
                          normalizer (C : Set G) ∧
                        Nonempty ((D ⧸ (C.normalizerMonoidHom.comp D.subtype).ker) ≃*
                          Matrix.PSL3Two.PSL)) ∧
                      ∀ Z : Subgroup G, Z = F.Vi 1 ∨ Z = c.endpoint.conjugate (F.Vi 1) →
                        ∃ z : C, z ≠ 1 ∧ (z : G) ∈ Z ∧
                          conjugationImage (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C =
                            MulAction.stabilizer (MulAut C) z ∧
                          Nat.card (conjugationImage
                            (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C) = 24 ∧
                          Nonempty (conjugationImage
                            (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C ≃*
                              Equiv.Perm (Fin 4)))) ∧
                  (Nat.card (smallSupportFactors (HStar I)
                    (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 →
                    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ I ∧
                      c.endpoint.conjugate (F.UH I) ≤ S ∧
                      (∃ x : I, S = (x : G)⁻¹ • T) ∧
                      let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                      let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
                      ((T : Subgroup G) ⊓ normalizer (K1 : Set G)).relIndex (T : Subgroup G) = 2 ∧
                      T1.relIndex (S : Subgroup G) = 2 ∧
                      T1 ≤ normalizer (C : Set G) ∧
                      I ⊓ normalizer (C : Set G) ≤ normalizer (K1 : Set G) ∧
                      ∃ P : Sylow 2 (I ⊓ normalizer (C : Set G) : Subgroup G),
                        (P : Subgroup (I ⊓ normalizer (C : Set G) : Subgroup G)).map
                          (I ⊓ normalizer (C : Set G)).subtype = T1) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,
      hr,hAc,hAd,hCX,hW,hcomp,hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,
      r,hlabels,hprod,hrr,hrd,hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre,
      hLC,hLZ,hCS,hoppN,hoppZ,hfixed,hfixedOpp,himageB,himageOpp,
      hsupp,hsuppOpp,hindex,hpair,hcubic,hcubicOpp,hnormalizer⟩ :=
    local_minimal_five_endpoint_pairings h hab structural previous J hJ hne
  let := hU
  let := hXn
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let := hCE
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  have hZcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hWcard : Nat.card (c.endpoint.conjugate (F.Vi 1)) = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans hZcard
  have hcase := cubic_pair_or_full_normalizer (F.Li L 1)
    (c.endpoint.conjugate (F.Li L 1)) C (F.Vi 1) (c.endpoint.conjugate (F.Vi 1))
    hCc hZcard hWcard hLC hoppN hfixed hfixedOpp hnepoints
    (himageB.1.imp_right And.left) (himageOpp.1.imp_right And.left)
  have hresult :
((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                    (conjugationImage (normalizer (C : Set G)) C = ⊤ ∧
                      Nonempty (((normalizer (C : Set G)) ⧸ C.normalizerMonoidHom.ker) ≃*
                        Matrix.PSL3Two.PSL) ∧
                      (∃ D : Subgroup (normalizer (C : Set G)), D.IsCComponent ∧
                        D.map C.normalizerMonoidHom = ⊤ ∧
                        D.map (normalizer (C : Set G)).subtype ⊔ centralizer (C : Set G) =
                          normalizer (C : Set G) ∧
                        Nonempty ((D ⧸ (C.normalizerMonoidHom.comp D.subtype).ker) ≃*
                          Matrix.PSL3Two.PSL)) ∧
                      ∀ Z : Subgroup G, Z = F.Vi 1 ∨ Z = c.endpoint.conjugate (F.Vi 1) →
                        ∃ z : C, z ≠ 1 ∧ (z : G) ∈ Z ∧
                          conjugationImage (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C =
                            MulAction.stabilizer (MulAut C) z ∧
                          Nat.card (conjugationImage
                            (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C) = 24 ∧
                          Nonempty (conjugationImage
                            (normalizer (C : Set G) ⊓ normalizer (Z : Set G)) C ≃*
                              Equiv.Perm (Fin 4)))) := by
    rcases hcase with hc | hfullC
    · exact Or.inl ⟨hcubic.mp hc.1,hcubicOpp.mp hc.2⟩
    · refine Or.inr ⟨hfullC,normalizer_quotient_of_full_image C hCc hfullC,
        common_eight_component_of_full_action h.source.simpleQTKE C hCc hfullC,?_⟩
      intro Z hZ
      have hZC : Z ≤ C := by rcases hZ with rfl | rfl <;> assumption
      have hZc : Nat.card Z = 2 := by rcases hZ with rfl | rfl <;> assumption
      exact point_normalizer_image_of_full_normalizer C Z hCc hZc hZC hfullC
  exact ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,hYm,hYk,he,
    hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,hr,hAc,hAd,hCX,hW,hcomp,
    hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,r,hlabels,hprod,hrr,hrd,
    hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre,hLC,hLZ,hCS,hoppN,hoppZ,
    hfixed,hfixedOpp,himageB,himageOpp,hsupp,hsuppOpp,hindex,hpair,
    hcubic,hcubicOpp,hresult,hnormalizer⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
