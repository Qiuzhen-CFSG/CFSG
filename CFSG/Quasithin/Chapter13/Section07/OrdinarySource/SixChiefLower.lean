module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SixChief
public import CFSG.Quasithin.Chapter13.Section07.SourceDuality
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.Representation.BinaryConjugationSection.CubicLength
public import Theory.Representation.ChiefCountCubic
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Kernel
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SixA4Quotient
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SixCubicMovement
/-!
# Six noncentral binary chief factors in the original six-letter branch

The marked natural section supplies two noncentral L₁-chief factors on U_H.
Their cubic fixed index is sixteen. Since the selected component fixes U₀,
source central duality gives the same cubic contribution on Q_H/C_H(U_H).
The moving V_H/U_H section contributes at least one further factor below
C_H(U_H). Thus Q_H has cubic length at least five. The original point
residual has its actual A₄ quotient with kernel Q_H ∩ L₁, whose Klein-four
layer supplies the sixth factor in every complete L₁ chief series.

All quotient maps and conjugation actions are retained. Fixed-layer centrality
and noncentrality of the full-span quotient are the independent earlier source
conclusions, respectively 13.7.16(2) and 13.7.7.
Source: Aschbacher--Smith, the final argument of 13.7.21, printed pp.945–946.
-/
public section
open Subgroup Representation
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The normal Klein-four layer of an A₄ quotient adds the sixth factor. -/
private theorem six_chief_count_of_kernel_length
    {J : Type*} [Group J] [Finite J]
    (f : J →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (A : Subgroup J) (hA : Nat.card A = 3)
    (hfive : 5 ≤ conjugationCubicLength A f.ker)
    (s : NoncentralChiefRefinement.ChiefSeries J) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    6 ≤ s.noncentralTwoCount := by
  rw [NoncentralChiefRefinement.CubicComparison.alternatingFour_count f hf hp A hA s h0 h1]
  omega

private theorem count_of_two_chief
    {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) J E)
    (h : Section08.CriticalGeometry.Reorientation.TwoNoncentralChiefFactors σ) :
    HasCount σ 2 := by
  obtain ⟨n,c,h0,h1,hc,hcount⟩ := h
  let s : Series σ := ⟨n,c,hc⟩
  refine ⟨s,h0,h1,?_⟩
  change Nat.card {i : Fin n // ¬ Central (c i.castSucc) (c i.succ)} = 2
  rw [← hcount]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  have he : Central (c i.castSucc) (c i.succ) ↔
      ∀ g v, Representation.BinaryOffender.sectionRepresentation σ
        (c i.castSucc) (c i.succ) g v = v := by
    apply forall_congr'
    intro g
    exact (Representation.BinaryOffender.sectionRepresentation_trivial_iff
      σ (c i.castSucc) (c i.succ) g).symm
  simpa only [not_forall] using not_congr he

private theorem uh_cubic_length
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (J : Subgroup G) (hJH : J ≤ H)
    (f : J →* alternatingGroup (Fin 4)) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker)
    (hc : Section08.CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      (ChiefQuotient.loneRepresentation H V₃ J hJH))
    (A : Subgroup G) (hAJ : A ≤ J) (hA : Nat.card A = 3) :
    conjugationCubicLength A (Section08.Source.UH H V₃) = 2 := by
  have hAc : Nat.card (A.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  let τ := (ChiefQuotient.loneRepresentation H V₃ J hJH).comp (A.subgroupOf J).subtype
  have hn : A ≤ normalizer (Section08.Source.UH H V₃ : Set G) :=
    (hAJ.trans hJH).trans (le_normalizer_conjugateSpanBy V₃ H)
  let := conjMulDistribMulActionOfLeNormalizer A (Section08.Source.UH H V₃) hn
  let e : (Section08.Source.UH H V₃) ≃* Multiplicative (Additive (Section08.Source.UH H V₃)) := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul u)
    invFun := fun u => u.toAdd.toMul
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have heq : ∀ a u, e (a • u) =
      Multiplicative.ofAdd (τ ((subgroupOfEquivOfLe hAJ).symm.toMonoidHom a) (e u).toAdd) := by
    intro a u
    rfl
  rw [conjugationCubicLength_eq A (Section08.Source.UH H V₃) hn]
  rw [BinaryFixedPoints.cubicLength_eq_of_equivariant τ
    (subgroupOfEquivOfLe hAJ).symm.toMonoidHom
    (subgroupOfEquivOfLe hAJ).symm.surjective e heq]
  exact ChiefCountCubic.log_fixedIndex_eq_count f hf hp (A.subgroupOf J) hAc _
    (count_of_two_chief _ hc)

private theorem source_core_cubic_length_five
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 3)
    (hcentral : A ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hUlen : conjugationCubicLength A (Section08.Source.UH H V₃) = 2)
    (hmove : ¬ ⁅Section08.Source.VH H V,A⁆ ≤ Section08.Source.UH H V₃) :
    5 ≤ conjugationCubicLength A (H.pCoreIn 2) := by
  obtain ⟨hE,τ,sU,sQ,hpair,hcoord⟩ := source_central_duality d h hU
  have hpA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hpQ : IsPGroup 2 (H.pCoreIn 2) := isPGroup_pCoreIn 2 H
  have hpU : IsPGroup 2 (Section08.Source.UH H V₃) :=
    hpQ.of_injective (inclusion h.UH_le_QH) (inclusion_injective _)
  have hd := sU.dual_sectionCubicLength sQ A hAH hA hpU hpQ
  have hfix : conjugationCubicLength A
      (PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)) = 0 := by
    unfold conjugationCubicLength
    rw [relIndex_eq_one.mpr (le_centralizer_iff.mp hcentral)]
    decide
  change conjugationCubicLength A
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G)) = 0 at hfix
  have hUV : Section08.Source.UH H V₃ ≤ Section08.Source.VH H V :=
    conjugateSpanBy_mono d.seed_le le_rfl
  have hVC : Section08.Source.VH H V ≤ Section08.Source.HC H V₃ :=
    VH_centralizes_UH d h hU
  have hAQ : A ≤ normalizer (H.pCoreIn 2 : Set G) := hAH.trans
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
  have hAV : A ≤ normalizer (Section08.Source.VH H V : Set G) :=
    hAH.trans (le_normalizer_conjugateSpanBy V H)
  have hAU : A ≤ normalizer (Section08.Source.UH H V₃ : Set G) :=
    hAH.trans (le_normalizer_conjugateSpanBy V₃ H)
  have hVU : Section08.Source.VH H V ≤ normalizer (Section08.Source.UH H V₃ : Set G) :=
    h.VH_le_H.trans (le_normalizer_conjugateSpanBy V₃ H)
  let : ((Section08.Source.UH H V₃).subgroupOf (Section08.Source.VH H V)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUV).mpr hVU
  have hpV : IsPGroup 2 (Section08.Source.VH H V) :=
    hpQ.of_injective (inclusion (VH_le_core d h hU)) (inclusion_injective _)
  have hpos := sectionCubicLength_pos_of_commutator_not_le A
    (Section08.Source.VH H V) (Section08.Source.UH H V₃) hpA hpV hUV hAV hAU hmove
  have hmono := conjugationCubicLength_mono A hVC
  have hCQ := conjugationCubicLength_mono A sQ.kernel_le
  unfold sectionCubicLength at hd hpos
  rw [hfix,hUlen] at hd
  omega

/-- The original six-letter packet forces six noncentral binary factors in
any complete chief series of the actual source point residual. -/
theorem source_six_chief_count_ge_six
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hspan : ¬ ⁅Section08.Source.VH H V,H⁆ ≤ Section08.Source.UH H V₃)
    (s : NoncentralChiefRefinement.ChiefSeries (sourceOne L T V₁))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    6 ≤ s.noncentralTwoCount := by
  let J := sourceOne L T V₁
  let Q := H.pCoreIn 2
  have hJH : J ≤ H := hL₁K.trans hKH
  obtain ⟨f,hf,hker⟩ := OrdinarySource.source_six_residual_surjection
    d hH h hKH hK hL₁K ρ hρ eK hs
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 H).comap_subtype
  have hdiv : 3 ∣ Nat.card J := by
    apply dvd_trans _ (card_dvd_of_surjective f hf)
    rw [nat_card_alternatingGroup]
    norm_num
  obtain ⟨B,hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := J) 3 (n := 1) (by simpa using hdiv)
  let A := B.map J.subtype
  have hAJ : A ≤ J := by
    rintro _ ⟨b,hb,rfl⟩
    exact b.property
  have hA : Nat.card A = 3 := by
    rw [card_map_of_injective Subtype.val_injective]
    simpa using hB
  have hUA : conjugationCubicLength A (Section08.Source.UH H V₃) = 2 :=
    uh_cubic_length J hJH f hf hp
      (ModelExclusions.six_chief_factors_of_one_le d hH h hKH hK hL₁K ρ hρ eK hs) A hAJ hA
  have hmove := OrdinarySource.source_six_cubic_movement d hH h hKH hK hL₁K
    ρ hρ eK hs hspan A hAJ hA
  have hfive := source_core_cubic_length_five d h inferInstance A (hAJ.trans hJH) hA
    ((hAJ.trans hL₁K).trans hcentral) hUA hmove
  have hQL : Q ≤ normalizer (J : Set G) := h.QH_le_T.trans
    (T_normalizes_one L T V₁ d.line_stable)
  have hLQ : J ≤ normalizer (Q : Set G) := hJH.trans
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
  have hlength := NoncentralChiefRefinement.CubicComparison.intersection_length_eq A Q J
    (IsPGroup.of_card (n := 1) (by simpa using hA)) (isPGroup_pCoreIn 2 H) hAJ hQL hLQ
  have hfi : conjugationCubicLength (A.subgroupOf J) f.ker =
      conjugationCubicLength A Q := by
    rw [hker]
    have he := NoncentralChiefRefinement.CubicComparison.length_subgroupOf A (J ⊓ Q) J hAJ inf_le_left
    rw [inf_subgroupOf_left] at he
    have he' : conjugationCubicLength (A.subgroupOf J) (Q.subgroupOf J) =
        conjugationCubicLength A (Q ⊓ J) := by simpa only [inf_comm] using he
    exact he'.trans hlength
  have hAc : Nat.card (A.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  apply six_chief_count_of_kernel_length f hf hp (A.subgroupOf J) hAc _ s h0 h1
  rw [hfi]
  exact hfive

end CFSG.Quasithin.Chapter13.Section07
