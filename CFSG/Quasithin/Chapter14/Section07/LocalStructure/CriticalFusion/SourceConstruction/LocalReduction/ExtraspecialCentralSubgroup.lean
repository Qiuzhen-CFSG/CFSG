module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCenterControl
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralSeed
public import Theory.GroupTheory.CubicCentralLayer
public import Theory.GroupTheory.PGroup.NormalIndexTwoStep
public import Theory.Representation.BinaryConjugationSection.EmbeddedSection

/-!
# The central subgroup in the original faithful branch

Adjoin U to the central seed C constructed from the actual permutation core.
The lower chief flank makes CU invariant under K. Its commutator with
P = O₂(K) lies in V. Irreducibility of K on the original U/V₁ section
reduces this commutator to V₁, retaining the exact original quotient map.

The point residual has two-core P and cubic quotient. Coprime fixed-point
lifting and two-perfect commutator idempotence therefore give an element
of Z(P) outside U. The proved center control Z(P) ≤ Z(K) gives V₁ < Z(K).
An invariant index-two step above V₁ in Z(P) constructs an actual subgroup
of order four, central in K and normalized by H = KT.

Source: the faithful case of Aschbacher–Smith 14.7.25 and the following
choice of D, printed pp.1051–1052, refs/quasithin.pdf. The original flag,
point normality and named earlier implications remain intact. Their final
source discharge stays with the existing qt-d-14775-source producers.
The central case of 14.7.24, maximal-normalizer control and the remaining
reductions through 14.7.52 are not asserted here.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source NoncentralChiefRefinement
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem centralSeed_residual_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    IsIrreducible (ρ.comp (inclusion (K_le_H F))) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ,_,_,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let q := (residualStarEquiv F).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K F)))
  have hq : Function.Surjective q := (residualStarEquiv F).surjective.comp (QuotientGroup.mk'_surjective _)
  have heq : (σ.comp (pResidual 2 (HStar F.H)).subtype).comp q =
      ρ.comp (inclusion (K_le_H F)) := by
    ext k w
    change σ (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k)) w = _
    rw [residualStarEquiv_mk]
    exact congrArg (fun τ : Representation (ZMod 2) F.H W => τ (inclusion (K_le_H F) k) w) hσ
  exact heq ▸ (irreducible_comp_surjective_iff q hq _).mpr hi

omit [Finite G] in
private theorem centralSeed_normalizes_commutator (A B C : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) (hAC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer ((⁅B,C⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hAB ha),mem_normalizer_iff_map_conj_eq.mp (hAC ha)]

/-- A literal central seed outside U forces the strict central-subgroup
conclusion. The seed's commutators, residual-core placement and genuine
earlier source implications are all explicit here. -/
theorem extraspecial_core_center_strict_of_central_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (C : Subgroup G) (hCP : C ≤ (K F).pCoreIn 2) (hCU : ¬ C ≤ F.U)
    (hCA : ⁅C,F.Li L 1⁆ ≤ V) (hCK : ⁅C,K F⁆ ≤ F.U) :
    F.Vi 1 < (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype := by
  let P := (K F).pCoreIn 2
  let A := F.Li L 1
  let D := C ⊔ F.U
  have hUP : F.U ≤ P := span_le_residual_core h hab
  have hDP : D ≤ P := sup_le hCP hUP
  have hPH : P ≤ F.H := (pCoreIn_le 2 _).trans (K_le_H F)
  have hcore : A.pCoreIn 2 = P :=
    (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1
  have hPA : P ≤ A := hcore ▸ pCoreIn_le 2 A
  have hAK : A ≤ K F := pointResidual_le F
  have hAH : A ≤ F.H := hAK.trans (K_le_H F)
  have hHnU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hPnU : P ≤ normalizer (F.U : Set G) := hPH.trans hHnU
  have hDK : ⁅D,K F⁆ ≤ F.U := by
    have hn := commutator_commutatorPreimage_le P (K F) F.U hPnU
    have hD : D ≤ commutatorPreimage P (K F) F.U := sup_le
      (le_commutatorPreimage hCP hCK)
      (le_commutatorPreimage hUP (le_normalizer_iff_commutator_le_left.mp ((K_le_H F).trans hHnU)))
    exact (commutator_mono hD le_rfl).trans hn
  have hKnD : K F ≤ normalizer (D : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hDK.trans le_sup_right)
  have hKnP : K F ≤ normalizer (P : Set G) :=
    (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))
  have hPnV : P ≤ normalizer (V : Set G) :=
    (hPA.trans ((F.Li_le L 1).trans inf_le_left)).trans h.chosen.normalizes
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hUPcomm : ⁅F.U,P⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro p hp u hu
    apply (s.action_mem_ker_iff ⟨p,hPH hp⟩).mp _ u hu
    apply core_le_action_kernel h s
    have hcoreP : P ≤ F.H.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)
    have hrelative : (F.H.pCoreIn 2).subgroupOf F.H = pCore 2 F.H :=
      comap_map_eq_self_of_injective F.H.subtype_injective _
    rw [←hrelative]
    exact hcoreP hp
  have hPV : ⁅D,P⁆ ≤ V := by
    have hD : D ≤ commutatorPreimage P P V := sup_le
      (le_commutatorPreimage hCP ((commutator_mono le_rfl hPA).trans hCA))
      (le_commutatorPreimage hUP (hUPcomm.trans (F.le_seed 1)))
    exact (commutator_mono hD le_rfl).trans (commutator_commutatorPreimage_le P P V hPnV)
  have hpoint : F.Vi 1 ≤ centralizer (K F : Set G) := by
    apply le_centralizer_iff.mp
    exact (K_le_H F).trans (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))
  let M := ⁅D,P⁆ ⊔ F.Vi 1
  have hMV : M ≤ V := sup_le hPV (F.le_seed 1)
  have hKnM : K F ≤ normalizer (M : Set G) :=
    (le_inf (centralSeed_normalizes_commutator (K F) D P hKnD hKnP)
      ((le_centralizer_iff.mp hpoint).trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : IsIrreducible (ρ.comp (inclusion (K_le_H F))) :=
    centralSeed_residual_irreducible h hab structural previous he s
  let t := s.restrictActor (K_le_H F) (hUP.trans (pCoreIn_le 2 _))
  have hUnM : ¬ F.U ≤ M := by
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion (hh.trans hMV)) (inclusion_injective _)
    rw [(extraspecial_source_reduction h hab structural previous he).2.1,h.seed_card] at hc
    omega
  have hPM : ⁅D,P⁆ ≤ F.Vi 1 := by
    rw [←t.inf_eq_kernel_of_irreducible M hKnM le_sup_right hUnM]
    exact le_inf (hPV.trans (le_conjugateSpanBy V F.H)) le_sup_left
  have hAp : IsPPerfect 2 A := by
    change IsPPerfect 2 (F.Li L 1)
    simp only [InvariantFlag.Li]
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.H)
  have hfix : ¬ D ⊓ centralizer (A : Set G) ≤ F.U := by
    apply cubic_central_layer_lift A D F.U (F.Vi 1) hAp
      (pointResidual_core_quotient_card h structural)
      (hcore.symm ▸ hDP) le_sup_right (fun hh => hCU (le_sup_left.trans hh))
      (hAK.trans hKnD) (hAH.trans hHnU)
      (hpoint.trans (centralizer_le hAK))
      ((commutator_mono le_rfl hAK).trans hDK)
    rwa [hcore]
  have hcent : D ⊓ centralizer (A : Set G) ≤ (center P).map P.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact le_inf (inf_le_left.trans hDP) (inf_le_right.trans (centralizer_le hPA))
  have hVZ : F.Vi 1 ≤ (center P).map P.subtype := by
    rw [←extraspecial_core_center_inf_span h hab structural previous he]
    exact inf_le_right
  apply lt_of_le_not_ge hVZ
  intro hle
  exact hfix (hcent.trans (hle.trans s.kernel_le))

/-- Source 14.7.25 in the faithful alternative of 14.7.23. The actual core
marking constructs the central seed; no extra local recognition premise remains. -/
theorem extraspecial_center_strict_of_faithful
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    F.Vi 1 < (center (K F)).map (K F).subtype := by
  obtain ⟨C,hCP,hCU,_,hCA,hCK⟩ :=
    extraspecial_faithful_central_seed h hab structural previous faithful he hnc
  exact (extraspecial_core_center_strict_of_central_seed h hab structural previous faithful
    he C hCP hCU hCA hCK).trans_le
      (extraspecial_core_center_central d h hab structural previous faithful earlier he)

/-- The literal order-four subgroup needed immediately after 14.7.25, in
its faithful branch. It contains V₁, is central in K and is normalized by H. -/
theorem extraspecial_center_four_of_faithful
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ F.H ≤ normalizer (D : Set G) := by
  obtain ⟨C,hCP,hCU,_,hCA,hCK⟩ :=
    extraspecial_faithful_central_seed h hab structural previous faithful he hnc
  have hlt := extraspecial_core_center_strict_of_central_seed h hab structural previous faithful
    he C hCP hCU hCA hCK
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  have hZK : Z ≤ (center (K F)).map (K F).subtype :=
    extraspecial_core_center_central d h hab structural previous faithful earlier he
  have hPT : P ≤ (T : Subgroup G) := by
    exact (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)).trans
      ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1)))
  have hZT : Z ≤ (T : Subgroup G) := (map_subtype_le _).trans hPT
  have hVT : F.Vi 1 ≤ (T : Subgroup G) := hlt.le.trans hZT
  have hHnZ : F.H ≤ normalizer (Z : Set G) :=
    ((H_normalizes_K F).trans
      (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))).trans
      (normalizer_le_normalizer_characteristic_image P (center P))
  let V₀ := (F.Vi 1).subgroupOf (T : Subgroup G)
  let Z₀ := Z.subgroupOf (T : Subgroup G)
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (F.invariant 1)
  let : Z₀.Normal := normal_subgroupOf_of_le_normalizer ((F.invariant 1).trans hHnZ)
  have hlt₀ : V₀ < Z₀ := by
    apply lt_of_le_not_ge (subgroupOf_mono _ hlt.le)
    intro hh
    have hm := map_mono (f := (T : Subgroup G).subtype) hh
    rw [map_subgroupOf_eq_of_le hZT,map_subgroupOf_eq_of_le hVT] at hm
    exact hlt.not_ge hm
  obtain ⟨X,hX,hVX,hXZ,hindex⟩ := exists_normal_index_two_step
    (T : Subgroup G) T.isPGroup' V₀ Z₀ hlt₀
  let D := X.map (T : Subgroup G).subtype
  have hVD : F.Vi 1 ≤ D := by
    have hh := map_mono (f := (T : Subgroup G).subtype) hVX
    rwa [map_subgroupOf_eq_of_le hVT] at hh
  have hDZ : D ≤ Z := by
    have hh := map_mono (f := (T : Subgroup G).subtype) hXZ
    rwa [map_subgroupOf_eq_of_le hZT] at hh
  have hcard : Nat.card D = 4 := by
    have hmul := relIndex_mul_card_of_le hVX
    have hVcard : Nat.card V₀ = 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv]
      simpa using F.card 1 (by decide)
    rw [hindex,hVcard] at hmul
    rw [card_map_of_injective (T : Subgroup G).subtype_injective]
    exact hmul.symm
  have hTnD : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    let : X.Normal := hX
    have hh := (map_mono (f := (T : Subgroup G).subtype)
      (show (⊤ : Subgroup (T : Subgroup G)) ≤ normalizer (X : Set (T : Subgroup G)) from
        le_normalizer_of_normal)).trans
      (X.le_normalizer_map (T : Subgroup G).subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨D,hVD,hDZ.trans hZK,hcard,?_⟩
  rw [residual_product]
  apply sup_le _ hTnD
  apply (le_centralizer_iff.mp _).trans (Subgroup.centralizer_le_normalizer _)
  rw [map_center_subtype_eq_inf_centralizer] at hZK
  exact hDZ.trans (hZK.trans inf_le_right)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
