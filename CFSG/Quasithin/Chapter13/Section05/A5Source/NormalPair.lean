module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ResidualStructure
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceGeometry
public import CFSG.Quasithin.ChapterF.Section09.ClosurePair
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Recognition
public import Theory.GroupTheory.BaerSuzukiSubgroup
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer

/-!
# The original normal A₅ quaternion pair and starred action

The source block calculation supplies quaternion factors in the actual U_H,
with center the original line V₁. Its square action embeds H/O₂(H) in the
binary orthogonal group. The normal cubic image of L₁ and the singular
involution induced by V place that action in an actual S₃ × S₃ normalizer;
in particular |H/O₂(H)| divides 36.

Baer–Suzuki selects a non-two pair in the literal starred quotient. F.9.5
makes its two seeds generate a quaternion group of order 32. Containment
and the already proved order of U_H identify this seed join with U_H,
so the original pair contains the entire closure.

These are source steps of 13.5.15 used by 13.5.17. The later identification
of the pair two-core, H=G₁, O₂(M)=V and the weak BN-pair recognition are
not asserted here. The sole earlier-source parameter is full A.3.12;
the original marked Context, nonabelian closure and relative normality
of L₁ in H are retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.15 and 13.5.17, printed pp.919–922 (PDF pp.936–939).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.Section09.Setup.Hypothesis
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The actual quaternion factors have center the original order-two line. -/
theorem normal_quaternion_with_center :
    ∃ _q : QuaternionCentralProductData (Source.UH H V₃),
      (center (Source.UH H V₃)).map (Source.UH H V₃).subtype = V₁ := by
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨_,_,_,_,_,_,_,_,_,_,q,hq⟩ :=
    NormalBranch.block_consequences hf d.third_eq_commutator hn
      (fun ht => ⟨markedBlockInput d hA312 hH hU hg hg₁ ht⟩)
      ChapterG.Section01.SL2FourRecognition.recognitionInput
  refine ⟨q,?_⟩
  change (center D.UH).map D.UH.subtype = D.V₁
  rw [q.center_eq]
  exact hq

/-- The inclusion H* ≤ Ω₄⁺(2) in 13.5.15(8), using the original square action. -/
theorem normal_star_embedding :
    (∃ f : Source.Hstar H →* NormalBranch.OmegaPlusFour, Function.Injective f) ∧
      Nat.card (Source.Hstar H) ∣ 36 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨q,hq⟩ := normal_quaternion_with_center d hA312 hH hU hn
  change QuaternionCentralProductData D.UH at q
  change (center D.UH).map D.UH.subtype = D.V₁ at hq
  have hseed : D.Vplus = ⁅D.V,D.L₁⁆ := d.third_eq_commutator
  let f : Source.Hstar H →* BinaryFourPlus.Wreath := hf.closureStarEmbedding q hq
  have hfi : Function.Injective f := hf.closureStarEmbedding_injective q hq
  let A := Source.starImage H (residualCentralizer L V₁)
  let : ((residualCentralizer L V₁).subgroupOf H).Normal := hn
  let : A.Normal := Normal.map hn (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _)
  have hA : Nat.card A = 3 := by
    rw [Nat.card_congr (normal_residual_star_cubic d hA312 hH hU hn).toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  have hvn : ¬ V ≤ D.QH := fun hv => hU (hf.UH_elementary_of_V_le_QH hv).toIsMulCommutative
  obtain ⟨v,hv,hvq⟩ := Set.not_subset.mp hvn
  let vV : D.V := ⟨v,hv⟩
  let vH := inclusion hf.V_le_H vV
  let π := QuotientGroup.mk' (pCore 2 H)
  let x := π vH
  have hx : x ≠ 1 := by
    intro he
    exact hvq (mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff vH).mp he))
  have hsing : BinaryFourPlus.SingularDisplacements (f x) := by
    change BinaryFourPlus.SingularDisplacements (closureOrthogonalAction D.H le_rfl q vH)
    apply q.wreath_singular_displacement
    intro a
    apply Subtype.ext
    change (((v : G) * (a : G) * v⁻¹) * (a : G)⁻¹)^2 = 1
    apply elemPow_eq_one_of_isElementaryAbelian (G := G) (A := V)
    apply hf.plus_le
    rw [show (v * (a : G) * v⁻¹) * (a : G)⁻¹ = ⁅v,(a : G)⁆ from rfl,
      ← commutatorElement_inv]
    exact D.Vplus.inv_mem ((hf.core_module_commutator_le_seed d.third_index hvn)
      (commutator_mem_commutator (hf.UH_le_QH a.property) hv))
  have hcentral : x ∈ centralizer (A : Set (Source.Hstar H)) := by
    rintro _ ⟨l,hl,rfl⟩
    have hc : ⁅vH,l⁆ ∈ pCore 2 H := by
      have hm : (⁅vH,l⁆ : H).val ∈ D.QH := hf.UH_le_QH
        (le_conjugateSpanBy _ _ (hseed.symm ▸ commutator_mem_commutator hv hl))
      exact (show D.QH.subgroupOf H = pCore 2 H from
        comap_map_eq_self_of_injective H.subtype_injective _) ▸ hm
    have he : π vH * π l = π l * π vH := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hc
    exact he.symm
  obtain ⟨hr,hd⟩ := BinaryFourPlus.CubicNormalizer.image_le_normalizer_and_card_dvd
    f hfi A hA x hx hsing hcentral
  obtain ⟨e⟩ := (BinaryFourPlus.CubicNormalizer.image_models f hfi A hA x hx hsing hcentral).1
  let j := f.codRestrict (normalizer (A.map f : Set BinaryFourPlus.Wreath))
    (fun y => hr ⟨y,rfl⟩)
  have hj : Function.Injective j := fun a b he => hfi
    (congrArg (fun z : normalizer (A.map f : Set BinaryFourPlus.Wreath) =>
      (z.val : BinaryFourPlus.Wreath)) he)
  exact ⟨⟨e.toMonoidHom.comp j,e.injective.comp hj⟩,hd⟩

/-- Every non-two starred pair has its seed join equal to the whole U_H. -/
theorem normal_pair_seed_eq {g : G} (hg : g ∈ H)
    (hpair : ¬ IsPGroup 2 (Source.starImage H
      (V ⊔ ChapterG.Section02.Setup.conjugate V g))) :
    V₃ ⊔ ChapterG.Section02.Setup.conjugate V₃ g = Source.UH H V₃ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hp : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) := by
    intro hh
    exact hpair (hh.comap_subtype.map _)
  obtain ⟨q⟩ := hf.pair_seed_quaternion d.third_index d.module_card
    (fun _ hk hi => source13_5_13_one d hA312 hH hU hk hi)
    (source_seed_centralizer_bound d hA312) g⁻¹ (H.inv_mem hg) hp
  obtain ⟨qU,_⟩ := normal_quaternion_with_center d hA312 hH hU hn
  apply eq_of_le_of_card_ge
  · exact sup_le (le_conjugateSpanBy _ _)
      (pair_seed_conjugate_le_closure (D := D) g⁻¹ (H.inv_mem hg))
  · exact qU.card.trans q.card.symm |>.le

/-- The original source pair is chosen internally; its starred quotient is S₃
and the pair contains the entire quaternion closure. -/
theorem source_normal_pair : ∃ g ∈ H,
    V₃ ⊔ ChapterG.Section02.Setup.conjugate V₃ g = Source.UH H V₃ ∧
    Source.UH H V₃ ≤ V ⊔ ChapterG.Section02.Setup.conjugate V g ∧
    Nonempty (Source.starImage H (V ⊔ ChapterG.Section02.Setup.conjugate V g) ≃*
      Equiv.Perm (Fin 3)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hc := LocalGeometry.star_V_card_two hf d.third_index hU
  have hp : IsPGroup 2 (Source.starImage H V) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  obtain ⟨x,hx⟩ := (le_pCore_or_exists_conjugate_sup_not_isPGroup _ hp).resolve_left (by
    intro hle
    rw [pCore_quotient_pCore_eq_bot] at hle
    have hz := le_bot_iff.mp hle
    rw [hz,card_bot] at hc
    contradiction)
  obtain ⟨g,hg,_,he⟩ := ComponentReduction.Fitting.SourceAction.lift_pair H V hf.V_le_H x
  have hpair : ¬ IsPGroup 2 (Source.starImage H
      (V ⊔ ChapterG.Section02.Setup.conjugate V g)) := he ▸ hx
  have hs := normal_pair_seed_eq d hA312 hH hU hn hg hpair
  refine ⟨g,hg,hs,?_,?_⟩
  · rw [←hs]
    exact sup_le_sup d.third_le (map_mono d.third_le)
  · exact hf.pair_star_symmetricThree_right d.third_index d.module_card
      (source13_5_13 d hA312 hH hU).2.1 (source_seed_centralizer_bound d hA312) g hg hpair

end CFSG.Quasithin.Chapter13.Section05.A5Source
