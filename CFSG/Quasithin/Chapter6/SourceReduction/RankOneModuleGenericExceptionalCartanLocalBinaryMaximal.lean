module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNoncentralExclusion
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

/-!
# Maximality and omega normalizers of the original binary-triality component

Apply the complete original Cartan reduction to every proposed local
component above the selected triality component. The literal residual still
has quotient PSL₂(8), excluding the exceptional PSL₂(4) conclusion. Unique
C-component containment identifies the newly selected triality component
with the proposed overcomponent. Equality of their intrinsic two-core
quotient orders lifts to equality in the original local family.

Thus the SAME original component is maximal, and genuine source 1.2.7
applies to it. It is a normal relative C-component in every local overgroup
of its join with the original full Sylow. In particular it is normal in
the whole omega centralizer, and the normalizer of each nonzero subgroup
of the original omega center normalizes it. No new ambient, quotient,
Hall, module, catalogue or maximality premise is imposed.

The original binary-triality ambient exclusion remains open. These results
do not assert SourceLocalCartanEscape or change its original statement.
The literal chosen-whole-module application is in the corresponding
Chapter12 extension.
Source: Aschbacher--Smith 1.2.4, 1.2.7 and 5.1.13, printed pp.505--506,
635--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem psl_four_not_eight {Q : Type*} [Group Q]
    (h4 : ClassicalGroup.IsPSL Q 2 4) (h8 : ClassicalGroup.IsPSL Q 2 8) : False := by
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := h4
  obtain ⟨E,_,_,hE,⟨eE⟩⟩ := h8
  have hf := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  have he := Atlas.ExceptionalSupport.card_psl_mul (F := E) 2
  rw [hF] at hf
  rw [hE] at he
  norm_num [Fin.prod_univ_two] at hf he
  have hh := Nat.card_congr (eF.symm.trans eE).toEquiv
  omega

omit [Finite G] in
private theorem local_of_component
    {T : Sylow 2 G} {Y : Subgroup G}
    (hY : Y ∈ Chapter1.H G) (hTY : (T : Subgroup G) ≤ Y)
    (C : Subgroup Y) (hC : C.IsCComponent) :
    C.map Y.subtype ∈ Chapter1.L G (T : Subgroup G) := by
  have hc : ((C.map Y.subtype).subgroupOf Y).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hC
  exact Chapter1.mem_L_of_cComponent hY
    ⟨T.subtype hTY,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTY]⟩
    (map_subtype_le C) hc

/-- No local component properly contains the original binary triality component.
The new overgroup is fed to the complete original Cartan reduction, so its
selected component is again triality. Unique containment identifies that
selection with the proposed overcomponent, and local quotient equality lifts. -/
theorem original_binary_triality_overcomponent_eq
    {T : Sylow 2 G} {L W H A B K Y J : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hCJ : C.map Y.subtype ≤ J) :
    C.map Y.subtype = J := by
  let X := C.map Y.subtype
  let P := J ⊔ (T : Subgroup G)
  have hX := local_of_component hY.1 (hH.1.1.2.trans hY.2) C hC
  obtain ⟨hKR,_,hr⟩ := LocalSieve.binaryTriality_residual_section h.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,hAC,_,_,_,_⟩ := original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hKP : K ≤ P := hKC.trans (hCJ.trans le_sup_left)
  have hHP : H ≤ P := by
    rw [←hKT]
    exact sup_le hKP le_sup_right
  have hP : P ∈ Chapter1.HOver G (H : Set G) := ⟨hJ.2.2,hHP⟩
  have hAP : A ≤ P := hAC.trans (hCJ.trans le_sup_left)
  have hescP : ¬ A ⊓ P ≤ normalizer (residual H : Set G) := by
    intro hh
    exact hescape ((le_inf inf_le_left (inf_le_left.trans hAP)).trans hh)
  rcases localCartan_escape_binary_or_exceptional h hH hgen c hP hescP with
    ⟨_,_,hfour,_⟩ | ⟨K₀,_,_,_,_,_,_,C₀,hC₀,_,hK₀C,_,_,_,_,hK₀R,hbin⟩
  · exact (psl_four_not_eight hfour hr).elim
  obtain ⟨_,_,hm₀,_⟩ := hbin
  have hKC₀ : K.subgroupOf P ≤ C₀ := by
    change K.comap P.subtype ≤ C₀
    have hle : K ≤ C₀.map P.subtype := by rwa [hKR,←hK₀R]
    have hh := comap_mono (f := P.subtype) hle
    simpa only [comap_map_eq_self_of_injective P.subtype_injective] using hh
  have hKin : K.subgroupOf P ∈ Chapter1.L P (T.subtype (show (T : Subgroup G) ≤ P from le_sup_right)) :=
    (Chapter1.mem_LIn_iff_subgroupOf le_sup_right hKP).mp ⟨hKP,hK⟩
  obtain ⟨D,_,hu⟩ := Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
    (Chapter1.Section02.containment_of_theoremsAC
      (fun Q _ _ => ChapterA.Section02.theoremA_knownSimple (G := Q))
      (fun Q _ _ => ChapterA.Section02.theoremC_knownSimple (G := Q)))
    (Chapter1.Section02.uniqueness_local_quotient_sqtk h.qtke hP.1)
    (T.subtype le_sup_right) hKin
  have he : J.subgroupOf P = C₀ :=
    (hu (J.subgroupOf P) ⟨hJ.1,comap_mono (hKC.trans hCJ)⟩).trans
      (hu C₀ ⟨hC₀,hKC₀⟩).symm
  have hemap : C₀.map P.subtype = J := by
    rw [←he,map_subgroupOf_eq_of_le (show J ≤ P from le_sup_left)]
  let a : C₀ ≃* J := (C₀.equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hemap)
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b : C ≃* X := C.equivMapOfInjective Y.subtype Y.subtype_injective
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  obtain ⟨e₀⟩ := (Triality.Standard.isTrialityGroupAt_two_iff _).mp hm₀
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff _).mp hm
  have hc : Nat.card (J ⧸ pCore 2 J) = Nat.card (X ⧸ pCore 2 X) :=
    Nat.card_congr ((aq.symm.trans e₀).trans (bq.symm.trans e).symm).toEquiv
  exact ChapterA.Section03.SourceEmbeddings.BinaryNested.local_eq_of_twoCore_card_le
    T hX.1 hJ.1 hCJ hc.le


/-- The SAME original triality component is maximal in the full local family.
No exceptional or larger-triality component is substituted for it. -/
theorem original_binary_triality_maximal
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    C.map Y.subtype ∈ Chapter1.LStar G (T : Subgroup G) := by
  refine ⟨local_of_component hY.1 (hH.1.1.2.trans hY.2) C hC,?_⟩
  intro J hJ hCJ
  exact (original_binary_triality_overcomponent_eq
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm hJ hCJ).symm

private theorem maximal_normal_component_in_overgroup
    {T : Sylow 2 G} {X P : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hX : X ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hP : P ∈ Chapter1.HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G)) :
    (X.subgroupOf P).IsCComponent ∧ (X.subgroupOf P).Normal ∧
      P ≤ normalizer (X : Set G) := by
  have hXP : X ≤ P := le_sup_left.trans hP.2
  have hTP : (T : Subgroup G) ≤ P := le_sup_right.trans hP.2
  let S := T.subtype hTP
  have hx : X.subgroupOf P ∈ Chapter1.L P (S : Subgroup P) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTP hXP).mp ⟨hXP,hX.1⟩
  have hs : (S : Subgroup P) ≤ normalizer (X.subgroupOf P : Set P) := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hXP]
    exact comap_mono hn
  obtain ⟨D,⟨hD,hXD,hDn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hP.1) S hx hs
  have hDX : D.map P.subtype = X := hX.2 _
    (local_of_component hP.1 hTP D hD) (by
      simpa only [map_subgroupOf_eq_of_le hXP] using map_mono (f := P.subtype) hXD)
  have hEq : X.subgroupOf P = D := by
    rw [←hDX]
    exact comap_map_eq_self_of_injective P.subtype_injective D
  have hnorm : (X.subgroupOf P).Normal := hEq.symm ▸ hDn
  exact ⟨hEq.symm ▸ hD,hnorm,(normal_subgroupOf_iff_le_normalizer hXP).mp hnorm⟩

/-- Every local overgroup of the original component and full Sylow normalizes
that same component. This uses its newly proved maximality, not an assumed
maximal containing row. -/
theorem original_binary_triality_overgroup_control
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype
    Chapter1.Section02.NonsolvableUniquenessConclusion T X ∧
      ∀ P ∈ Chapter1.HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G),
        (X.subgroupOf P).IsCComponent ∧ (X.subgroupOf P).Normal ∧
          P ≤ normalizer (X : Set G) := by
  let X := C.map Y.subtype
  have hmax := original_binary_triality_maximal
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hCn := (LocalSieve.binaryTriality_seed_eq_residual_and_normal h.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm).2
  have hCnY : (X.subgroupOf Y).Normal := by
    simpa only [X,subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hTN : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (hH.1.1.2.trans hY.2).trans
      ((normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp hCnY)
  exact ⟨Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hmax,
    fun P hP => maximal_normal_component_in_overgroup h.qtke hmax hTN hP⟩

/-- The original component itself is normal in the whole omega centralizer.
Moreover, the normalizer of every nonzero subgroup of the original omega
center normalizes this same component. The literal quotient model is retained. -/
theorem original_binary_triality_omega_normalizers
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype
    residual H ≤ X ∧ X ≤ omegaCentralizer T ∧
      (X.subgroupOf (omegaCentralizer T)).IsCComponent ∧
      (X.subgroupOf (omegaCentralizer T)).Normal ∧
      Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X) ∧
      ∀ Z₀ : Subgroup G, Z₀ ≤ omegaOneCenterAmbient (T : Subgroup G) → Z₀ ≠ ⊥ →
        normalizer (Z₀ : Set G) ≤ normalizer (X : Set G) := by
  let X := C.map Y.subtype
  have hXC := original_container_centralizes
    h hH c hKH hK hKT horbit hY hescape C hC hKC hm
  have hKR := (LocalSieve.binaryTriality_seed_eq_residual_and_normal h.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm).1
  have hRX : residual H ≤ X := hKR ▸ hKC
  have hP := omegaCentralizer_mem_HOver_of_residual hH.1.1 (hRX.trans hXC)
  have hc := (original_binary_triality_overgroup_control
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2
  obtain ⟨hcomp,hnorm,_⟩ := hc (omegaCentralizer T)
    ⟨hP.1,sup_le hXC sylow_le_omegaCentralizer⟩
  let e := C.equivMapOfInjective Y.subtype Y.subtype_injective
  let eqv := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine ⟨hRX,hXC,hcomp,hnorm,hm.of_mulEquiv eqv.symm,?_⟩
  intro Z₀ hZ hZ0
  have hZp : IsPGroup 2 Z₀ :=
    (omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)).isPGroup.to_le hZ
  have hZN : Z₀ ≤ (normalizer (Z₀ : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hZp Z₀.le_normalizer le_rfl
  have hN : normalizer (Z₀ : Set G) ∈ Chapter1.H G :=
    fun hz => hZ0 (bot_unique (hZN.trans_eq hz))
  have hCN : omegaCentralizer T ≤ normalizer (Z₀ : Set G) :=
    (centralizer_le hZ).trans (Subgroup.centralizer_le_normalizer _)
  exact (hc _ ⟨hN,(sup_le hXC sylow_le_omegaCentralizer).trans hCN⟩).2.2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
