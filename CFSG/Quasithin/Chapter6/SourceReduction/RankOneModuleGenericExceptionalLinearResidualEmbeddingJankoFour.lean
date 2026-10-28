module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingCatalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.JankoFour
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.SylowOvergroups.PrimeTwentyThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyFour

/-!
# The native J₄ configuration of a proper containing component

Completeness of the actual J₄ carrier realizes conjugation on a normal
J₄ quotient by a surjective homomorphism from the original local group.
Its restriction to the component is exactly the chosen two-core quotient.
The residual quotient and original diagram actor survive because the kernel
on the residual is a two-group. For local-component membership we restrict
first to the containing component, where the quotient kernel is solvable;
Sylow maximality identifies that image Sylow with the full original image.

The resulting J₄ local component has nontrivial two-core, supplying a common
two-local with its full Sylow actor. The actual M₂₄ quotient excludes placement
in every conjugate of the native Mathieu local. Hence the prime-23 placement
theorem shows that this common two-local has order prime to 23.

The last theorem applies the construction to the literal exceptional residual.
This reduces the remaining J₄ row; it does not exclude the other native locals
or prove maximality. The FSU diagram exclusion remains a separate obligation
of the same residual maximality/nonfaithfulness owner.

Source: Aschbacher–Smith A.3.12, 5.1.12 and 5.1.14, printed pp.47–48,
635 and 638 (refs/quasithin.pdf); GLS3 Table 5.3i for the native J₄ locals.
The Mathieu-local transport follows the checked argument in Chapter1's
ExceptionalOvercomponentsJankoFour module, with the literal graph retained.
-/

public noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The original diagram action survives a homomorphism whose kernel on the
normalized subgroup is a two-group. Both conjugation identities are retained. -/
theorem HasLinearFourGraphAction.map_of_two_kernel
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {S K : Subgroup G} (h : HasLinearFourGraphAction S K)
    (hn : S ≤ normalizer (K : Set G)) (f : G →* X)
    (hk : IsPGroup 2 (f.subgroupMap K).ker) :
    HasLinearFourGraphAction (S.map f) (K.map f) := by
  obtain ⟨F,hF,hfin,hcard,e,t,ht,a,b,ha,hb,hd⟩ := h
  let B := K.map f
  let j := MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap K)
    (f.subgroupMap_surjective K) hk
  have hj (k : K) : j (QuotientGroup.mk' (pCore 2 K) k) =
      QuotientGroup.mk' (pCore 2 B) (f.subgroupMap K k) :=
    MonoidHom.quotientPCoreEquivOfSurjective_mk (f.subgroupMap K)
      (f.subgroupMap_surjective K) hk k
  have htN : f t ∈ normalizer (B : Set X) :=
    le_normalizer_map f (mem_map_of_mem f (hn ht))
  let a' := B.normalizerMonoidHom ⟨f t,htN⟩
  have hac (k : K) : a' (f.subgroupMap K k) = f.subgroupMap K (a k) := by
    apply Subtype.ext
    change f t * f k * (f t)⁻¹ = f (a k : G)
    rw [ha]
    simp only [map_mul,map_inv]
  refine ⟨F,hF,hfin,hcard,j.symm.trans e,f t,mem_map_of_mem f ht,a',b,?_,?_,hd⟩
  · intro k
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  · intro k
    obtain ⟨k,rfl⟩ := f.subgroupMap_surjective K k
    rw [hac]
    change e (j.symm (QuotientGroup.mk' _ (f.subgroupMap K (a k)))) =
      b (e (j.symm (QuotientGroup.mk' _ (f.subgroupMap K k))))
    rw [← hj (a k), ← hj k]
    simpa only [j.symm_apply_apply] using hb k

/-- The actual inner realization of a normal J₄ quotient extends its marking
to a surjection on the entire original local overgroup. -/
theorem exists_jankoFour_map_of_normal_quotient
    {Y : Type*} [Group Y] [Finite Y] (C : Subgroup Y) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ∃ f : Y →* Janko4.Model,
      (∀ c : C, f c = e (QuotientGroup.mk' (pCore 2 C) c)) ∧ Function.Surjective f := by
  let j : Janko4.Model ≃* MulAut Janko4.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot,
      Janko4.AdequateLocal.conj_surjective⟩
  let f : Y →* Janko4.Model := j.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (normalQuotientAction C (pCore 2 C)))
  have hf (c : C) : f c = e (QuotientGroup.mk' (pCore 2 C) c) := by
    apply j.injective
    change j (j.symm (MulAut.congr e (normalQuotientAction C (pCore 2 C) c))) = _
    rw [j.apply_symm_apply, normalQuotientAction_inner]
    change MulAut.congr e (MulAut.conj (QuotientGroup.mk' _ c)) =
      MulAut.conj (e (QuotientGroup.mk' _ c))
    ext x : 1
    change e (QuotientGroup.mk' _ c * e.symm x * (QuotientGroup.mk' _ c)⁻¹) = _
    simp only [map_mul,map_inv,e.apply_symm_apply,MulAut.conj_apply]
  refine ⟨f,hf,?_⟩
  intro x
  obtain ⟨c,hc⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 C)) x
  exact ⟨c,(hf c).trans hc⟩

private theorem local_image_of_normal_quotient
    {Y X : Type*} [Group Y] [Finite Y] [Group X] [Finite X]
    (S : Sylow 2 Y) (K C : Subgroup Y) [C.Normal]
    (hK : K ∈ localCComponents S) (hKC : K ≤ C)
    (f : Y →* X) (e : (C ⧸ pCore 2 C) ≃* X)
    (hf : ∀ c : C, f c = e (QuotientGroup.mk' (pCore 2 C) c)) :
    K.map f ∈ localCComponents ((S : Subgroup Y).map f) := by
  let q : C →* X := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal C
  have hl : K.subgroupOf C ∈ localCComponents R := hR.symm ▸ local_restrict hK hKC
  let : Group.IsSolvable q.ker := by
    have he : q.ker = pCore 2 C := by
      ext c
      change e (QuotientGroup.mk' (pCore 2 C) c) = 1 ↔ _
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff c
    rw [he]
    let := pCore_isNilpotent (p := 2) (G := C)
    infer_instance
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hKmap : (K.subgroupOf C).map q = K.map f := by
    ext x
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact ⟨c,hc,hf c⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hKC hk⟩,hk,(hf ⟨k,hKC hk⟩).symm⟩
  have hSmap : (R : Subgroup C).map q = (S : Subgroup Y).map f := by
    symm
    apply (R.mapSurjective hq).is_maximal' (S.isPGroup'.map f)
    rintro x ⟨c,hc,rfl⟩
    have hcS : c ∈ (S : Subgroup Y).subgroupOf C := hR ▸ hc
    exact ⟨c,hcS,hf c⟩
  rwa [hKmap,hSmap] at hlocal

private theorem HasLinearFourGraphAction.exceptionalModel
    {Y : Type*} [Group Y] {S K : Subgroup Y} (hg : HasLinearFourGraphAction S K) :
    Exceptional.IsModel (K ⧸ pCore 2 K) := by
  obtain ⟨F,hF,hfin,hcard,e,_⟩ := hg
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let a : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      Matrix.PSL3Four.card_F])
  exact Or.inr (Or.inr ⟨e.trans (Atlas.fieldEquivPSL 3 a)⟩)

private theorem jankoFour_not_max1_section
    (S : Sylow 2 (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (B : Subgroup (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) ≤
        normalizer (B : Set (Janko4.Cardinality.max1Subgroup
          Janko4.matrixA_mul_self Janko4.matrixB_pow_four)))
    (h : Exceptional.IsModel (B ⧸ pCore 2 B)) : False := by
  let q := QuotientGroup.mk' (Janko4.Cardinality.localKernel
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk', Janko4.LocalStructure.localKernel_eq_twoCore]
    let := pCore_isNilpotent (p := 2) (G := Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    infer_instance
  obtain ⟨hb,hs,hm⟩ := Exceptional.local_section_map hB hn h q
  exact Exceptional.not_mathieu_twentyFour
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) (B.map q) hb hs hm
    (Janko4.LocalStructure.localQuotientEquivM24
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)

/-- The native Mathieu local cannot contain both the residual section and
its full Sylow actor, in any conjugate coordinates. -/
theorem jankoFour_graph_section_not_le_conjugate_max1
    (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (hg : HasLinearFourGraphAction (S : Subgroup Janko4.Model) B)
    (g : Janko4.Model)
    (hS : (S : Subgroup Janko4.Model) ≤
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
        Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom) :
    ¬ B ≤ (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
        Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom := by
  intro hBM
  let C := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let M := C.map (MulAut.conj g).toMonoidHom
  let e : M ≃* C := ((MulAut.conj g).subgroupMap C).symm
  let P := S.subtype hS
  have hl : B.subgroupOf M ∈ localCComponents P := local_restrict hB hBM
  have hnorm : (P : Subgroup M) ≤ normalizer (B.subgroupOf M : Set M) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : Janko4.Model)
  have hm : Exceptional.IsModel ((B.subgroupOf M) ⧸ pCore 2 (B.subgroupOf M)) :=
    hg.exceptionalModel.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBM)))
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  obtain ⟨hl',hn',hm'⟩ := Exceptional.local_section_map hl hnorm hm e.toMonoidHom
  exact jankoFour_not_max1_section (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    ((B.subgroupOf M).map e.toMonoidHom) hl' hn' hm'

/-- The actual common two-local in J₄ has no factor 23: otherwise the
proved native placement forces the already excluded Mathieu local. -/
theorem jankoFour_graph_section_twoLocal_not_twentyThree
    (S : Sylow 2 Janko4.Model) (B N : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (hg : HasLinearFourGraphAction (S : Subgroup Janko4.Model) B)
    (hN : IsTwoLocal N) (hBN : B ≤ N) (hSN : (S : Subgroup Janko4.Model) ≤ N) :
    ¬ 23 ∣ Nat.card N := by
  intro h23
  obtain ⟨g,hNg⟩ := Janko4.SylowOvergroups.twoLocal_le_conjugate_max1_of_twentyThree
    S N hN hSN h23
  exact jankoFour_graph_section_not_le_conjugate_max1 S B hB hn hg g
    (hSN.trans hNg) (hBN.trans hNg)

/-- Construct the native normalized graph section, its nontrivial intrinsic
two-core and a common two-local of order prime to 23. -/
theorem exists_jankoFour_graph_section
    {Y : Type*} [Group Y] [Finite Y]
    (S : Sylow 2 Y) (K C : Subgroup Y) [C.Normal]
    (hK : K ∈ localCComponents S)
    (hn : (S : Subgroup Y) ≤ normalizer (K : Set Y)) (hKC : K ≤ C)
    (hg : HasLinearFourGraphAction (S : Subgroup Y) K)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ∃ (f : Y →* Janko4.Model) (P : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ c : C, f c = e (QuotientGroup.mk' (pCore 2 C) c)) ∧
      (P : Subgroup Janko4.Model) = (S : Subgroup Y).map f ∧
      K.map f ∈ localCComponents P ∧
      (P : Subgroup Janko4.Model) ≤ normalizer (K.map f : Set Janko4.Model) ∧
      HasLinearFourGraphAction (P : Subgroup Janko4.Model) (K.map f) ∧
      pCore 2 (K.map f) ≠ ⊥ ∧
      ∃ N : Subgroup Janko4.Model, IsTwoLocal N ∧ K.map f ≤ N ∧
        (P : Subgroup Janko4.Model) ≤ N ∧ ¬ 23 ∣ Nat.card N := by
  obtain ⟨f,hf,hfs⟩ := exists_jankoFour_map_of_normal_quotient C e
  let P := S.mapSurjective hfs
  have hk : IsPGroup 2 (f.subgroupMap K).ker := by
    have hker : (f.subgroupMap K).ker ≤ (pCore 2 C).comap (inclusion hKC) := by
      intro k hk
      have hfk : f (k : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      change f ((inclusion hKC k : C) : Y) = 1 at hfk
      rw [hf (inclusion hKC k)] at hfk
      change inclusion hKC k ∈ pCore 2 C
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (hfk.trans (map_one e).symm)
    exact (pCore_isPGroup.comap_of_injective (inclusion hKC)
      (inclusion_injective hKC)).to_le hker
  have hl : K.map f ∈ localCComponents P := local_image_of_normal_quotient S K C hK hKC f e hf
  have hnorm : (P : Subgroup Janko4.Model) ≤ normalizer (K.map f : Set Janko4.Model) :=
    (map_mono hn).trans (le_normalizer_map f)
  have hgraph : HasLinearFourGraphAction (P : Subgroup Janko4.Model) (K.map f) :=
    hg.map_of_two_kernel hn f hk
  have hm := hgraph.exceptionalModel
  obtain ⟨N,hN,hBN,hPN⟩ :=
    Exceptional.jankoFour_exists_twoLocal P _ hl hnorm hm (MulEquiv.refl _)
  exact ⟨f,P,hfs,hf,rfl,hl,hnorm,hgraph,
    Exceptional.jankoFour_core_ne_bot P _ hl hnorm hm (MulEquiv.refl _),
    N,hN,hBN,hPN,jankoFour_graph_section_twoLocal_not_twentyThree P _ N
      hl hnorm hgraph hN hBN hPN⟩

/-- Every proper containing component produces a normalized local section
in the native J₄ carrier, retaining the original residual map and graph actor. -/
theorem linear_residual_proper_container_jankoFour_configuration
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H Y : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hnC : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype) (hne : residual H ≠ C.map Y.subtype) :
    ∃ (e : (C ⧸ pCore 2 C) ≃* Janko4.Model)
      (f : Y →* Janko4.Model) (P : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ c : C, f c = e (QuotientGroup.mk' (pCore 2 C) c)) ∧
      (P : Subgroup Janko4.Model) = ((T : Subgroup G).subgroupOf Y).map f ∧
      ((residual H).subgroupOf Y).map f ∈ localCComponents P ∧
      (P : Subgroup Janko4.Model) ≤
        normalizer (((residual H).subgroupOf Y).map f : Set Janko4.Model) ∧
      HasLinearFourGraphAction (P : Subgroup Janko4.Model)
        (((residual H).subgroupOf Y).map f) ∧
      pCore 2 (((residual H).subgroupOf Y).map f) ≠ ⊥ ∧
      ∃ N : Subgroup Janko4.Model, IsTwoLocal N ∧
        ((residual H).subgroupOf Y).map f ≤ N ∧ (P : Subgroup Janko4.Model) ≤ N ∧ ¬ 23 ∣ Nat.card N := by
  obtain ⟨e⟩ := linear_residual_proper_containing_component_jankoFour hG T hTM
    hH hlinear hY C hC hnC hRC hne
  let := hnC
  have hTY : (T : Subgroup G) ≤ Y := hH.1.1.2.trans hY.2
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  let S := T.subtype hTY
  have hr : (residual H).subgroupOf Y ∈ localCComponents S :=
    ((Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp
      ⟨hRY,linear_residual_mem_localFamily hH.1.1 hlinear⟩).1
  have hn : (S : Subgroup Y) ≤
      normalizer ((residual H).subgroupOf Y : Set Y) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp ((hH.1.1.2.trans (le_normalizer_residual H)) hs) (k : G)
  have hKC : (residual H).subgroupOf Y ≤ C := by
    intro k hk
    obtain ⟨c,hc,he⟩ := hRC hk
    exact Y.subtype_injective he ▸ hc
  exact ⟨e,exists_jankoFour_graph_section S _ C hr hn hKC
    ((linear_residual_graph_action T hTM hH hlinear).subgroupOf hTY hRY) e⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
