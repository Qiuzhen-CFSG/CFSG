module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentRankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SpecialLinearThreeLocalQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# Split rank-two overcomponents of the original source component

A proper local component inside a containing component with binary SL₃,
PSL₃, Sp₄ or G₂ two-core quotient has a PSL₂ two-core quotient over the
same field. Restrict the original full Sylow to the containing component,
project through its literal two-core, and use the two actual parabolic
residuals of the concrete model. Equality is reflected through the
projection, so the image stays proper.

The previously proved PSL₂ exclusions therefore force equality for Suzuki
and higher-rank seeds. Suzuki and unitary seeds cannot equal a split model:
two proper parabolics contain the same full Sylow and generate the whole
split group, whereas a Bender model has a unique maximal Sylow overgroup.
For a unitary star image, perfectness reflects properness through the
actual central cover; no identification of that image with K/O₂(K) is assumed.

The final theorem applies these comparisons to the original component
catalogue, with every source quotient and independent field exponent
retained. Other containing models and the FF exclusions, elementary
full-root lifting, and the paired/doubled-SL₃ assembly remain necessary.

Source: Aschbacher–Smith A.3.12(1–2), printed pp.47–48, and the embedding
argument in 11.3.5(1), pp.771–772. Concrete parabolic results are imported
from the existing source/ATLAS ports with their attribution retained.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- Transport a proper original local component through the containing
component's literal two-core quotient, retaining its own quotient and a
full Sylow subgroup in the containing model. -/
theorem Models.proper_local_quotient_image {X Y : Type*}
    [Group X] [Finite X] [Group Y] [Finite Y]
    (T : Sylow 2 X) {B J : Subgroup X}
    (hB : B ∈ localCComponents T) (hJ : J ∈ localCComponents T)
    (hBJ : B < J) (e : (J ⧸ pCore 2 J) ≃* Y) :
    ∃ (P : Sylow 2 Y) (C : Subgroup Y), C ∈ localCComponents P ∧ C ≠ ⊤ ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* (C ⧸ pCore 2 C)) := by
  obtain ⟨S,_,hlocal⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hJ hBJ.le
  let D := B.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent f.ker := (hk ▸ (pCore_isPGroup (p := 2) (G := J))).isNilpotent
  have ht : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.subgroupOf_of_le le_rfl le_sup_left
  let P := S.mapSurjective (f := f) hf
  let C := D.map f
  have hproper : C ≠ ⊤ := by
    intro he
    have heq : D.map q = (⊤ : Subgroup J).map q := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_map,map_map,map_top_of_surjective f hf]
      exact he
    have hD := local_cComponent_eq_of_map_eq hlocal ht le_top q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S) heq
    exact hBJ.not_ge (subgroupOf_eq_top.mp hD)
  let d := subgroupOfEquivOfLe hBJ.le
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hker : IsPGroup 2 (f.subgroupMap D).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let a := (f.subgroupMap D).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective D) hker
  exact ⟨P,C,Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f,
    hproper,⟨dq.symm.trans a⟩⟩

private theorem projective_three_local_quotient {F : Type*}
    [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (P : Sylow 2 PSL(3,F)) (C : Subgroup PSL(3,F))
    (hC : C ∈ localCComponents P) (hp : C ≠ ⊤) :
    Nonempty ((C ⧸ pCore 2 C) ≃* SL(2,F)) := by
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hf P C hC hp
  let a := (MulAut.conj g).subgroupMap C
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  suffices h : Nonempty (((C.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (C.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) from ⟨aq.trans h.some⟩
  rcases hg with hg | hg
  · rw [hg]
    exact ⟨Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F⟩
  · rw [hg]
    exact ⟨Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F⟩

private theorem symplectic_local_quotient {F : Type*}
    [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (P : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (C : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hC : C ∈ localCComponents P) (hp : C ≠ ⊤) :
    Nonempty ((C ⧸ pCore 2 C) ≃* SL(2,F)) := by
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hf P C hC hp
  let a := (MulAut.conj g).subgroupMap C
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  suffices h : Nonempty (((C.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (C.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) from ⟨aq.trans h.some⟩
  rcases hg with hg | hg
  · rw [hg]
    exact ⟨Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hf⟩
  · rw [hg]
    exact ⟨Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hf⟩

private theorem g2_local_quotient {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (P : Sylow 2 (Atlas.G2.Model F))
    (C : Subgroup (Atlas.G2.Model F))
    (hC : C ∈ localCComponents P) (hp : C ≠ ⊤) :
    Nonempty ((C ⧸ pCore 2 C) ≃* SL(2,F)) := by
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hF P C hC hp
  let a := (MulAut.conj g).subgroupMap C
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  suffices h : Nonempty (((C.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (C.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) from ⟨aq.trans h.some⟩
  rcases hg with hg | hg
  · rw [hg]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
        Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL⟩
  · rw [hg]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      Atlas.G2.LieParabolicSetup.local₂_pCore).trans
        Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- A proper seed in any of the four split rank-two containing models has
the binary PSL₂ quotient at the containing model's actual field exponent. -/
theorem ComponentSeed.linear_model_of_proper_split_overcomponent (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K < J)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ f) ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  have hB := (s.mem_local_family h).1
  rcases hm with hm | hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨P,C,hC,hp,⟨a⟩⟩ := Models.proper_local_quotient_image T hB hJ.1 hKJ e
    obtain ⟨b⟩ := special_linear_three_local_core_quotient hF (by omega) P C hC hp
    exact ⟨F,inferInstance,inferInstance,hF,⟨(a.trans b).trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨P,C,hC,hp,⟨a⟩⟩ := Models.proper_local_quotient_image T hB hJ.1 hKJ e
    obtain ⟨b⟩ := projective_three_local_quotient hF (by omega) P C hC hp
    exact ⟨F,inferInstance,inferInstance,hF,⟨(a.trans b).trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let e' := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    obtain ⟨P,C,hC,hp,⟨a⟩⟩ := Models.proper_local_quotient_image T hB hJ.1 hKJ e'
    obtain ⟨b⟩ := symplectic_local_quotient hF (by omega) P C hC hp
    exact ⟨F,inferInstance,inferInstance,hF,⟨(a.trans b).trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨P,C,hC,hp,⟨a⟩⟩ := Models.proper_local_quotient_image T hB hJ.1 hKJ e
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (by decide : 2 < 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hf)
    obtain ⟨b⟩ := g2_local_quotient hlarge P C hC hp
    exact ⟨F,inferInstance,inferInstance,hF,⟨(a.trans b).trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩

/-- The Suzuki seed cannot be a proper local component of a split model. -/
theorem ComponentSeed.eq_split_overcomponent_of_suzuki
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    {f : ℕ} (hf : 2 ≤ f)
    (hmodel : Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ f) ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f)) : K = J := by
  by_contra hne
  exact s.not_linear_overcomponent_of_suzuki h (s.mem_local_family h) le_rfl hm he f hf
    (s.linear_model_of_proper_split_overcomponent h hJ (lt_of_le_of_ne hKJ hne) hf hmodel)

/-- A seed with a higher-rank star image cannot be properly enlarged inside
a split rank-two containing model, even at an independent exponent. -/
theorem ComponentSeed.eq_split_overcomponent_of_higher_rank_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n))
    {f : ℕ} (hf : 2 ≤ f)
    (hmodel : Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ f) ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f)) : K = J := by
  by_contra hne
  exact s.not_linear_overcomponent_of_higher_rank_image h (s.mem_local_family h) le_rfl
    R hR hn hm f hf (s.linear_model_of_proper_split_overcomponent h hJ
      (lt_of_le_of_ne hKJ hne) hf hmodel)

omit [Finite G] in
private theorem not_bender_of_parabolic_pair {X : Type*} [Group X]
    (P : Sylow 2 X) (A B : Subgroup X) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hPA : (P : Subgroup X) ≤ A) (hPB : (P : Subgroup X) ≤ B)
    (hgen : A ⊔ B = ⊤) : ¬ ClassificationModels.IsBenderModel X := by
  intro hm
  have hf := ChapterE.Structure.bender_sylow_facts hm P
  apply hf.proper.ne
  apply top_unique
  rw [←hgen]
  exact sup_le (hf.unique_maximal A hPA (lt_top_iff_ne_top.mpr hA))
    (hf.unique_maximal B hPB (lt_top_iff_ne_top.mpr hB))

private theorem parabolic_pair_transport {X Y : Type*} [Group X] [Finite X] [Group Y]
    (e : X ≃* Y) (P : Sylow 2 X) (A B : Subgroup X)
    (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hPA : (P : Subgroup X) ≤ A) (hPB : (P : Subgroup X) ≤ B)
    (hgen : A ⊔ B = ⊤) :
    ∃ (Q : Sylow 2 Y) (U W : Subgroup Y), U ≠ ⊤ ∧ W ≠ ⊤ ∧
      (Q : Subgroup Y) ≤ U ∧ (Q : Subgroup Y) ≤ W ∧ U ⊔ W = ⊤ := by
  have hproper (C : Subgroup X) (hC : C ≠ ⊤) : C.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hC
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [he,map_top_of_surjective _ e.surjective]
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,
    A.map e.toMonoidHom,B.map e.toMonoidHom,hproper A hA,hproper B hB,
    map_mono hPA,map_mono hPB,?_⟩
  rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ e.surjective]

private theorem split_parabolic_pair {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hf : 2 ≤ f)
    (hm : Source.IsSL X 3 (2 ^ f) ∨ ClassicalGroup.IsPSL X 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp X 2 (2 ^ f) ∨ ClassificationModels.IsG2At X (2 ^ f)) :
    ∃ (P : Sylow 2 X) (A B : Subgroup X), A ≠ ⊤ ∧ B ≠ ⊤ ∧
      (P : Subgroup X) ≤ A ∧ (P : Subgroup X) ≤ B ∧ A ⊔ B = ⊤ := by
  rcases hm with hm | hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact parabolic_pair_transport e.symm (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F (by omega) hF)
      _ _ (Matrix.PSL3.LinearThree.pointParabolicSL_isCoatom F).ne_top
      (Matrix.PSL3.LinearThree.lineParabolicSL_isCoatom F).ne_top
      ((Matrix.PSL3.LinearThree.unipotentSL_le_borelSL F).trans inf_le_left)
      ((Matrix.PSL3.LinearThree.unipotentSL_le_borelSL F).trans inf_le_right)
      (Matrix.PSL3.LinearThree.parabolicsSL_sup_eq_top F)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact parabolic_pair_transport e.symm (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
      _ _ (Matrix.PSL3.LinearThree.projective_parabolics_isCoatom F).1.ne_top
      (Matrix.PSL3.LinearThree.projective_parabolics_isCoatom F).2.ne_top
      ((Matrix.PSL3.LinearThree.unipotent_le_borel F).trans
        ((Matrix.PSL3.LinearThree.projective_parabolics_inf F) ▸ inf_le_left))
      ((Matrix.PSL3.LinearThree.unipotent_le_borel F).trans
        ((Matrix.PSL3.LinearThree.projective_parabolics_inf F) ▸ inf_le_right))
      (Matrix.PSL3.LinearThree.parabolics_sup_eq_top F)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact parabolic_pair_transport
      ((Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).trans e.symm)
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega))
      _ _ Theory.SpecificGroups.SymplecticFour.pointParabolic_ne_top
      Theory.SpecificGroups.SymplecticFour.planeParabolic_ne_top
      (Theory.SpecificGroups.SymplecticFour.unipotent_le_borel.trans inf_le_left)
      (Theory.SpecificGroups.SymplecticFour.unipotent_le_borel.trans inf_le_right)
      Theory.SpecificGroups.SymplecticFour.parabolics_sup_eq_top
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact parabolic_pair_transport e.symm (Atlas.G2.LieParabolicSetup.sylow (F := F))
      _ _ Atlas.G2.HigherFieldResiduals.parabolic₁_isCoatom.ne_top
      Atlas.G2.HigherFieldResiduals.parabolic₂_isCoatom.ne_top
      ((show Atlas.G2.unipotent ≤ Atlas.G2.borel from le_sup_left).trans
        Atlas.G2.LieParabolicSetup.borel_le_parabolic₁)
      ((show Atlas.G2.unipotent ≤ Atlas.G2.borel from le_sup_left).trans
        Atlas.G2.LieParabolicSetup.borel_le_parabolic₂)
      Atlas.G2.LieParabolicSetup.parabolics_generate

private theorem split_not_bender {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hf : 2 ≤ f)
    (hm : Source.IsSL X 3 (2 ^ f) ∨ ClassicalGroup.IsPSL X 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp X 2 (2 ^ f) ∨ ClassificationModels.IsG2At X (2 ^ f)) :
    ¬ ClassificationModels.IsBenderModel X := by
  obtain ⟨P,A,B,hA,hB,hPA,hPB,hgen⟩ := split_parabolic_pair hf hm
  exact not_bender_of_parabolic_pair P A B hA hB hPA hPB hgen

private theorem split_not_bender_central_image {X Y : Type*}
    [Group X] [Finite X] [Group.IsPerfect X] [Group Y]
    (q : X →* Y) (hq : Function.Surjective q) (hk : q.ker ≤ center X)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : Source.IsSL X 3 (2 ^ f) ∨ ClassicalGroup.IsPSL X 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp X 2 (2 ^ f) ∨ ClassificationModels.IsG2At X (2 ^ f)) :
    ¬ ClassificationModels.IsBenderModel Y := by
  obtain ⟨P,A,B,hA,hB,hPA,hPB,hgen⟩ := split_parabolic_pair hf hm
  have hproper (C : Subgroup X) (hC : C ≠ ⊤) : C.map q ≠ ⊤ := by
    intro he
    apply hC
    apply top_unique
    apply le_of_map_le_of_perfect q hk ⊤ C
    rw [he]
    exact le_top
  apply not_bender_of_parabolic_pair (P.mapSurjective hq) (A.map q) (B.map q)
    (hproper A hA) (hproper B hB) (map_mono hPA) (map_mono hPB)
  rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ hq]

/-- A Suzuki seed has no split rank-two containing quotient, including equality. -/
theorem ComponentSeed.not_split_overcomponent_of_suzuki
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    {f : ℕ} (hf : 2 ≤ f) :
    ¬ (Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ f) ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f)) := by
  intro hmodel
  have hsame := s.eq_split_overcomponent_of_suzuki h hJ hKJ hm he hf hmodel
  subst J
  exact split_not_bender hf hmodel (.suzuki m hm he)

/-- A unitary star image excludes every split rank-two containing quotient;
the comparison uses the original central star projection. -/
theorem ComponentSeed.not_split_overcomponent_of_unitary_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n))
    {f : ℕ} (hf : 2 ≤ f) :
    ¬ (Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ f) ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f)) := by
  intro hmodel
  have hsame := s.eq_split_overcomponent_of_higher_rank_image h hJ hKJ R hR hn
    (.inl hm) hf hmodel
  subst J
  let B := K.subgroupOf H
  let e := s.intrinsicQuotientEquiv
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e
  let q := Models.starCover B R s.component.2 hR
  have hmodelB : Source.IsSL (B ⧸ pCore 2 B) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp (B ⧸ pCore 2 B) 2 (2 ^ f) ∨
      ClassificationModels.IsG2At (B ⧸ pCore 2 B) (2 ^ f) := by
    rcases hmodel with hm | hm | hm | hm
    · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
      exact .inl ⟨F,hF,hfin,hcard,⟨e.symm.trans a⟩⟩
    · exact .inr (.inl (hm.of_mulEquiv e.symm))
    · exact .inr (.inr (.inl (hm.of_mulEquiv e.symm)))
    · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
      exact .inr (.inr (.inr ⟨F,hF,hfin,hcard,⟨e.symm.trans a⟩⟩))
  exact split_not_bender_central_image q.toMonoidHom q.surjective q.ker_le_center hf
    hmodelB (.unitary n hn hm)

/-- The original catalogue with split rank-two comparisons: all four containing
models are excluded for Suzuki and unitary seeds, and force equality for the
linear-three and symplectic-four seeds. The generation minimum is unchanged. -/
theorem exists_componentSeed_with_split_overcomponent_sieve
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      (((∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∧
          solvableRadical H = pCore 2 H) ∨
        (Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          (∀ f : ℕ, 2 ≤ f → ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2 ^ f)) ∧
          (((∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
              solvableRadical H = pCore 2 H ∧
              (∀ f : ℕ, 2 ≤ f → ¬ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ f)) ∧
              (∀ d : ℕ, 2 ≤ d → ¬ (Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ d) ∨
                  ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ d) ∨
                  ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ d) ∨
                  ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ d)))) ∨
            ((K.subgroupOf H).Normal ∧ (T : Subgroup G) ≤ normalizer (J : Set G) ∧
              (∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W)) ∧
              (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
               ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
                 ((ClassicalGroup.IsPSU I 3 (2 ^ f) ∧
                    (∀ m : ℕ, 1 ≤ m → ¬ Nonempty
                      ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
                    (ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) →
                      K = J ∧ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ f)) ∧
                    (∀ d : ℕ, 2 ≤ d → ¬ (Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ d) ∨
                  ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ d) ∨
                  ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ d) ∨
                  ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ d)))) ∨
                  ((ClassicalGroup.IsPSL I 3 (2 ^ f) ∨ ClassicalGroup.IsPSp I 2 (2 ^ f)) ∧
                    ¬ ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) ∧
                    (∀ d : ℕ, 2 ≤ d → (Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ d) ∨
                  ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ d) ∨
                  ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ d) ∨
                  ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ d)) → K = J)))))))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hcases⟩ :=
    exists_componentSeed_with_bender_overcomponent_sieve h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  rcases hcases with hlin | ⟨hsource,hnlin,hcases⟩
  · exact .inl hlin
  refine .inr ⟨hsource,hnlin,?_⟩
  rcases hcases with ⟨⟨m,hm,hbound,he⟩,hrad,hnuni⟩ |
      ⟨hn,hTJ,hchosen,n,hnn,hbound,hmodels⟩
  · exact .inl ⟨⟨m,hm,hbound,he⟩,hrad,hnuni,
      fun _ hf => s.not_split_overcomponent_of_suzuki h hJ.1 hKJ hm he hf⟩
  · let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let R := ChapterB.minimalParabolicCore P hP
    let : IsSimpleGroup ((K.subgroupOf H).map (QuotientGroup.mk' R)) :=
      (ChapterE.Structure.source_component_simple_image P hP
        (counterexample_not_solvable h pr hc hs) (K.subgroupOf H) s.component.2
        (s.intrinsic_supplement h.outside.1.1.2)).1
    have hR := ChapterB.minimalParabolicTwoCore_le_core P hP
    refine .inr ⟨hn,hTJ,hchosen,n,hnn,hbound,?_⟩
    rcases hmodels with ⟨huni,hnsuz,hb⟩ | ⟨htwo,hnben⟩
    · exact .inl ⟨huni,hnsuz,hb,
        fun _ hf => s.not_split_overcomponent_of_unitary_image h hJ.1 hKJ R hR hnn huni hf⟩
    · exact .inr ⟨htwo,hnben,fun _ hf hsplit =>
        s.eq_split_overcomponent_of_higher_rank_image h hJ.1 hKJ R hR hnn (.inr htwo) hf hsplit⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
