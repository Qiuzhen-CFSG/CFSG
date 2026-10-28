module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.G2Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.MaximalFaithfulSp4

/-!
# Faithful maximality of the original G₂ third vertex

A central seed in the original natural module lies in its first flag line.
Strictness of the first component kills the fixed layer, so L₂ moves the
Sylow omega-center and I = K₀ ∨ L₂ is faithful. The full three-model
recognition and both marked locals exclude every strict maximal envelope.
This constructs a chosen module of the same join without a naturality premise.
The nontrivial common normal Q remains explicit.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764.
-/

open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
open ChapterA.Section04 Chapter1.Section02.Adequate
public noncomputable section
variable {G : Type*} [Group G] [Finite G]
private theorem local_faithful_of_sylow_center_movement
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T) {I : Subgroup G}
    (hI : I ∈ Chapter1.L G T)
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (hm : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (I : Set G)) :
    I ∈ MainForward.faithfulLocalComponents T := by
  let J := I ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hJ : J ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T hE ⟨hI.2.2,fun _ hx => (show (T : Subgroup G) ≤ J from le_sup_right) hx⟩
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hJI : J ≤ normalizer (I : Set G) := sup_le I.le_normalizer hTI
  have hJQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hIQ : I.pCoreIn 2 ≤ Q := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    ((pCoreIn_le 2 I).trans le_sup_left)
    (hJI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hcomm : ⁅I,Q⁆ ≤ I.pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show I ≤ J from le_sup_left))
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hQT.trans hTI))
      (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hJQ))
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ omegaOneCenterAmbient Q := by
    intro z hz
    obtain ⟨hzT,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hJ ⟨hTJ hzT,fun q hq => hzc q (hQT hq)⟩,hz2,
      fun q hq => hzc q (hQT hq)⟩
  apply (mem_faithfulLocalComponents_iff_module T hE).mpr
  refine ⟨hI,?_⟩
  intro he
  have hs := signalizerModule_le_intrinsicModule I Q (mem_L_isPPerfect hI)
    (le_sup_left.trans hJQ) hIQ hcomm
  rw [signalizerModule_eq_commutator_omegaCenter,he] at hs
  apply hm
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact bot_unique ((commutator_mono le_rfl hZ).trans hs)

private theorem exists_central_seed (T : Sylow 2 G) {V : Subgroup G}
    (hVT : V ≤ (T : Subgroup G)) (hn : (T : Subgroup G) ≤ normalizer (V : Set G))
    [IsElementaryAbelian 2 V] (hV : V ≠ ⊥) :
    ∃ z : G, z ∈ V ∧ z ≠ 1 ∧ z ∈ omegaOneCenterAmbient (T : Subgroup G) := by
  let B := V.subgroupOf (T : Subgroup G)
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  have hB : B ≠ ⊥ := by
    intro he
    apply hV
    have hh := congrArg (map (T : Subgroup G).subtype) he
    simpa only [B,map_subgroupOf_eq_of_le hVT,Subgroup.map_bot] using hh
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨z,hzne,hzc⟩ := exists_nontrivial_center_mem_normal B (p := 2)
  refine ⟨z.val.val,z.property,?_,?_⟩
  · intro he
    exact hzne (Subtype.ext (Subtype.ext he))
  · apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨z.val.property,elemPow_eq_one_of_isElementaryAbelian (p := 2) _ z.property,?_⟩
    intro t ht
    exact congrArg (fun a : T => (a : G)) ((mem_center_iff.mp hzc) ⟨t,ht⟩)

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (.g2 m))

/-- The original second residual moves the Sylow omega-center. -/
theorem g2_second_moves_sylow_center
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfaith : V ⊓ centralizer (L : Set G) = ⊥) :
    ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (f.Li 1 : Set G) := by
  have he (i : Fin 3) : f.space i = (LocalGeometry.G2.flag S m).space i :=
    LocalGeometry.G2.flag_inner_unique S m i (f.space i) (f.dimension i)
      (inf_le_left.trans (f.invariant i))
  have hv (i : Fin 3) : f.Vi i = (LocalGeometry.G2.flag S m).Vi i :=
    congrArg (Coordinates.preimage (.g2 m)) (he i)
  have hr (i : Fin 2) : f.Li i = (LocalGeometry.G2.flag S m).Li i :=
    congrArg (localResidual L) (hv i.castSucc)
  have hgen : f.Li 0 ⊔ f.Li 1 = L := by
    rw [hr 0,hr 1]
    exact LocalGeometry.G2.ResidualIncidence.flag_Li_sup S m
  let := D.elementary
  obtain ⟨z,hzV,hzne,hzZ⟩ := exists_central_seed T D.le_sylow S.sylow_normalizes D.ne_bot
  have hzfirst : z ∈ f.Vi 0 := by
    rw [hv 0]
    apply G2.inner_fixed_le_first S m
    refine ⟨hzV,?_⟩
    intro t ht
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hzZ).2.2 t ht.1
  intro hm
  have hzL : z ∈ centralizer (L : Set G) := by
    have hzA : f.Li 0 ≤ centralizer ({z} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (hfix ha z hzfirst).symm
    have hzB : f.Li 1 ≤ centralizer ({z} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hm hzZ b hb)
    intro l hl
    exact (mem_centralizer_singleton_iff.mp ((sup_le hzA hzB) (hgen.symm ▸ hl)))
  exact hzne (mem_bot.mp (hfaith ▸ (show z ∈ V ⊓ centralizer (L : Set G) from ⟨hzV,hzL⟩)))

/-- Sylow-center movement makes the literal local join faithful, without
a model recognition or an assumed natural action on that join. -/
theorem g2_triangle_join_faithful
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfaith : V ⊓ centralizer (L : Set G) = ⊥)
    {K₀ : Subgroup G} (hI : K₀ ⊔ f.Li 1 ∈ Chapter1.L G T)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G)) :
    K₀ ⊔ f.Li 1 ∈ MainForward.faithfulLocalComponents T := by
  apply local_faithful_of_sylow_center_movement T (S.source.simpleQTKE.evenCharacteristic T) hI
    ((le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup K₀ (f.Li 1)))
  intro h
  exact g2_second_moves_sylow_center D S m f hfix hfaith
    (h.trans (centralizer_le (show f.Li 1 ≤ K₀ ⊔ f.Li 1 from le_sup_right)))

/-- In the actual strict G₂ triangle, the common-normal construction
produces a faithful local component, with the original Cartan and three-ranks.
The fixed-free condition is proved from strictness, not supplied by the caller.
The source amalgam argument still has to supply Q. -/
theorem g2_triangle_join_faithful_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      (K₀ ⊔ f.Li 1) ∈ MainForward.faithfulLocalComponents T ∧
      X ≤ K₀ ⊔ f.Li 1 ∧ primeRank 3 (K₀ ⊔ f.Li 1 : Subgroup G) = 2 ∧
      primeRank 3 ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) = 2 := by
  obtain ⟨hI,hIL,hIH,_⟩ := triangle_join_component_of_common_normal_projective
    D S f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hfaith := first_strict_fixed_layer_eq_bot D S f hm₁ hfix hK.1 hLK
  have hf := g2_triangle_join_faithful D S m f hfix hfaith hIL hTK₀
  obtain ⟨hr,hrq⟩ := g2_triangle_join_three_rank D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp hQ hQT hKQ hLQ
  exact ⟨hI,hIL,hIH,hf,g2_triangle_cartan_le_join D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp,hr,hrq⟩

/-- The same original join and marked locals determine its maximal envelope. -/
theorem g2_triangle_reselection_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    (∃ W : Subgroup G, Nonempty (ChosenModule T I W)) ∧
      (FaithfulMaximalLocal T I ∨
        ∃ J : Subgroup G, I < J ∧
          (T : Subgroup G) ≤ normalizer (J : Set G) ∧
          Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          FieldFourOvergroup (J ⧸ pCore 2 J) ∧
          ∃ W : Subgroup G, Nonempty (ChosenModule T J W)) := by
  intro I
  obtain ⟨_,hIL,_,hf,_,hr,_⟩ := g2_triangle_join_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hq,hm⟩ := g2_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    (le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup K₀ (f.Li 1))
  refine ⟨exists_chosen_of_normalized_faithful hIL hf.2 hq hTI,?_⟩
  obtain ⟨J,hIJ,hTJ,hsource,hchosen⟩ := exists_maximal_faithful_envelope S.source hIL hf hTI hr.ge
  by_cases he : I = J
  · exact .inl (he ▸ hsource.maximal_faithful)
  have hlt : I < J := lt_of_le_of_ne hIJ he
  refine .inr ⟨J,hlt,hTJ,hsource,?_,hchosen⟩
  have hJ := hsource.maximal_faithful.1.1
  let H := J ⊔ (T : Subgroup G)
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    have hh := (S.source.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal N from ⟨R,hJ.2.2,isPGroup_pCoreIn 2 H,rfl⟩)).subgroup
      (H.subgroupOf N)
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hh
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) H := by
    refine ⟨T.subtype le_sup_right,?_⟩
    simp only [Sylow.coe_subtype]
    exact map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
  have hB := flag_mem_local_of_model D S f 1 hm₂
  have hcase := Embedding.relative_component_alternative hH hP hB
    (show Source.ComponentIn H J from ⟨le_sup_left,hJ.1⟩)
    ((show f.Li 1 ≤ I from le_sup_right).trans hIJ)
    (f.sylow_normalizes_Li 1) S.nonbinary hm₂
  rw [hfour] at hcase
  have hneq (hh : Source.IsSL (J ⧸ pCore 2 J) 3 4 ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∨
      Source.IsSp (J ⧸ pCore 2 J) 2 4 ∨ ClassificationModels.IsG2At (J ⧸ pCore 2 J) 4 ∨
      Triality.Standard.IsTrialityGroupAt 4 (J ⧸ pCore 2 J)) : False :=
    he (local_eq_of_triangle_models hIL hJ hIJ hr.ge hm hh)
  cases hcase with
  | equal heq => exact (hlt.not_ge (heq ▸ (show f.Li 1 ≤ I from le_sup_right))).elim
  | lie hmJ =>
    cases hmJ with
    | sl3 h => exact (hneq (.inl h)).elim
    | psl3 h => exact (hneq (.inr (.inl h))).elim
    | sp4 h => exact (hneq (.inr (.inr (.inl h)))).elim
    | g2 h => exact (hneq (.inr (.inr (.inr (.inl h))))).elim
    | ree n hn heq _ => omega
    | triality h => exact (hneq (.inr (.inr (.inr (.inr h))))).elim
    | trialityCube n hn heq _ => omega
  | four _ hmJ => exact hmJ

/-- The same original join and marked locals determine its maximal envelope. -/
theorem g2_triangle_maximal_or_janko_four_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    (∃ W : Subgroup G, Nonempty (ChosenModule T I W)) ∧
      (FaithfulMaximalLocal T I ∨
        ∃ J : Subgroup G, I < J ∧
          (T : Subgroup G) ≤ normalizer (J : Set G) ∧
          Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) ∧
          ∃ W : Subgroup G, Nonempty (ChosenModule T J W)) := by
  intro I
  obtain ⟨hchosen,hmax | ⟨J,hIJ,hTJ,hsource,hmJ,hchosenJ⟩⟩ :=
    g2_triangle_reselection_of_common_normal D S m f hu hm₁ hm₂ hfour hfix
      hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ
  · exact ⟨hchosen,.inl hmax⟩
  obtain ⟨_,hmI⟩ := g2_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨_,_,_,_,hXI,hr,_⟩ := g2_triangle_join_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hJ := hsource.maximal_faithful.1.1
  have hrJ : 2 ≤ primeRank 3 (J ⧸ pCore 2 J) := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hr.ge.trans (primeRank_mono 3 hIJ.le)
  have hB := flag_mem_local_of_model D S f 1 hm₂
  have hm₂four : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 4 := by
    simpa only [hfour,show (2:ℕ)^2 = 4 by decide] using hm₂
  obtain ⟨_,_,_,hm₀,_,_⟩ :=
    (g2_triangle_marked_locals_of_common_normal D S m f hu hm₁ hm₂ hfour hfix
      hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ).2.2.2.2.2.2 K₀ (.inl rfl)
  have hXN : X ≤ normalizer (f.Li 1 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
    exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hXcard : Nat.card X = 9 := by
    rw [(Coordinates.g2 m).cartan_card hX,hfour]
    norm_num
  have hspor := local_quotient_not_three_sporadics T hB.1 hJ.1
    (lt_of_le_of_lt (show f.Li 1 ≤ I from le_sup_right) hIJ)
    (f.sylow_normalizes_Li 1) (hXI.trans hIJ.le) hXN hXcard hm₂four
  have hcover := triangle_join_overcomponent_not_m22_cover T hK₀.1 hB.1 hJ.1
    ((show K₀ ≤ I from le_sup_left).trans hIJ.le)
    ((show f.Li 1 ≤ I from le_sup_right).trans hIJ.le)
    hTK₀ (f.sylow_normalizes_Li 1) hm₀ hm₂four hmI
  refine ⟨hchosen,.inr ⟨J,hIJ,hTJ,hsource,?_,hchosenJ⟩⟩
  rcases triangle_exceptional_overcomponent_sieve hIJ.le hrJ hsource.quasisimple hmI hmJ
      with hm | hm | hm | hm
  · exact (hcover hm).elim
  · exact (hspor (.inl hm)).elim
  · exact hm
  · exact (hspor (.inr (.inr hm))).elim

/-- The same original join and marked locals determine its maximal envelope. -/
theorem g2_triangle_maximal_faithful_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    FaithfulMaximalLocal T I ∧ Hypothesis1223 KnownSimple.IsKnownSimple T I ∧
      ∃ W : Subgroup G, Nonempty (ChosenModule T I W) := by
  intro I
  obtain ⟨hchosen,hcases⟩ := g2_triangle_maximal_or_janko_four_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hqI,hmI⟩ := g2_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hmax : FaithfulMaximalLocal T I := by
    rcases hcases with hmax | ⟨J,hIJ,_,hsource,hmJ,_⟩
    · exact hmax
    have hB := flag_mem_local_of_model D S f 1 hm₂
    have hm₂four : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 4 := by
      simpa only [hfour,show (2:ℕ)^2 = 4 by decide] using hm₂
    obtain ⟨_,_,_,hm₀,_,_⟩ :=
      (g2_triangle_marked_locals_of_common_normal D S m f hu hm₁ hm₂ hfour hfix
        hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ).2.2.2.2.2.2 K₀ (.inl rfl)
    exact (triangle_join_overcomponent_not_j4 T hK₀.1 hB.1 hsource.maximal_faithful.1.1.1
      ((show K₀ ≤ I from le_sup_left).trans hIJ.le)
      ((show f.Li 1 ≤ I from le_sup_right).trans hIJ.le)
      hTK₀ (f.sylow_normalizes_Li 1) hm₀ hm₂four hmI hmJ).elim
  refine ⟨hmax,?_,hchosen⟩
  exact {
    simpleQTKE := S.source.simpleQTKE
    maximal_faithful := hmax
    quasisimple := hqI
    no_rankTwo := S.source.no_rankTwo
    no_M22 := S.source.no_M22
    no_M23 := S.source.no_M23
    no_J4 := S.source.no_J4 }

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
