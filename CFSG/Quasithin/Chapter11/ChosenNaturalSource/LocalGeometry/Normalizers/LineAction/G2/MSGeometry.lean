module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSRecognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.MSInputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import Theory.AtlasPort.LinearGroups.G2.Simplicity

/-!
# Critical geometry of the actual exceptional escape

For the original marked G₂ component, escape of the Sylow normalizer supplies
the MS characteristic condition inside LT. The central-omega orbit is faithful
modulo O₂(LT), so the full FF classification recognizes its moved quotient as
the natural G₂(4) module. The same original pair has a positive even critical
distance and a reversible critical pair with noncommuting central layers.
The recognized commutator embeds as the actual U-layer at both critical
vertices; its canonical projection is a central cover with its fixed kernel
retained.

These are the inputs to the critical-pair comparison in MS93 (3.2),
pp.865--866. That comparison, and hence the G₂ exclusion in source 3.3.16,
remain with the line-action owner. The final 11.2.3 assembly belongs to
`qt-d-1222-natural-normalizer-source`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
open ChapterC ChapterC.MSCentralOrbit
open RecognitionSource.FusionReducibleNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
local notation "H" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "K" => Subgroup.subgroupOf L (L ⊔ (T : Subgroup G))
local notation "R" => Subgroup.subgroupOf (T : Subgroup G) (L ⊔ (T : Subgroup G))

include D in
omit [Finite G] in
private theorem source_product : ∀ h : H, ∃ k ∈ K, ∃ r ∈ R, k*r=h := by
  intro h
  have hp : (h : G) ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
      D.sylow_normalizes_component]
    exact h.property
  obtain ⟨k,hk,r,hr,he⟩ := hp
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

omit [Finite G] in
private theorem source_radical_two : IsPGroup 2 R :=
  T.isPGroup'.of_equiv (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ H from le_sup_right)).symm

include D in
omit [Finite G] in
private theorem source_radical_ne_bot : R ≠ ⊥ := by
  intro hb
  have hh := congrArg (map (H).subtype) hb
  rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right),Subgroup.map_bot] at hh
  exact D.ne_bot (bot_unique (D.le_sylow.trans_eq hh))

omit [Finite G] in
private theorem source_core_le_radical : pCore 2 H ≤ R :=
  pCore_isPGroup.le_sylow_of_normal (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right))

include D S in
/-- MS3 transported to the original Sylow subgroup inside LT, retaining relative normality. -/
theorem source_msCharacteristic
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    MSCharacteristicCondition R := by
  intro C hC hne hn
  let e := subgroupOfEquivOfLe (show (T : Subgroup G) ≤ H from le_sup_right)
  let B : Subgroup (T : Subgroup G) := C.comap e.symm.toMonoidHom
  let : B.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    have hh := characteristic_iff_le_comap.mp hC ((e.trans a).trans e.symm) hx
    change e.symm (a (e (e.symm x))) ∈ C at hh
    change e.symm (a x) ∈ C
    simpa only [MulEquiv.apply_symm_apply] using hh
  have he : B.map (T : Subgroup G).subtype = (C.map (R).subtype).map (H).subtype := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨e.symm t,⟨e.symm t,ht,rfl⟩,rfl⟩
    · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
      refine ⟨e t,?_,rfl⟩
      change e.symm (e t) ∈ C
      rwa [e.symm_apply_apply]
  have hn' : ((B.map (T : Subgroup G).subtype).subgroupOf H).Normal := by
    rw [he,subgroupOf_map_subtype_eq]
    exact hn
  have hb := characteristic_eq_bot_of_escape S.source D hescape B
    ((normal_subgroupOf_iff_le_normalizer
      ((map_subtype_le B).trans le_sup_right)).mp hn')
  apply hne
  have hc : B.map e.symm.toMonoidHom = C := by
    change (C.comap e.symm.toMonoidHom).map e.symm.toMonoidHom = C
    exact map_comap_eq_self_of_surjective e.symm.surjective C
  rw [← hc,hb,Subgroup.map_bot]

include D S m in
/-- The original G₂ marking identifies the intrinsic component inside LT. -/
theorem source_component_model : Nonempty ((K ⧸ pCore 2 K) ≃* Atlas.G2.Model S.field.Carrier) := by
  let e := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  exact ⟨(QuotientGroup.congr (pCore 2 K) (pCore 2 L) e (pCore_map_iso 2 e)).trans m.groupEquiv⟩

include D S m in
/-- The central orbit is faithful modulo the literal two-core of LT. -/
theorem source_omegaOrbit_centralizer
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    centralizer (omegaOrbit R : Set H) = pCore 2 H := by
  have hK := S.source.maximal_faithful.1.1.1
  have hres := component_eq_residual K R hK source_radical_two (source_product D)
  let : (K).Normal := by rw [←hres]; infer_instance
  have hF : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (2 : ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Atlas.G2.Model S.field.Carrier) := Atlas.G2.isSimple hF
  let : IsSimpleGroup (K ⧸ pCore 2 K) := (source_component_model D S m).some.isSimpleGroup
  exact omegaOrbit_centralizer K R source_radical_two (source_radical_ne_bot D)
    source_core_le_radical (join_characteristicTwo S.source) (source_product D)
    (source_msCharacteristic D S hescape)

include D S m in
/-- The actual G₂ escape supplies positive even critical geometry and endpoint centralizer control. -/
theorem source_critical_geometry
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    (∃ g : BinaryMS.MS93.Geometry R, 0 < g.b R ∧ Even (g.b R)) ∧
      BinaryMS.MS93.EdgeCentralizerCondition R := by
  have hf := source_omegaOrbit_centralizer D S m hescape
  exact ⟨exists_positive_even_geometry R source_radical_two (source_radical_ne_bot D)
    (source_msCharacteristic D S hescape) source_core_le_radical
    (join_characteristicTwo S.source) hf,
    edgeCentralizerCondition R source_radical_two source_core_le_radical hf⟩

include D S m in
/-- The original escape constructs a genuine reversible critical pair with
noncommuting Z-layers; the endpoints are in the same original-group orbit. -/
theorem source_critical_pair
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ g : BinaryMS.MS93.Geometry R, 0 < g.b R ∧ Even (g.b R) ∧
      ∃ a : Stellmacher.PushingUp.AmalgamGraph.Vertex R,
      ∃ ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false,
        BinaryMS.MS93.CriticalPair R (BinaryMS.MS93.alpha R) a
          (g.exists_critical (BinaryMS.MS93.alpha R) rfl) ∧
        BinaryMS.MS93.CriticalPair R a (BinaryMS.MS93.alpha R)
          (g.exists_critical a ha) ∧
        ⁅BinaryMS.MS93.Z R (BinaryMS.MS93.alpha R), BinaryMS.MS93.Z R a⁆ ≠ ⊥ := by
  obtain ⟨⟨g,hpos,hev⟩,hC⟩ := source_critical_geometry D S m hescape
  obtain ⟨a,ha⟩ := BinaryMS.MS93.criticalPair_exists R (BinaryMS.MS93.alpha R)
    (g.exists_critical _ rfl)
  have hcol := BinaryMS.MS93.critical_endpoint_color R _ rfl _ ha
  exact ⟨g,hpos,hev,a,hcol,ha,
    BinaryMS.MS93.critical_reverse R g hC _ rfl hpos a hcol ha,
    BinaryMS.MS93.critical_noncommutation R g hC _ rfl hpos ha⟩

include D S m in
private theorem source_component_simple : IsSimpleGroup (K ⧸ pCore 2 K) := by
  have hF : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (2 : ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Atlas.G2.Model S.field.Carrier) := Atlas.G2.isSimple hF
  exact (source_component_model D S m).some.isSimpleGroup

include D S m in
private theorem source_image_structure :
    let B := (K).map (QuotientGroup.mk' (pCore 2 H))
    (K).Normal ∧ B.Normal ∧ IsSimpleGroup B ∧ IsQuasisimple B ∧
      centralizer (B : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let := source_component_simple D S m
  exact component_image_structure K R S.source.maximal_faithful.1.1.1
    source_radical_two (source_product D)

include D S m in
private theorem source_image_card
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nat.card ((K).map (QuotientGroup.mk' (pCore 2 H))) = 251596800 := by
  have hK := S.source.maximal_faithful.1.1.1
  have hF : Nat.card S.field.Carrier = 4 := by
    rw [S.field.card_eq, degree_eq_two_of_sylow_normalizer_escape (G2.flag S m) hescape]
    rfl
  rw [← Nat.card_congr (cComponentTwoCoreQuotientEquiv hK).toEquiv,
    Nat.card_congr (source_component_model D S m).some.toEquiv,
    Atlas.G2.card_Model,hF]
  norm_num

include D S m in
private theorem source_image_sqtk
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    IsSQTK KnownSimple.IsKnownSimple ((K).map (QuotientGroup.mk' (pCore 2 H))) := by
  have hm := sylow_msPair_of_escape D S (Coordinates.g2 m) hescape
  have hsqK := hm.sqtk.subgroup K
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    refine ⟨?_,hsqK.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    exact hsqK.stronglyQuasithin p hp ho
  exact (IsSQTK.equiv (cComponentTwoCoreQuotientEquiv hm.component)).mp hsqQ

set_option backward.isDefEq.respectTransparency false in
include D S m in
/-- The escaping G₂ branch has a natural field-four action on the actual
central-omega moved quotient. No faithful-layer or FF premise is added. -/
theorem source_initial_module
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let B := (K).map q
    let X := omegaCenterIn (pCore 2 H)
    ∃ hker : q.ker = centralizer (X : Set H), ∃ hn : B.Normal,
      let := hn
      let ρ := NormalElementaryQuotient.representation X q
        (QuotientGroup.mk'_surjective _) hker
      IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) ∧
        ∃ F : BinaryField, F.degree = 2 ∧
          Nonempty (ActionEquiv ((MovedSection.ofNormal ρ B).action.comp B.subtype)
            (binaryG2 F)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (K).map q
  let X := omegaCenterIn (pCore 2 H)
  have hs := source_image_structure (T := T) (L := L) (V := V) D S m
  have hBn : B.Normal := hs.2.1
  let : (K).Normal := hs.1
  let : B.Normal := hBn
  let : IsSimpleGroup B := hs.2.2.1
  let : IsQuasisimple B := hs.2.2.2.1
  have hBC : centralizer (B : Set (H ⧸ pCore 2 H)) = ⊥ := hs.2.2.2.2
  have hc := source_image_card D S m hescape
  have hsq := source_image_sqtk D S m hescape
  have hf := source_omegaOrbit_centralizer D S m hescape
  have hX := centralOmega_centralizer R source_core_le_radical
    (join_characteristicTwo S.source) hf
  let hker : q.ker = centralizer (X : Set H) := (QuotientGroup.ker_mk' _).trans hX.symm
  refine ⟨hker,hBn,?_⟩
  apply ff_card_g2_four_moved_natural _ B hc hBC hsq
  · exact NormalElementaryQuotient.representation_injective _ _ _ _
  · exact centralOmega_isFFModule R (source_msCharacteristic D S hescape)
      source_radical_two (source_radical_ne_bot D) source_core_le_radical
      (join_characteristicTwo S.source) hf q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

include D S m in
/-- The faithful Sylow-center orbit has the same original commutator as
Ω₁Z(O₂(LT)); thus recognition applies to the literal initial moving layer. -/
theorem source_initial_commutator
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ⁅omegaOrbit R,K⁆ = ⁅omegaCenterIn (pCore 2 H),K⁆ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (K).map q
  let : Group.IsPerfect K := S.source.maximal_faithful.1.1.1.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective K)
  let : IsElementaryAbelian 2 (omegaOrbit R) :=
    omegaOrbit_elementary R source_core_le_radical (join_characteristicTwo S.source)
  obtain ⟨hker,hn,hi,_⟩ := source_initial_module D S m hescape
  let := hn
  have hne : B ≠ ⊥ := by
    have hc := source_image_card D S m hescape
    intro hz
    change Nat.card B = 251596800 at hc
    rw [hz,card_bot] at hc
    omega
  exact NormalElementaryQuotient.commutator_eq_of_irrPlus (omegaOrbit R)
    (omegaCenterIn (pCore 2 H))
    (omegaOrbit_le_centralOmega R source_core_le_radical (join_characteristicTwo S.source))
    q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (source_omegaOrbit_centralizer D S m hescape).symm)
    hker K B rfl hne hi

include D S m in
/-- The recognized original commutator embeds as Uα in the actual MS amalgam. -/
theorem source_initial_commutator_map
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    (⁅omegaCenterIn (pCore 2 H),K⁆).map
        (Stellmacher.PushingUp.AmalgamGraph.embedM R) =
      BinaryMS.MS93.U R (BinaryMS.MS93.alpha R) := by
  rw [← source_initial_commutator D S m hescape, BinaryMS.MS93.U,
    Z_alpha_eq_omegaOrbit, BinaryMS.MS93.Ltilde_alpha, ← map_commutator,
    component_eq_residual K R S.source.maximal_faithful.1.1.1 source_radical_two
      (source_product D)]

/-- The canonical moved projection is a central cover of the marked G₂(4)
module. The original actor, fixed kernel and quotient projection are retained. -/
def HasNaturalMovingCover
    {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) J W) (B : Subgroup J) [B.Normal] : Prop :=
  let s := MovedSection.ofNormal ρ B
  ∃ F : BinaryField, F.degree = 2 ∧
    ∃ e : ActionEquiv (s.action.comp B.subtype) (binaryG2 F),
      Representation.OneCohomology.IsCover (MovedSection.coverProjection s e)

private theorem cover_of_natural_moved
    {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) J W) (B : Subgroup J) [B.Normal]
    (h : IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) ∧
      ∃ F : BinaryField, F.degree = 2 ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ B).action.comp B.subtype)
          (binaryG2 F))) : HasNaturalMovingCover ρ B := by
  obtain ⟨hi,F,hF,⟨e⟩⟩ := h
  exact ⟨F,hF,e,MovedSection.coverProjection_isCover _ hi e⟩

set_option backward.isDefEq.respectTransparency false in
include D S m in
/-- The literal projection from the original moved layer is a central cover
of the field-four G₂ module. The fixed kernel is retained. -/
theorem source_initial_cover
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let B := (K).map q
    let X := omegaCenterIn (pCore 2 H)
    ∃ hker : q.ker = centralizer (X : Set H), ∃ hn : B.Normal,
      letI := hn
      HasNaturalMovingCover (NormalElementaryQuotient.representation X q
        (QuotientGroup.mk'_surjective _) hker) B := by
  obtain ⟨hker,hn,h⟩ := source_initial_module D S m hescape
  let := hn
  exact ⟨hker,hn,cover_of_natural_moved _ _ h⟩

open Stellmacher.PushingUp.AmalgamGraph BinaryMS.MS93

include D S m in
/-- At the opposite critical vertex the same original LT, component, two-core
and recognized moving layer occur through one actual injective homomorphism. -/
theorem source_critical_coordinates
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ g : Geometry R, 0 < g.b R ∧ Even (g.b R) ∧
      ∃ a : Vertex R, ∃ ha : color R a = false,
        CriticalPair R (alpha R) a (g.exists_critical (alpha R) rfl) ∧
        CriticalPair R a (alpha R) (g.exists_critical a ha) ∧
        ⁅Z R (alpha R),Z R a⁆ ≠ ⊥ ∧
        ∃ i : H →* FreeAmalgam R, Function.Injective i ∧
          i.range = stabilizer R a ∧ (K).map i = Ltilde R a ∧
          (pCore 2 H).map i = Q R a ∧
          (⁅omegaCenterIn (pCore 2 H),K⁆).map i = U R a := by
  obtain ⟨g,hpos,hev,a,ha,hc,hrev,hcomm⟩ := source_critical_pair D S m hescape
  refine ⟨g,hpos,hev,a,ha,hc,hrev,hcomm,?_⟩
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color R ha
  let i := (MulAut.conj x⁻¹).toMonoidHom.comp (embedM R)
  refine ⟨i,(MulAut.conj x⁻¹).injective.comp (embedM_injective R),?_,?_,?_,?_⟩
  · have hh := stabilizer_act R x (alpha R)
    dsimp only [i]
    rw [MonoidHom.range_comp]
    change (Mbar R).map (MulAut.conj x⁻¹).toMonoidHom = _
    simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using hh.symm
  · have hh := Ltilde_act R x (alpha R)
    rw [Ltilde_alpha,component_eq_residual K R S.source.maximal_faithful.1.1.1
      source_radical_two (source_product D)] at hh
    simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
  · have hh := Q_act R x (alpha R)
    rw [Q_alpha R source_radical_two source_core_le_radical] at hh
    simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
  · have hh := U_act R x (alpha R)
    rw [← source_initial_commutator_map D S m hescape] at hh
    simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
