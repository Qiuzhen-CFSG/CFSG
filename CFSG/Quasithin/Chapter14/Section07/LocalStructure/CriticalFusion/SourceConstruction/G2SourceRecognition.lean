module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceFamilies
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.Constituent
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.CentralSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.ResidualMovedGeneration

/-!
# Natural and Weyl recognition on the original G₂ section

The literal critical denominator U ∩ Qα is contained in the commutator
preimage for Uα and Zα. Its selected index bounds the codimension of that
preimage, whose displacements lie in the image of the order-two Zα.
The no-strong-FF and no-transvection arguments then force the unique
noncentral constituent to fill the section, using the complete earlier
F.9.18 orbit alternatives. Binary G₂ recognition constructs its central
natural quotient; no natural projection or whole-module identification
is assumed.

The natural normalizer constructs an embedding of the original H/O₂(H)
into full G₂(2), compatible with a recognized K/O₂(K) marking. Uniqueness
of maps from the generated Weyl cover extends equivariance to that entire
actor. Dimension six or seven gives the two alternatives of 14.7.54.

The faithful descended action, generalized-Fitting identity, F.9.18 orbit
implications and quadratic critical choice remain explicit earlier source
inputs. Their producers and final discharge remain with qt-d-14775-source.
This module proves the recognition implication, not the later G₂ exclusion.
The original section and generation are those of SourceConstruction;
no Data or legacy CriticalSymmetryInput is used.

Source: Aschbacher–Smith, 14.7.54, pp.1065–1066, with Notation 14.7.1,
pp.1042–1043, F.9.18, B.4.2, B.4.5 and B.4.6(1). The octonion results
retain the attribution in LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

/-- The original section, expressed with the literal two-core quotient actor. -/
def starSection : ConjugationSection F.H F.U (F.Vi 1) σ where
  le := c.section_le
  normalizes := c.normalized
  centralizes := normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  line_le := c.kernel_le
  quotient := c.coordinates
  surjective := c.onto
  kernel := c.kernel_eq
  conjugates := fun a v => (c.equivariant a v).symm

omit [Finite G] in
include c in
/-- Descent of the action gives the original two-core commutator bound. -/
theorem core_commutator : ⁅F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1 := by
  apply commutator_le.mpr
  rintro _ ⟨a, ha, rfl⟩ v hv
  exact (c.action_mem_ker_iff a).mp (by
    change σ (QuotientGroup.mk' (pCore 2 F.H) a) = 1
    have he : QuotientGroup.mk' (pCore 2 F.H) a = 1 :=
      (QuotientGroup.eq_one_iff a).mpr ha
    rw [he,map_one]) v hv

omit [Finite G] in
include c in
/-- Conjugating the original action retains the reciprocal point denominator. -/
theorem reciprocal_core_commutator (path : CriticalPath (L := L) F) :
    ⁅path.Qα, path.Uα⁆ ≤ path.Zα := by
  have hh := map_mono (f := (MulAut.conj path.conjugator⁻¹).toMonoidHom)
    (core_commutator c)
  rw [map_commutator, map_pCoreIn_of_injective 2 _ _
    (MulAut.conj path.conjugator⁻¹).injective] at hh
  exact hh

/-- Critical index and displacement bounds on the original coordinates. -/
theorem critical_linear_bounds
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) :
    let D := commutatorPreimage F.U path.Uα path.Zα
    Module.finrank (ZMod 2) (W ⧸ c.imageSpace D) ≤ rank (star F path.Uα) ∧
      Module.finrank (ZMod 2) (c.imageSpace path.Zα) ≤ 1 ∧
      ∀ a ∈ star F path.Uα, ∀ v ∈ c.imageSpace D,
        σ a v - v ∈ c.imageSpace path.Zα := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let s := starSection c
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hD : F.U ⊓ path.Qα ≤ commutatorPreimage F.U path.Uα path.Zα :=
    le_commutatorPreimage inf_le_left
      ((commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator c path))
  have hidx := relIndex_le_of_le_left hD
    (show (F.U ⊓ path.Qα).relIndex F.U ≠ 0 from Subgroup.index_ne_zero_of_finite)
  have hd : Module.finrank (ZMod 2)
      (W ⧸ s.image (Chapter13.Section08.Source.DH F.U path.Uα path.Zα)) ≤
      rank (star F path.Uα) := by
    rw [s.quotient_finrank _ (s.line_le_DH _ _ hAH)]
    exact (Nat.log_monotone (b := 2) hidx).trans selection.comparison
  have hl := s.critical_line_displacement_of_conjugate path.Uα path.conjugator⁻¹
    (reciprocal_placement h path) (by simpa using F.card 1 (by decide))
  exact ⟨hd, hl⟩

include c in
/-- The original seed generation gives full movement by the actual K-star. -/
theorem full_star_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    subspaceCommutator σ ⊤ (star F (K F)) = ⊤ := by
  rw [subspaceCommutator_top_eq_coinvariants]
  let r : K F →* star F (K F) := {
    toFun := fun k => ⟨starMap F ⟨k, map_subtype_le _ k.property⟩,
      ⟨⟨k, map_subtype_le _ k.property⟩, k.property, rfl⟩⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun x y => Subtype.ext ((starMap F).map_mul
      ⟨x,map_subtype_le _ x.property⟩ ⟨y,map_subtype_le _ y.property⟩) }
  exact c.coinvariants_eq_top_of_group_generation (K F) (map_subtype_le _)
    (σ.comp (star F (K F)).subtype) r (fun _ _ => rfl) (by
      rw [commutator_comm,commutator_U h F,sup_eq_left.mpr c.kernel_le])

private theorem component_properties
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasisimple (star F (K F)) ∧
      centralizer (star F (K F) : Set (HStar F.H)) = ⊥ := by
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsSimpleGroup (star F (K F)) := e.isSimpleGroup
  let : Group.IsPerfect (star F (K F)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center (star F (K F)) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h))
  refine ⟨⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩,
    bot_unique ?_⟩
  intro x hx
  have hxL : x ∈ star F (K F) := by
    rw [← hfit] at hx ⊢
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hx
  have hh : (⟨x,hxL⟩ : star F (K F)) ∈ center (star F (K F)) := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hx l l.property)
  rw [hz,mem_bot] at hh
  exact congrArg Subtype.val hh

include c in
/-- Recognition of the original central section. The explicit hypotheses are
the earlier faithful star action, generalized-Fitting conclusion, complete
F.9.18 orbit alternatives, and the quadratic critical choice. -/
theorem source_isIrrPlus
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hA : IsElementaryTwo (star F path.Uα)) :
    IsIrrPlus σ (star F (K F)) ⊤ := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : (star F (K F)).Normal := hfit ▸ inferInstance
  obtain ⟨hq,hc⟩ := component_properties hcomponent hfit eK
  let := hq
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  obtain ⟨hd,hl,hm⟩ := critical_linear_bounds c h path hplace selection
  let D := c.imageSpace (commutatorPreimage F.U path.Uα path.Zα)
  have hcrit : D ≤ fixedSpace σ (star F path.Uα) ∨
      ∃ S : Submodule (ZMod 2) W, IsAtom S ∧
        ∀ a ∈ star F path.Uα, ∀ v ∈ D, σ a v - v ∈ S := by
    by_cases hz : c.imageSpace path.Zα = ⊥
    · left
      intro v hv a
      have hh := hm a a.property v hv
      rw [hz] at hh
      exact sub_eq_zero.mp hh
    · right
      refine ⟨c.imageSpace path.Zα, Submodule.isAtom_iff_finrank_eq_one.mpr ?_, hm⟩
      have hn : Module.finrank (ZMod 2) (c.imageSpace path.Zα) ≠ 0 :=
        fun hh => hz (Submodule.finrank_eq_zero.mp hh)
      omega
  exact Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.whole_isIrrPlus
    σ (star F (K F)) hf hc e (full_star_commutator c h) P hP orbit
    _ hA D hcrit hd

include c in
/-- The central natural projection is constructed from the actual Irr⁺
quotient, with a freshly recognized intrinsic K/O₂(K) marking. -/
theorem source_projection
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hi : IsIrrPlus σ (star F (K F)) ⊤)
    (A : Subgroup (HStar F.H)) (hA : IsElementaryTwo A)
    (hquad : IsQuadratic σ A) (hbound : fixedCodim σ A ≤ 2 * rank A) :
    ∃ eK' : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
        (∀ k : K F, i (starMap F ⟨k,map_subtype_le _ k.property⟩) =
          (eK' (QuotientGroup.mk' (pCore 2 (K F)) k) : Atlas.G2.Model (ZMod 2))) ∧
      ∃ p : Representation.IntertwiningMap (σ.comp (modelActor (map_subtype_le _) hcomponent eK'))
        (Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2)),
        Function.Surjective p ∧ p.toLinearMap.ker ≤
          OneCohomology.fixed (σ.comp (modelActor (map_subtype_le _) hcomponent eK')) ∧
        ∀ a w, p (σ a w) = Atlas.G2.Natural.action (ZMod 2) (i a) (p w) := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : (star F (K F)).Normal := hfit ▸ inferInstance
  obtain ⟨hq,hc⟩ := component_properties hcomponent hfit eK
  let := hq
  let j : ((K F) ⧸ pCore 2 (K F)) ≃* star F (K F) :=
    Chapter13.Section08.Components.componentStarEquiv F.H (K F) (map_subtype_le _) hcomponent
  obtain ⟨e,f,he⟩ :=
    Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.central_section_natural
      σ (star F (K F)) hc (j.symm.trans eK) ⊤ hi A hA hquad hbound
  let τ := normalCentralQuotient σ (star F (K F)) (⊤ : Subrepresentation σ)
  have hτ : Function.Injective τ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hx' : (⟨x, mem_top x⟩ : (⊤ : Subgroup (HStar F.H))) ∈
        (centralSectionRepresentation σ (star F (K F)) ⊤ ⊤
          (le_subspaceStabilizer σ ⊤ (by simp)) le_normalizer_of_normal).ker := hx
    have hh := (centralSection_kernel_le_centralizer σ (star F (K F)) ⊤ le_top ⊤
      hi (le_subspaceStabilizer σ ⊤ (by simp)) le_normalizer_of_normal
      (mem_map_of_mem (⊤ : Subgroup (HStar F.H)).subtype hx')).2
    change x ∈ centralizer (star F (K F) : Set (HStar F.H)) at hh
    rwa [hc] at hh
  obtain ⟨i,hi',hmark,hiAct⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    τ (star F (K F)) e f he hτ
  let eK' := j.trans e
  let C := (fixedSpace σ (star F (K F))).comap (⊤ : Submodule (ZMod 2) W).subtype
  let t : W →ₗ[ZMod 2] (⊤ : Submodule (ZMod 2) W) :=
    (LinearEquiv.ofTop (⊤ : Submodule (ZMod 2) W) rfl).symm.toLinearMap
  let p : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2) :=
    f.toLinearMap.comp (C.mkQ.comp t)
  have hp (v : W) : p v = f (C.mkQ (t v)) := rfl
  have hpeq (a : commutator (Atlas.G2.Model (ZMod 2))) (v : W) :
      p (σ (modelActor (map_subtype_le _) hcomponent eK' a) v) =
        Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2) a (p v) := by
    have hh := he (e.symm a) (C.mkQ (t v))
    rw [e.apply_symm_apply] at hh
    have ha : modelActor (map_subtype_le _) hcomponent eK' a =
        (e.symm a : HStar F.H) := by
      change (j (j.symm (e.symm a)) : HStar F.H) = _
      rw [j.apply_symm_apply]
    rw [ha]
    exact hh
  let P : Representation.IntertwiningMap
      (σ.comp (modelActor (map_subtype_le _) hcomponent eK'))
      (Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ hpeq
  refine ⟨eK',i,hi',?_,P,?_,?_,?_⟩
  · intro k
    have hh := hmark (j (QuotientGroup.mk' (pCore 2 (K F)) k))
    have hj := Chapter13.Section08.Components.componentStarEquiv_mk F.H (K F)
      (map_subtype_le _) hcomponent k
    change (j (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) = _ at hj
    rw [hj] at hh
    exact hh
  · exact f.surjective.comp (C.mkQ_surjective.comp
      (LinearEquiv.ofTop (⊤ : Submodule (ZMod 2) W) rfl).symm.surjective)
  · intro v hv a
    have hz : C.mkQ (t v) = 0 := f.injective (by
      change p v = f 0
      rw [map_zero]
      exact hv)
    have hh : t v ∈ C := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact hh (j (eK'.symm a))
  · intro a w
    exact hiAct a (C.mkQ (t w))


include c in
/-- The Weyl cover is equivariant for the whole original star actor. Only
recognition of the proper central section was used to construct that actor. -/
theorem source_weyl_cover
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hi : IsIrrPlus σ (star F (K F)) ⊤)
    (A : Subgroup (HStar F.H)) (hA : IsElementaryTwo A)
    (hquad : IsQuadratic σ A) (hbound : fixedCodim σ A ≤ 2 * rank A) :
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
    ∃ p : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2), Function.Surjective p ∧
      (∀ a w, p (σ a w) = Atlas.G2.Natural.action (ZMod 2) (i a) (p w)) ∧
    ∃ f : Atlas.G2.Natural.TraceZero (ZMod 2) →ₗ[ZMod 2] W,
      Function.Surjective f ∧
      (∀ a w, f (Atlas.G2.Natural.traceZeroAction (ZMod 2) (i a) w) = σ a (f w)) ∧
      ∀ w, p (f w) = Atlas.G2.Natural.mk (ZMod 2) w := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : (star F (K F)).Normal := hfit ▸ inferInstance
  obtain ⟨eK',i,hi',hmark,p,hp,hker,hact⟩ :=
    source_projection c hcomponent hfit eK hi A hA hquad hbound
  let j : ((K F) ⧸ pCore 2 (K F)) ≃* star F (K F) :=
    Chapter13.Section08.Components.componentStarEquiv F.H (K F) (map_subtype_le _) hcomponent
  let e : star F (K F) ≃* commutator (Atlas.G2.Model (ZMod 2)) := j.symm.trans eK'
  have hj (k : K F) : (j (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) =
      starMap F ⟨k,map_subtype_le _ k.property⟩ :=
    Chapter13.Section08.Components.componentStarEquiv_mk F.H (K F) (map_subtype_le _) hcomponent k
  have himark (a : star F (K F)) : i a = (e a : Atlas.G2.Model (ZMod 2)) := by
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 (K F)) (j.symm a)
    have ha : j (QuotientGroup.mk' (pCore 2 (K F)) k) = a := by rw [hk,j.apply_symm_apply]
    rw [←ha,hj,hmark]
    exact congrArg Subtype.val (congrArg eK' (j.symm_apply_apply _)).symm
  have hcontains : commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range := by
    intro g hg
    refine ⟨e.symm ⟨g,hg⟩,?_⟩
    rw [himark,e.apply_symm_apply]
  have hfull : Coinvariants.ker (σ.comp (modelActor (map_subtype_le _) hcomponent eK')) = ⊤ :=
    c.coinvariants_eq_top_of_group_generation (K F) (map_subtype_le _)
      (σ.comp (modelActor (map_subtype_le _) hcomponent eK'))
      (eK'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K F))))
      (fun k w => by
        change σ (starMap F ⟨k,map_subtype_le _ k.property⟩) w =
          σ (modelActor (map_subtype_le _) hcomponent eK'
            (eK' (QuotientGroup.mk' (pCore 2 (K F)) k))) w
        exact congrArg (fun a => σ a w)
          (modelActor_mk (map_subtype_le _) hcomponent eK' k).symm)
      (by rw [commutator_comm,commutator_U h F,sup_eq_left.mpr c.kernel_le])
  obtain ⟨f,hf,hover⟩ := Atlas.G2.Natural.OrthogonalCover.exists_quotient (ZMod 2) p
    ⟨hp,hker,hfull⟩
  let ζ := (Atlas.G2.Natural.traceZeroAction (ZMod 2)).comp i
  let η := (Atlas.G2.Natural.action (ZMod 2)).comp i
  have hζ : ζ.comp (star F (K F)).subtype =
      (Atlas.G2.Natural.OrthogonalCover.binaryAction (ZMod 2)).comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro v
    change Atlas.G2.Natural.traceZeroAction (ZMod 2) (i a) v =
      Atlas.G2.Natural.traceZeroAction (ZMod 2) (e a) v
    rw [himark]
  have hgen : Coinvariants.ker (ζ.comp (star F (K F)).subtype) = ⊤ := by
    rw [hζ,OneCohomology.CentralCoverOriginalAction.commutator_comp_equiv]
    exact (Atlas.G2.Natural.OrthogonalCover.binaryProjection_isCover (ZMod 2)).2.2
  have hfixed : p.toLinearMap.ker ≤ OneCohomology.fixed (σ.comp (star F (K F)).subtype) := by
    intro v hv a
    have hh := hker hv (e a)
    have ha : modelActor (map_subtype_le _) hcomponent eK' (e a) = a := by
      change (j (eK'.symm (eK' (j.symm a))) : HStar F.H) = a
      rw [eK'.symm_apply_apply,j.apply_symm_apply]
    change σ (modelActor (map_subtype_le _) hcomponent eK' (e a)) v = v at hh
    rwa [ha] at hh
  have hfL (a : star F (K F)) (w) : f (ζ a w) = σ a (f w) := by
    have hh := LinearMap.congr_fun (f.isIntertwining' (e a)) w
    have ha : modelActor (map_subtype_le _) hcomponent eK' (e a) = a := by
      change (j (eK'.symm (eK' (j.symm a))) : HStar F.H) = a
      rw [eK'.symm_apply_apply,j.apply_symm_apply]
    change f (Atlas.G2.Natural.traceZeroAction (ZMod 2) (e a) w) =
      σ (modelActor (map_subtype_le _) hcomponent eK' (e a)) (f w) at hh
    change f (Atlas.G2.Natural.traceZeroAction (ZMod 2) (i a) w) = _
    rw [himark]
    rwa [ha] at hh
  refine ⟨i,hi',hcontains,p.toLinearMap,hp,hact,f.toLinearMap,hf,?_,hover⟩
  exact OneCohomology.CentralCoverOriginalAction.quotient_original_equivariant
    (star F (K F)) (η := η) (ζ := ζ) (τ := σ)
    (Atlas.G2.Natural.mk (ZMod 2)) p.toLinearMap f.toLinearMap
    (fun _ _ => rfl) hact hfixed hgen hfL hover


/-- The actor selected in Notation 14.7.1 is elementary and nontrivial;
this uses the original abelian span and the positive critical index. -/
theorem critical_elementary
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) : IsElementaryTwo (star F path.Uα) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : IsElementaryAbelian 2 path.Uα :=
    IsElementaryAbelian.map (MulAut.conj path.conjugator⁻¹).toMonoidHom
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  let := IsElementaryAbelian.subgroupOf (p := 2) hAH
  exact ⟨path.star_ne_bot selection,IsElementaryAbelian.map (starMap F)⟩

include c in
/-- Source 14.7.54 with the earlier faithful action and F.9.18 implications
explicit. Both alternatives identify the whole original section, equivariantly
for its entire star actor; the natural projection is not assumed. -/
theorem source_natural_or_weyl
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (hquad : IsQuadratic σ (star F path.Uα))
    (hbound : fixedCodim σ (star F path.Uα) ≤ 2 * rank (star F path.Uα)) :
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
      ((∃ E : Atlas.G2.Natural.Space (ZMod 2) ≃ₗ[ZMod 2] W,
        ∀ a v, E (Atlas.G2.Natural.action (ZMod 2) (i a) v) = σ a (E v)) ∨
       (∃ E : Atlas.G2.Natural.TraceZero (ZMod 2) ≃ₗ[ZMod 2] W,
        ∀ a v, E (Atlas.G2.Natural.traceZeroAction (ZMod 2) (i a) v) = σ a (E v))) := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hA := critical_elementary h hab path hplace selection
  have hi := source_isIrrPlus c h hcomponent hfit eK hf P hP orbit path hplace selection hA
  obtain ⟨i,hi,hcontains,p,hp,hact,f,hf,hfact,hover⟩ :=
    source_weyl_cover c h hcomponent hfit eK hi _ hA hquad hbound
  refine ⟨i,hi,hcontains,?_⟩
  have hlo : 6 ≤ Module.finrank (ZMod 2) W := by
    simpa only [Atlas.G2.Natural.finrank_space] using LinearMap.finrank_le_finrank_of_surjective hp
  have hhi : Module.finrank (ZMod 2) W ≤ 7 := by
    simpa only [Atlas.G2.Natural.OrthogonalCover.finrank_traceZero] using
      LinearMap.finrank_le_finrank_of_surjective hf
  by_cases hdim : Module.finrank (ZMod 2) W = 6
  · left
    have hinj : Function.Injective p :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (hdim.trans (Atlas.G2.Natural.finrank_space (ZMod 2)).symm)).mpr hp
    let E := (LinearEquiv.ofBijective p ⟨hinj,hp⟩).symm
    have hE (v) : p (E v) = v :=
      (LinearEquiv.ofBijective p ⟨hinj,hp⟩).apply_symm_apply v
    refine ⟨E,?_⟩
    intro a v
    apply hinj
    rw [hE,hact,hE]
  · right
    have hdim : Module.finrank (ZMod 2) W = 7 := by omega
    have hinj : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((Atlas.G2.Natural.OrthogonalCover.finrank_traceZero (ZMod 2)).trans hdim.symm)).mpr hf
    exact ⟨LinearEquiv.ofBijective f ⟨hinj,hf⟩,hfact⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
