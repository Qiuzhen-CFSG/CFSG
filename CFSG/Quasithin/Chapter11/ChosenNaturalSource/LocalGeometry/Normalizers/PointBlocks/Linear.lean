module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Conditions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Point
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.PResidual.CentralizerCorrection

/-!
# The original nonbinary linear point and its Sylow-centralizer comparison

In J=LR₁ the actual Sylow subgroup is S'=T∩J. Normality of J in LT
constructs its Sylow witness; no assertion that T lies in J is needed.
The chosen seed embeds in Z([O₂(J),L]). Thus the natural central section
in C.1.34(3), or its central commutator in (4), is exactly the original V.
Odd-index averaging corrects each S'-central element by a vector of V.
The correction is S'-fixed and lies on the caller's point V₁. Conversely,
a nonidentity vector in V∩Ω₁Z(S') spans that point over the original field.

Consequently C_J(Ω₁Z(S')) = C_L(V₁)R₁ in both central-layer cases.
The literal C.1.34 consumer excludes (5) and reduces (3)--(4) to the
remaining computation O₂(C_L(V₁)R₁)=R₁. The doubled-natural case remains
separate. In particular no whole-core fixed-factor centrality, assumed
radical equality, or conclusion of 11.1.5 is used, including at field four.

The intrinsic classification remains with qt-c134-nonbinary-linear-three-source.
This point consumer and the final normalizer assembly remain with
qt-d-1222-natural-normalizer-source, under the original local-geometry owner.
Source: Aschbacher--Smith, C.1.34, printed pp.136--137, and the first
paragraph of 11.1.5, p.765. The averaging argument reuses the checked
binary point-centralizer method of ChapterC.NaturalPointControl.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual Sylow intersection, on the carrier LR₁. -/
noncomputable def pointSylow : Sylow 2 (L ⊔ f.Ri 0 : Subgroup G) :=
  (NormalSylowQuotientAction.intersection_sylow T (L ⊔ f.Ri 0)
    (le_sup_right.trans (point_join_normalizes D f))).choose

/-- The chosen Sylow has the prescribed original intersection. -/
theorem pointSylow_eq :
    (pointSylow D S f : Subgroup (L ⊔ f.Ri 0 : Subgroup G)) =
      (T : Subgroup G).subgroupOf (L ⊔ f.Ri 0) :=
  (NormalSylowQuotientAction.intersection_sylow T (L ⊔ f.Ri 0)
    (le_sup_right.trans (point_join_normalizes D f))).choose_spec

/-- Its ambient image is T∩LR₁, with the original inclusion. -/
theorem pointSylow_map :
    (pointSylow D S f : Subgroup (L ⊔ f.Ri 0 : Subgroup G)).map (L ⊔ f.Ri 0).subtype =
      (T : Subgroup G) ⊓ (L ⊔ f.Ri 0) := by
  rw [pointSylow_eq,subgroupOf_map_subtype]

/-- The exact Sylow premise of the intrinsic C.1.34 classifier. -/
theorem pointSylow_isSylowIn :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) (L ⊔ f.Ri 0) :=
  ⟨pointSylow D S f,pointSylow_map D S f⟩

/-- The source radical is contained in this Sylow. -/
theorem radical_le_pointSylow : f.Ri 0 ≤ (T : Subgroup G) ⊓ (L ⊔ f.Ri 0) :=
  le_inf (localRadical_le_sylow _) le_sup_right

/-- The original seed lies in O₂(LR₁). -/
theorem seed_le_pointCore : V ≤ (L ⊔ f.Ri 0).pCoreIn 2 :=
  D.le_componentCore.trans (pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer ((localRadical_le_sylow _).trans D.sylow_normalizes_component)))

/-- Relative normality compares the two original local cores. -/
theorem pointCore_le_core : (L ⊔ f.Ri 0).pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  pCoreIn_mono_of_normalizes
    (sup_le le_sup_left ((localRadical_le_sylow _).trans le_sup_right))
    (point_join_normalizes D f)

open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- Full L-movement places V in the literal MS commutator core. -/
theorem seed_le_msQ : V ≤ msQ L (f.Ri 0) :=
  D.eq_commutator.le.trans (commutator_mono (seed_le_pointCore D S f) le_rfl)

/-- Reducedness places the same V in the center of that core. -/
theorem seed_le_msQ_center : V ≤ SourceInterface.centerIn (msQ L (f.Ri 0)) := by
  have hQ : msQ L (f.Ri 0) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (le_normalizer_iff_commutator_le_left.mp
      ((le_sup_left : L ≤ L ⊔ f.Ri 0).trans
        ((L ⊔ f.Ri 0).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))).trans (pointCore_le_core D S f)
  intro v hv
  refine ⟨⟨v,seed_le_msQ D S f hv⟩,mem_center_iff.mpr (fun q => Subtype.ext ?_),rfl⟩
  exact (D.core_centralizes (hQ q.property) v hv).symm

/-- The original seed is contained in the moved central layer. -/
theorem seed_le_center_commutator : V ≤ ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ :=
  D.eq_commutator.le.trans (commutator_mono (seed_le_msQ_center D S f) le_rfl)

variable (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))

include m in
/-- Faithful natural coordinates retain the exact order of V. -/
theorem seed_card : Nat.card V = Nat.card (Fin 3 → S.field.Carrier) :=
  Nat.card_congr (SL3.naturalEquiv D S m).toEquiv

omit [Finite G] in
private theorem section_card {B W F : Type*} [Group B] [AddCommGroup W]
    [Field F] [Module F W] {K A : Subgroup G} {actor : K →* B}
    {rho : Representation F B W} (hm : HasSectionModel K A ⊥ actor rho) :
    Nat.card A = Nat.card W := by
  obtain ⟨_,_,_,hn,e,_⟩ := hm
  let := hn
  let a : A ≃* Multiplicative W := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf A).symm).trans e)
  exact Nat.card_congr a.toEquiv

/-- Case (3) identifies the original center with V by containment and order. -/
theorem center_eq_seed_of_natural
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := S.field.Carrier) 3)) :
    SourceInterface.centerIn (msQ L (f.Ri 0)) = V := by
  apply (Subgroup.eq_of_le_of_card_ge (seed_le_msQ_center D S f) ?_).symm
  rw [section_card h,seed_card D S m]

/-- Case (4) identifies its original moved central layer with V. -/
theorem center_commutator_eq_seed_of_natural
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := S.field.Carrier) 3)) :
    ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ = V := by
  apply (Subgroup.eq_of_le_of_card_ge (seed_le_center_commutator D S f) ?_).symm
  rw [section_card h,seed_card D S m]

/-- A nontrivial Sylow-fixed seed vector excludes C.1.34(5). -/
theorem pointSylow_omega_not_central :
    ¬ SourceInterface.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) ≤
      SourceInterface.centerIn (L ⊔ f.Ri 0) := by
  intro hc
  have hn := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V
    ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))
    (le_inf D.le_sylow (D.le_component.trans le_sup_left))
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans S.sylow_normalizes) D.ne_bot
  apply hn
  apply bot_unique
  apply le_trans _ (Preliminary.sl3_centralizer_eq_bot D S m).le
  apply inf_le_inf_left
  intro z hz l hl
  obtain ⟨w,hw,he⟩ := hc hz
  have hh := congrArg (L ⊔ f.Ri 0).subtype
    (mem_center_iff.mp hw ⟨l,mem_sup_left hl⟩)
  change l * (w : G) = (w : G) * l at hh
  change (w : G) = z at he
  simpa only [he] using hh

/-- The local characteristic-two premise controls the centralizer of its
literal two-core inside J, rather than in the full ambient group. -/
theorem pointCore_selfCentralizing :
    (L ⊔ f.Ri 0) ⊓ centralizer ((L ⊔ f.Ri 0).pCoreIn 2 : Set G) ≤
      (L ⊔ f.Ri 0).pCoreIn 2 := by
  have hc : centralizer (pCore 2 (L ⊔ f.Ri 0 : Subgroup G) : Set (L ⊔ f.Ri 0 : Subgroup G)) ≤
      pCore 2 (L ⊔ f.Ri 0 : Subgroup G) := by
    simpa only [point_join_characteristicTwo D S f] using
      centralizer_generalizedFitting_le (L ⊔ f.Ri 0 : Subgroup G)
  rintro x ⟨hx,hxc⟩
  refine ⟨⟨x,hx⟩,hc ?_,rfl⟩
  intro q hq
  exact Subtype.ext (hxc q (mem_map_of_mem _ hq))

include D S f in
/-- The genuine component is two-perfect on its original carrier. -/
private theorem component_twoPerfect : IsPPerfect 2 L := by
  let : Group.IsPerfect (L.subgroupOf (L ⊔ f.Ri 0)) := (point_join_component D S f).perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ f.Ri 0 from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show L ≤ L ⊔ f.Ri 0 from le_sup_left)).surjective
  intro N hN hQ
  let := hN
  apply eq_top_iff.mpr
  intro l _
  apply (QuotientGroup.eq_one_iff l).mp
  have hs : Subsingleton (L ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hQ.isNilpotent
  exact Subsingleton.elim _ _

/-- A central element of the actual point Sylow can be corrected by a
Sylow-fixed vector of V whenever the central commutator core is V. -/
theorem sylow_fixed_correction
    (hZ : ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ≤ V)
    (z : G) (hzJ : z ∈ L ⊔ f.Ri 0)
    (hz : z ∈ centralizer (((T : Subgroup G) ⊓ (L ⊔ f.Ri 0) : Subgroup G) : Set G)) :
    ∃ v ∈ V ⊓ centralizer (((T : Subgroup G) ⊓ (L ⊔ f.Ri 0) : Subgroup G) : Set G),
      v⁻¹ * z ∈ centralizer (L : Set G) := by
  let J := L ⊔ f.Ri 0
  let A := (T : Subgroup G) ⊓ J
  let N := J.pCoreIn 2
  let := D.elementary
  have hNA : N ≤ A := by
    have h := pCoreIn_le_sylow J (pointSylow D S f)
    rwa [pointSylow_map] at h
  have hLQ : L ≤ normalizer (N : Set G) :=
    (le_sup_left : L ≤ J).trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hQN : msQ L (f.Ri 0) ≤ N := le_normalizer_iff_commutator_le_left.mp hLQ
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component
  have hPA : (P : Subgroup L).map L.subtype ≤ A := by
    rw [hP,subgroupOf_map_subtype]
    exact inf_le_inf_left _ le_sup_left
  obtain ⟨v,hv,hc⟩ := fixed_correction_of_center_commutator L N V
    (component_twoPerfect D S f) (pCore_isPGroup.map J.subtype) hLQ D.normalizes
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) hZ P z
    (pointCore_selfCentralizing D S m f ⟨hzJ,centralizer_le hNA hz⟩)
    (centralizer_le (hQN.trans hNA) hz) (centralizer_le hPA hz)
  refine ⟨v,⟨hv.1,?_⟩,hc⟩
  intro s hs
  let v' := s * v * s⁻¹
  let b := v⁻¹ * z
  let b' := s * b * s⁻¹
  have hv' : v' ∈ V := (S.sylow_normalizes hs.1 v).mp hv.1
  have hb' : b' ∈ centralizer (L : Set G) :=
    ((normalizer_le_normalizer_centralizer L (D.sylow_normalizes_component hs.1)) b).mp hc
  have hp : v' * b' = v * b := by
    calc
      v' * b' = s * (v * b) * s⁻¹ := by dsimp [v',b']; group
      _ = s * z * s⁻¹ := by simp only [b,mul_inv_cancel_left]
      _ = z := by rw [hz s hs,mul_inv_cancel_right]
      _ = v * b := (mul_inv_cancel_left v z).symm
  have hd : v⁻¹ * v' = b * b'⁻¹ := by
    calc
      v⁻¹ * v' = v⁻¹ * (v' * b') * b'⁻¹ := by group
      _ = v⁻¹ * (v * b) * b'⁻¹ := by rw [hp]
      _ = b * b'⁻¹ := by group
  have he : v⁻¹ * v' = 1 := by
    apply mem_bot.mp
    rw [← Preliminary.sl3_centralizer_eq_bot D S m]
    refine ⟨V.mul_mem (V.inv_mem hv.1) hv',?_⟩
    rw [hd]
    exact (centralizer _).mul_mem hc ((centralizer _).inv_mem hb')
  exact mul_inv_eq_iff_eq_mul.mp ((inv_mul_eq_one.mp he).symm : v' = v)

/-- The correction lies on the actual point of the caller's flag. -/
theorem omega_point_correction
    (hZ : ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ≤ V)
    (z : G) (hz : z ∈ Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))) :
    ∃ v ∈ f.Vi 0, v⁻¹ * z ∈ centralizer (L : Set G) := by
  obtain ⟨hzS,hzc,_⟩ := (mem_omegaCenterIn_iff _ _).mp hz
  obtain ⟨v,hv,hc⟩ := sylow_fixed_correction D S m f hZ z hzS.2 hzc
  refine ⟨v,?_,hc⟩
  rw [← PointCohomology.PointGeometry.SL3Core.local_core_fixed D S m f]
  refine ⟨hv.1,centralizer_le ?_ hv.2⟩
  apply le_trans _ (radical_le_pointSylow D S f)
  exact pCoreIn_mono_of_normalizes le_sup_left
    (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))

/-- Pointwise fixation of the source point detects all Sylow-central
involutions inside the original component in the two central-layer rows. -/
theorem point_fixer_centralizes_omega
    (hZ : ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ≤ V) :
    L ⊓ centralizer (f.Vi 0 : Set G) ≤
      centralizer (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G) := by
  rintro l ⟨hl,hfix⟩ z hz
  obtain ⟨v,hv,hc⟩ := omega_point_correction D S m f hZ z hz
  calc
    z * l = (v * (v⁻¹ * z)) * l := by rw [mul_inv_cancel_left]
    _ = v * ((v⁻¹ * z) * l) := mul_assoc _ _ _
    _ = v * (l * (v⁻¹ * z)) := by rw [← hc l hl]
    _ = (v * l) * (v⁻¹ * z) := (mul_assoc _ _ _).symm
    _ = (l * v) * (v⁻¹ * z) := by rw [hfix v hv]
    _ = l * z := by rw [mul_assoc,mul_inv_cancel_left]

/-- Apply the correction to both actual central-layer alternatives of C.1.34.
The field-four fixed factor is never required to be central in LR₁. -/
theorem central_cases_point_fixer
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := S.field.Carrier) 3) ∨
      HasSectionModel L ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := S.field.Carrier) 3)) :
    L ⊓ centralizer (f.Vi 0 : Set G) ≤
      centralizer (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G) := by
  apply point_fixer_centralizes_omega D S m f
  rcases h with h | h
  · rw [center_eq_seed_of_natural D S m f e h,← D.eq_commutator]
  · exact (center_commutator_eq_seed_of_natural D S m f e h).le


/-- A nonzero Sylow-central seed vector lies on the actual field point. -/
theorem exists_nontrivial_point_omega :
    ∃ v ∈ f.Vi 0, v ≠ 1 ∧
      v ∈ Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) := by
  have hn := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V
    ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))
    (le_inf D.le_sylow (D.le_component.trans le_sup_left))
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans S.sylow_normalizes) D.ne_bot
  obtain ⟨v,hv,hv1⟩ := (V ⊓ Subgroup.omegaCenterIn
    ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))).bot_or_exists_ne_one.resolve_left hn
  refine ⟨v,?_,hv1,hv.2⟩
  rw [← PointCohomology.PointGeometry.SL3Core.local_core_fixed D S m f]
  refine ⟨hv.1,centralizer_le ?_ ((mem_omegaCenterIn_iff _ _).mp hv.2).2.1⟩
  apply le_trans _ (radical_le_pointSylow D S f)
  exact pCoreIn_mono_of_normalizes le_sup_left
    (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))

set_option backward.isDefEq.respectTransparency false in
/-- In the component, fixing one nonidentity vector of the point fixes the
whole field line. This uses the original faithful natural marking. -/
theorem fixes_point_of_nontrivial_vector (l : L) (v : G) (hv : v ∈ f.Vi 0)
    (hv1 : v ≠ 1) (hfix : (l : G) * v = v * (l : G)) :
    (l : G) ∈ centralizer (f.Vi 0 : Set G) := by
  let c := Coordinates.sl3 m
  let vV : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  let w : Fin 3 → S.field.Carrier := (c.projection vV).toAdd
  have hw : w ∈ f.space 0 := (c.mem_preimage _ vV).mp hv
  have hw0 : w ≠ 0 := by
    intro hz
    apply hv1
    exact congrArg Subtype.val ((SL3.projection_injective D S m)
      (show c.projection vV = c.projection 1 from
        (congrArg Multiplicative.ofAdd hz).trans (map_one _).symm))
  have he : c.modelAction (c.quotientMap l) w = w := by
    apply (PointCohomology.PointGeometry.SL3Core.projection_fixed_iff D S m l vV).mpr
    apply Subtype.ext
    change (l : G) * v * (l : G)⁻¹ = v
    rw [hfix,mul_inv_cancel_right]
  intro u hu
  let uV : V := ⟨u,D.centralQuotientPreimage_le _ hu⟩
  have hspan : f.space 0 = Submodule.span S.field.Carrier {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (f.dimension 0) hw hw0
  have huW : (c.projection uV).toAdd ∈ Submodule.span S.field.Carrier {w} :=
    hspan ▸ (c.mem_preimage _ uV).mp hu
  obtain ⟨a,ha⟩ : ∃ a : S.field.Carrier, a • w = (c.projection uV).toAdd :=
    Submodule.mem_span_singleton.mp huW
  have huFix : c.modelAction (c.quotientMap l) (c.projection uV).toAdd =
      (c.projection uV).toAdd := by
    rw [← ha,map_smul,he]
  have hc := congrArg Subtype.val
    ((PointCohomology.PointGeometry.SL3Core.projection_fixed_iff D S m l uV).mp huFix)
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- The original Sylow omega centralizer in L lies in the literal point fixer. -/
theorem omega_fixer_le_point_fixer :
    L ⊓ centralizer (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G) ≤
      L ⊓ centralizer (f.Vi 0 : Set G) := by
  obtain ⟨v,hv,hv1,hvz⟩ := exists_nontrivial_point_omega D S m f
  rintro l ⟨hl,hc⟩
  exact ⟨hl,fixes_point_of_nontrivial_vector D S m f ⟨l,hl⟩ v hv hv1 (hc v hvz).symm⟩

/-- The actual centralizer comparison for both central-layer rows, retaining
S'=T intersect LR₁ throughout. -/
theorem central_cases_component_centralizer
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := S.field.Carrier) 3) ∨
      HasSectionModel L ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := S.field.Carrier) 3)) :
    L ⊓ centralizer (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G) =
      L ⊓ centralizer (f.Vi 0 : Set G) := by
  apply le_antisymm (omega_fixer_le_point_fixer D S m f)
  exact le_inf inf_le_left (central_cases_point_fixer D S m f e h)


/-- Since R₁ lies in the actual Sylow, the omega centralizer in LR₁ is
the product of R₁ with its component centralizer. -/
theorem omega_centralizer_join :
    (L ⊔ f.Ri 0) ⊓ centralizer
      (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G) =
    (L ⊓ centralizer
      (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G)) ⊔ f.Ri 0 := by
  let Z := Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))
  have hRC : f.Ri 0 ≤ centralizer (Z : Set G) := by
    intro r hr z hz
    exact (((mem_omegaCenterIn_iff _ _).mp hz).2.1 r
      (radical_le_pointSylow D S f hr)).symm
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    have hp : x ∈ (L : Set G) * (f.Ri 0 : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (f.Ri 0)
        ((localRadical_le_sylow _).trans D.sylow_normalizes_component)]
      exact hx
    obtain ⟨l,hl,r,hr,rfl⟩ := hp
    have hlc : l ∈ centralizer (Z : Set G) :=
      (mul_mem_cancel_right (hRC hr)).mp hc
    exact mul_mem_sup ⟨hl,hlc⟩ hr
  · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hRC)

/-- Literal LR₁ centralizer comparison in the two central-layer alternatives.
This is the centralizer whose two-core occurs in C.1.34, with no ambient-T
Sylow substitution and no assumed radical equality. -/
theorem central_cases_join_centralizer
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := S.field.Carrier) 3) ∨
      HasSectionModel L ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := S.field.Carrier) 3)) :
    (L ⊔ f.Ri 0) ⊓ centralizer
      (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G) =
      (L ⊓ centralizer (f.Vi 0 : Set G)) ⊔ f.Ri 0 := by
  rw [omega_centralizer_join D S m f,central_cases_component_centralizer D S m f e h]

/-- The exact C.1.34 consumer reduces the central-layer cases to the
literal point-fixer core calculation. The doubled-natural case remains
separate, and the binary exceptional case has already been excluded. -/
theorem alternatives_point_fixer_core
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : MSModuleAlternatives L (f.Ri 0) ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))
      S.field.degree S.field.Carrier e) :
    ChapterC.IsSL3EvenBlock L S.field.degree ∨
    (HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := S.field.Carrier) 3).prod
        (Representation.specialLinearNatural (k := S.field.Carrier) 3)) ∧
      MSNotCentralizerCore L (f.Ri 0) ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))) ∨
    f.Ri 0 ≠ ((L ⊓ centralizer (f.Vi 0 : Set G)) ⊔ f.Ri 0).pCoreIn 2 := by
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1.2.1
  · exact Or.inr (Or.inl h2)
  · apply Or.inr ∘ Or.inr
    have hn := h3.2.2
    change f.Ri 0 ≠ ((L ⊔ f.Ri 0) ⊓ centralizer
      (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G)).pCoreIn 2 at hn
    rwa [central_cases_join_centralizer D S m f e (Or.inl h3.1)] at hn
  · apply Or.inr ∘ Or.inr
    have hn := h4.2.2.2.2.2.2.2.2.2
    change f.Ri 0 ≠ ((L ⊔ f.Ri 0) ⊓ centralizer
      (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G)).pCoreIn 2 at hn
    rwa [central_cases_join_centralizer D S m f e (Or.inr h4.2.2.2.2.2.1)] at hn
  · exact (pointSylow_omega_not_central D S m f h5.2.2.2.1).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
