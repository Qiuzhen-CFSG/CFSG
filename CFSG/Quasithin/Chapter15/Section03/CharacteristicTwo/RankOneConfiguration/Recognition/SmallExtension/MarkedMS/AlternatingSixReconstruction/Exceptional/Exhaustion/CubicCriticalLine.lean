module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.DistanceTwoCubic
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.GroupTheory.Commutator.NormalClosureSupplement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Transposition

/-!
# The cubic-kernel critical transposition

At distance two the actual natural quotient actor is S₆. The entire initial
moved cover, including its fixed attachment, is a quotient of the six-letter
augmentation module. Quadraticity of the opposite Q-image therefore puts
the source commutator in its central omega layer, and Frattini detection
contradicts the retained cubic initial kernel.

The opposite image centralizes the critical X-image and fixes its natural
movement. The finite nonquadratic-fixer theorem now makes every nonidentity
critical image element a transposition. Sign then gives order two. The
source Z-image is the same nontrivial image, although Z and X themselves
remain distinct. Finally sign kills the image of every commutator contained
in that critical layer; its two-group structure removes the odd E/Q kernel.

This proves the critical-line reduction and excludes every larger critical
image. The remaining transposition orbit argument and all larger-distance
branches remain obligations of the reconstruction owner. Whole-core and
literal rank-two applications are in CubicCriticalLine/Source.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), (3.6), pp.866--871;
Aschbacher--Smith I.1.5--6, p.408, for the universal moved cover. The finite
six-letter fixer proof is reused from Natural/Exhaustion/DistanceTwo.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "X₀" => centralOmega L R
local notation "q" => QuotientGroup.mk' (layerKernel L R)
local notation "π" => projection h e hz hk
local notation "s" => layerSection h
local notation "ρ₆" => BinaryPermutation.naturalRepresentation (Fin 6)

/-- The entire initial moved cover, with its original six-letter marking. -/
theorem moved_cover_model (hb : sourceDistance h = 2) :
    BinaryPermutation.SixCover.IsNaturalOrCore (s).space.toRepresentation
      (permutationAction h e hz hk) := by
  let E : LayerActor L R ≃* Equiv.Perm (Fin 6) :=
    MulEquiv.ofBijective (permutationAction h e hz hk)
      ⟨permutationAction_injective h e hz hk, fun g => by
        obtain ⟨m,hm⟩ := projection_surjective_of_distanceTwo h e hz hk hb g
        exact ⟨q m,hm⟩⟩
  let c := coordinates h e hz hk
  let p := ((s).coverProjection c).toLinearMap
  have hC : (layerComponent L R).map E.toMonoidHom = alternatingGroup (Fin 6) := by
    change ((K).map q).map (permutationAction h e hz hk) = _
    rw [map_map]
    exact component_image h e hz hk
  have hp (g : LayerActor L R) (v : (s).space.toSubmodule) :
      p ((s).space.toRepresentation g v) = ρ₆ (E g) (p v) := by
    exact ((s).coverProjection_ambient c g v).trans
      (permutationAction_apply h e hz hk g (p v))
  have hsur : Function.Surjective p :=
    ((s).coverProjection_isCover (layer_moved_alternating h e hz hk).1 c).1
  have hker : p.ker ≤ fixedSpace (s).space.toRepresentation (layerComponent L R) := by
    intro v hv
    have hzv : (s).central.toSubmodule.mkQ v = 0 :=
      c.linearEquiv.injective (hv.trans c.linearEquiv.map_zero.symm)
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hzv
    rwa [(s).central_eq] at hm
  have hgen : subspaceCommutator (s).space.toRepresentation ⊤ (layerComponent L R) = ⊤ := by
    have hi := (layer_moved_alternating h e hz hk).1
    have hm : (s).space.toSubmodule ≤
        (subspaceCommutator (s).space.toRepresentation ⊤ (layerComponent L R)).map
          (s).space.toSubmodule.subtype := by
      have hi' : IsIrrPlus (layerAction L R) (layerComponent L R) (s).space.toSubmodule :=
        (s).space_eq.symm ▸ hi
      conv_lhs => rw [←hi'.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact ⟨(s).space.toRepresentation g ⟨v,hv⟩-⟨v,hv⟩,
        Submodule.subset_span ⟨g,hg,⟨v,hv⟩,Submodule.mem_top,rfl⟩,rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w,hw,he⟩ := hm v.property
    rwa [show w=v from Subtype.ext he] at hw
  exact BinaryPermutation.SixCover.naturalOrCore_symmetric (s).space.toRepresentation E
    (layerComponent L R) hC p hp hsur hker hgen

/-- The augmentation cover surjects onto the entire initial moved space. -/
theorem moved_space_surjection (hb : sourceDistance h = 2) :
    ∃ f : BinaryPermutation.core (Fin 6) →ₗ[ZMod 2] (s).space.toSubmodule,
      Function.Surjective f ∧ ∀ g v,
        f (BinaryPermutation.coreRepresentation (Fin 6) (π g) v) =
          (s).space.toRepresentation (q g) (f v) := by
  rcases moved_cover_model h e hz hk hb with ⟨E,hE⟩ | ⟨E,hE⟩
  · refine ⟨E.symm.toLinearMap.comp (BinaryPermutation.coreToNatural (Fin 6)),
      E.symm.surjective.comp BinaryPermutation.coreToNatural_surjective,?_⟩
    intro g v
    apply E.injective
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,E.apply_symm_apply,hE]
    exact BinaryPermutation.coreToNatural_equivariant _ _
  · refine ⟨E.symm.toLinearMap,E.symm.surjective,?_⟩
    intro g v
    apply E.injective
    simp only [LinearEquiv.coe_coe,E.apply_symm_apply,hE]
    rfl

/-- Original subgroup coordinates on the entire initial moved cover. -/
theorem moved_subgroup_surjection (hb : sourceDistance h = 2) :
    let := h.relative_normal
    let : IsElementaryAbelian 2 (⁅X₀,K⁆ : Subgroup M) :=
      IsElementaryAbelian.of_le (commutator_le_left X₀ K)
    ∃ f : BinaryPermutation.core (Fin 6) →ₗ[ZMod 2] Additive (⁅X₀,K⁆ : Subgroup M),
      Function.Surjective f ∧ ∀ g v,
        (f (BinaryPermutation.coreRepresentation (Fin 6) (π g) v)).toMul =
          MulAut.conjNormal g (f v).toMul := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 (⁅X₀,K⁆ : Subgroup M) :=
    IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  let E := NormalElementaryQuotient.movedEquiv X₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K
  obtain ⟨f,hf,he⟩ := moved_space_surjection h e hz hk hb
  refine ⟨E.symm.toLinearMap.comp f,E.symm.surjective.comp hf,?_⟩
  intro g v
  have hh := he g v
  change (E.symm (f (_))).toMul = _
  rw [hh]
  apply Subtype.ext
  have hval (w : (s).space.toSubmodule) :
      ((E.symm w).toMul : M) = w.val.toMul.val :=
    congrArg (fun z : (s).space.toSubmodule => z.val.toMul.val) (E.apply_symm_apply w)
  change ((E.symm ((s).space.toRepresentation (q g) (f v))).toMul : M) =
    g*((E.symm (f v)).toMul : M)*g⁻¹
  rw [hval,hval]
  exact NormalElementaryQuotient.representation_apply X₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g (f v).val

/-- Quadraticity on the whole augmentation cover controls the literal
initial commutator, including its possible central line. -/
theorem moved_commutator_central_of_quadratic_image
    (hb : sourceDistance h = 2) (B : Subgroup M)
    (hquad : IsQuadratic (BinaryPermutation.coreRepresentation (Fin 6)) (B.map π)) :
    ⁅⁅X₀,K⁆,B⁆ ≤ centralizer (B : Set M) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 (⁅X₀,K⁆ : Subgroup M) :=
    IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  obtain ⟨f,hf,hact⟩ := moved_subgroup_surjection h e hz hk hb
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hbB w hw y hy
  obtain ⟨v,hv⟩ := hf (Additive.ofMul (⟨w,hw⟩ : (⁅X₀,K⁆ : Subgroup M)))
  let δ := BinaryPermutation.coreRepresentation (Fin 6) (π b) v-v
  have he : (f δ).toMul = MulAut.conjNormal b (f v).toMul * (f v).toMul⁻¹ := by
    dsimp only [δ]
    rw [map_sub,toMul_sub,div_eq_mul_inv,hact]
  have hfixed : MulAut.conjNormal y (f δ).toMul = (f δ).toMul := by
    rw [←hact]
    change (f (BinaryPermutation.coreRepresentation (Fin 6) (π y)
      (BinaryPermutation.coreRepresentation (Fin 6) (π b) v-v))).toMul = _
    rw [hquad _ (mem_map_of_mem π hy) _ (mem_map_of_mem π hbB)]
  have heval : ((f δ).toMul : M) = ⁅b,w⁆ := by
    rw [he,hv]
    rfl
  have hh := congrArg Subtype.val hfixed
  change y*((f δ).toMul : M)*y⁻¹ = ((f δ).toMul : M) at hh
  rw [heval] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
local notation "T" => edge L R

include h e hz in
/-- The source orbit equals its whole moved cover joined with the edge seed. -/
theorem orbit_eq_moved_sup_seed :
    ChapterC.MSCentralOrbit.omegaOrbit T = ⁅X₀,K⁆ ⊔ omegaCenter T := by
  let := h.relative_normal
  let H := ChapterC.MSCentralOrbit.omegaOrbit T
  have hHK : ⁅H,K⁆ = ⁅X₀,K⁆ := omegaOrbit_moved_eq h e hz
  have hHM : ⁅H,(⊤ : Subgroup M)⁆ ≤ ⁅X₀,K⁆ := by
    change ⁅normalClosure (omegaCenter T : Set M),(⊤ : Subgroup M)⁆ ≤ _
    rw [normalClosure_commutator_eq_of_centralizing_supplement
      (omegaCenter T) K T (codisjoint_subgroupOf_sup L R).eq_top
      (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)]
    rw [←hHK]
    exact commutator_mono le_normalClosure le_rfl
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    have hc : ⁅g,a⁆ ∈ ⁅X₀,K⁆ := by
      apply hHM
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top g) (subset_normalClosure ha)
    have he : g*a*g⁻¹ = ⁅g,a⁆*a := by simp [commutatorElement_def,mul_assoc]
    rw [he]
    exact mul_mem (mem_sup_left hc) (mem_sup_right ha)
  · apply sup_le _ le_normalClosure
    rw [←hHK]
    exact commutator_le_left H K

include h e hz in
/-- The literal graph layer retains its fixed edge attachment. -/
theorem graph_Z_eq_moved_sup_edge {t : Vertex T} (hat : Adjacent T (alpha T) t) :
    Z T (alpha T) = (⁅X₀,K⁆).map (embedM T) ⊔ Z T t := by
  have hbase : Z T (alpha T) = (⁅X₀,K⁆).map (embedM T) ⊔ Z T (beta T) := by
    rw [graph_Z,orbit_eq_moved_sup_seed h e hz,Subgroup.map_sup]
    congr 1
    rw [Z,if_neg (by exact Bool.noConfusion : color T (beta T) ≠ false),
      edgeOmega,Q_beta,omegaCenter_map _ _ (embedM_injective T)]
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors T (alpha T) (base_adjacent T) hat
  have he := congrArg (fun A : Subgroup (FreeAmalgam T) =>
    A.map (MulAut.conj g⁻¹).toMonoidHom) hbase
  change act T g (alpha T) = alpha T at hg
  change act T g (beta T) = t at hgt
  have hmove : (⁅X₀,K⁆).map (embedM T) = ⁅X T (alpha T),Ltilde T (alpha T)⁆ := by
    rw [graph_X h,graph_component h,map_commutator]
  rw [Subgroup.map_sup,hmove,map_commutator,←Z_act,←X_act,←Ltilde_act,←Z_act,hg,hgt,
    ←hmove] at he
  exact he

/-- Quadraticity of the opposite Q-image forces the actual critical
commutator into X at that endpoint. -/
theorem opposite_commutator_le_X_of_quadratic_image
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hquad : IsQuadratic (BinaryPermutation.coreRepresentation (Fin 6))
      (graphImage h e hz hk (Q T c))) :
    ⁅Q T c,Z T (alpha T)⁆ ≤ X T c := by
  obtain ⟨t,hat,hct,_,_⟩ := distanceTwo_source_actor h e hb c hc
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hat
    change false ≠ color T t at hh
    cases hcol : color T t <;> simp_all
  have hQH : Q T c ≤ stabilizer T (alpha T) :=
    (Q_le_adjacent_h T ht hct).trans (fun _ hx => hx.2 _ (adjacent_symm T hat))
  let B := (Q T c).comap (embedM T)
  have hBm : B.map (embedM T) = Q T c :=
    map_comap_eq_self (hQH.trans_eq (stabilizer_m_base T))
  have hZt : Z T t ≤ centralizer (Q T c : Set (FreeAmalgam T)) := by
    simp only [Z,ht,Bool.true_eq_false,if_false,edgeOmega]
    intro z hzT y hy
    exact (mem_omegaCenter_iff.mp hzT).2.2 y (Q_le_adjacent_h T ht hct hy)
  let D := (Z T t).comap (embedM T)
  have hDH : Z T t ≤ stabilizer T (alpha T) := by
    simp only [Z,ht,Bool.true_eq_false,if_false,edgeOmega]
    exact (omegaCenter_le _).trans (fun _ hx => hx.2 _ (adjacent_symm T hat))
  have hDm : D.map (embedM T) = Z T t :=
    map_comap_eq_self (hDH.trans_eq (stabilizer_m_base T))
  have hDB : D ≤ centralizer (B : Set M) := by
    intro z hzD y hy
    apply embedM_injective T
    simpa only [map_mul] using hZt hzD (embedM T y) hy
  have hwhole0 : ⁅⁅X₀,K⁆ ⊔ D,B⁆ ≤ centralizer (B : Set M) := by
    let := h.relative_normal
    apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨w,hw,z,hzD,rfl⟩ := mem_sup_of_normal_left.mp hx
    have hzy : Commute z y := (hDB hzD y hy).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzy.commutator_eq]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact moved_commutator_central_of_quadratic_image h e hz hk hb B hquad
      (commutator_mem_commutator hw hy)
  have hwhole : ⁅Q T c,Z T (alpha T)⁆ ≤ centralizer (Q T c : Set (FreeAmalgam T)) := by
    rw [commutator_comm,graph_Z_eq_moved_sup_edge h e hz hat,←hDm,←hBm,
      ←Subgroup.map_sup,←map_commutator]
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    simpa only [map_mul] using congrArg (embedM T) (hwhole0 hx y hy)
  have hZa : Z T (alpha T) ≤ X T (alpha T) :=
    (sourceGeometry h).omega_bound _ rfl (sourceDistance_pos h)
  have hQ : ⁅Q T c,Z T (alpha T)⁆ ≤ Q T c :=
    le_normalizer_iff_commutator_le_left.mp
      ((hZa.trans (critical_X_le_vertex h e (alpha T) rfl c hc)).trans (Q_normalized T c))
  have hZ : ⁅Q T c,Z T (alpha T)⁆ ≤ Z T (alpha T) :=
    le_normalizer_iff_commutator_le_right.mp (hQH.trans (Z_normalized T (alpha T)))
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hQ hx,
    (mem_omegaCenter_iff.mp (hZa (hZ hx))).2.1,hwhole hx⟩

/-- The quadratic-image test gives exhaustion of the original whole core. -/
theorem coreExhaustion_of_opposite_quadratic_image
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hquad : IsQuadratic (BinaryPermutation.coreRepresentation (Fin 6))
      (graphImage h e hz hk (Q T c))) : CoreExhaustion L R := by
  have hbound := opposite_commutator_le_X_of_quadratic_image h e hz hk hb c hc hquad
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hcCol
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hgcCol : color T (act T g⁻¹ c) = false := by rw [hg];rfl
  have hc' := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hcCol)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hgcCol)).mpr hr
  have hd : CriticalPair T (alpha T) (act T g⁻¹ (alpha T))
      ((sourceGeometry h).exists_critical (alpha T) rfl) := by simpa only [hg] using hc'
  have hm := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hbound
  rw [map_commutator,←Q_act,←Z_act,←X_act,hg] at hm
  exact coreExhaustion_of_critical_commutator_le h e hz _ hd (hm.trans le_sup_right)

/-- No opposite critical Q-image is quadratic on the entire augmentation
cover when the central cubic acts trivially on the initial layer. -/
theorem opposite_image_nonquadratic
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    ¬ IsQuadratic (BinaryPermutation.coreRepresentation (Fin 6))
      (graphImage h e hz hk (Q T c)) := by
  intro hquad
  have hx := coreExhaustion_of_opposite_quadratic_image h e hz hk hb c hc hquad
  have he : extensionKernel h = pCore 2 M := hk.symm.trans (centralOmega_centralizer h hx)
  have hi := extensionKernel_core_index h hz
  have htop : pCore 2 (extensionKernel h) = ⊤ := by
    apply map_injective (extensionKernel h).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact (extensionKernel_twoCore h).trans he.symm
  rw [htop,index_top] at hi
  norm_num at hi

/-- Centralization on the actual X-layer descends to fixation of natural
quotient displacement. -/
theorem image_fixes_moved_of_centralizes (A B : Subgroup M)
    (hcent : B ≤ centralizer ((⁅X₀,A⁆ : Subgroup M) : Set M)) :
    B.map π ≤ subspaceKernel ρ₆ (subspaceCommutator ρ₆ ⊤ (A.map π)) ⊤ := by
  let p := ((s).coverProjection (coordinates h e hz hk)).toLinearMap
  have hp (g : M) (v : (s).space.toSubmodule) :
      p ((s).space.toRepresentation (q g) v) = ρ₆ (π g) (p v) :=
    ((s).coverProjection_ambient (coordinates h e hz hk) (q g) v).trans
      (permutationAction_apply h e hz hk (q g) (p v))
  have hsur : Function.Surjective p :=
    ((s).coverProjection_isCover (layer_moved_alternating h e hz hk).1
      (coordinates h e hz hk)).1
  rintro _ ⟨b,hbB,rfl⟩
  refine ⟨mem_top _,?_⟩
  have hspace : subspaceCommutator ρ₆ ⊤ (A.map π) ≤ LinearMap.ker (ρ₆ (π b)-LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,_,rfl⟩
    obtain ⟨w,hw⟩ := hsur v
    let δ : (s).space.toSubmodule := (s).space.toRepresentation (q a) w-w
    have hdval : (δ.val.toMul : M) = ⁅a,(w.val.toMul : M)⁆ := by
      change ((layerAction L R (q a) w.val-w.val).toMul : M) = _
      rw [toMul_sub,div_eq_mul_inv]
      change ((layerAction L R (q a) w.val).toMul : M) * (w.val.toMul : M)⁻¹ = _
      rw [show ((layerAction L R (q a) w.val).toMul : M) =
        a*(w.val.toMul : M)*a⁻¹ from NormalElementaryQuotient.representation_apply X₀ q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) a w.val]
      rfl
    have hdmem : (δ.val.toMul : M) ∈ ⁅X₀,A⁆ := by
      rw [hdval,commutator_comm]
      exact commutator_mem_commutator ha w.val.toMul.property
    have hd : (s).space.toRepresentation (q b) δ = δ := by
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((layerAction L R (q b) δ.val).toMul : M) = _
      rw [show ((layerAction L R (q b) δ.val).toMul : M) =
        b*(δ.val.toMul : M)*b⁻¹ from NormalElementaryQuotient.representation_apply X₀ q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) b δ.val,
        ←hcent hbB _ hdmem,mul_inv_cancel_right]
    have hδ : p δ = ρ₆ (π a) v-v := by
      dsimp only [δ]
      rw [map_sub,hp,hw]
    change ρ₆ (π b) (ρ₆ (π a) v-v) - (ρ₆ (π a) v-v) = 0
    rw [←hδ,←hp,hd,sub_self]
  intro v hv
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hspace hv

/-- The opposite Q-image fixes the movement of the critical X-image in
its literal natural quotient coordinates. -/
theorem critical_image_fixer (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    graphImage h e hz hk (Q T c) ≤ subspaceKernel ρ₆
      (subspaceCommutator ρ₆ ⊤ (graphImage h e hz hk (X T c))) ⊤ := by
  apply image_fixes_moved_of_centralizes h e hz hk
  intro b hbB x hx
  apply embedM_injective T
  simp only [map_mul]
  apply Q_le_centralizer_X T c hbB
  have hm := mem_map_of_mem (embedM T) hx
  rw [map_commutator,←graph_X h] at hm
  exact ((commutator_mono le_rfl (map_comap_le _ _)).trans
    ((critical_X_commutator_le h e (alpha T) rfl c hc).trans inf_le_right)) hm

/-- Every nontrivial critical X-image is a transposition. The larger
Q-image and its nonquadratic whole-cover action are derived, not assumed. -/
theorem critical_image_isSwap (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    {a : Equiv.Perm (Fin 6)} (ha : a ∈ graphImage h e hz hk (X T c))
    (ha1 : a ≠ 1) : a.IsSwap := by
  let A := graphImage h e hz hk (X T c)
  let B := graphImage h e hz hk (Q T c)
  have hel := (critical_image_data h e hz hk c hc).1
  let := hel.2
  have hcol := critical_endpoint_color T (alpha T) rfl _ hc
  have hp : IsPGroup 2 ((Q T c).comap (embedM T)) :=
    (Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le c hcol).of_injective
      ((embedM T).subgroupComap (Q T c)) (by
        intro x y hh
        exact Subtype.ext ((embedM_injective T) (congrArg Subtype.val hh)))
  have hcent : B ≤ centralizer (A : Set (Equiv.Perm (Fin 6))) := by
    rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩
    have hh := Q_le_centralizer_X T c hy (embedM T x) hx
    have he : x*y=y*x := (embedM_injective T) (by simpa only [map_mul] using hh)
    simpa only [map_mul] using congrArg π he
  exact Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.isSwap_of_nonquadratic_fixer A B
    (hp.map π) (map_mono (comap_mono (omegaCenter_le _))) hcent
    (critical_image_fixer h e hz hk c hc)
    (opposite_image_nonquadratic h e hz hk hb c hc) ha ha1
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)

/-- The remaining critical image has exactly order two; all order-four
images are excluded while retaining the cubic covering kernel. -/
theorem critical_image_card_two (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    Nat.card (graphImage h e hz hk (X T c)) = 2 := by
  let A := graphImage h e hz hk (X T c)
  have hne := (critical_image_data h e hz hk c hc).1.1
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hswap := critical_image_isSwap h e hz hk hb c hc ht ht1
  have he : A = zpowers t := by
    apply le_antisymm ?_ (zpowers_le.mpr ht)
    intro a ha
    by_cases h1 : a=1
    · rw [h1];exact one_mem _
    have haSwap := critical_image_isSwap h e hz hk hb c hc ha h1
    have hat : a*t⁻¹=1 := by
      by_contra hnon
      have hh := critical_image_isSwap h e hz hk hb c hc (A.mul_mem ha (A.inv_mem ht)) hnon
      have hs := hh.sign_eq
      rw [map_mul,map_inv,haSwap.sign_eq,hswap.sign_eq] at hs
      norm_num at hs
    rw [mul_inv_eq_one.mp hat]
    exact mem_zpowers t
  change Nat.card A = 2
  rw [he,Nat.card_zpowers,hswap.orderOf]

include h e hz hk in
/-- Exact source Q-index for every cubic-kernel distance-two critical pair. -/
theorem critical_core_index_two (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    (Q T (alpha T)).relIndex (X T c) = 2 :=
  (critical_image_data h e hz hk c hc).2.symm.trans
    (critical_image_card_two h e hz hk hb c hc)

/-- Sign detects every nonidentity element of the critical image. -/
theorem critical_image_eq_zpowers_transposition (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      graphImage h e hz hk (X T c) = zpowers t := by
  let A := graphImage h e hz hk (X T c)
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left
    (critical_image_data h e hz hk c hc).1.1
  have hs := critical_image_isSwap h e hz hk hb c hc ht ht1
  refine ⟨t,hs,?_⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr ht) ?_).symm
  rw [critical_image_card_two h e hz hk hb c hc,Nat.card_zpowers,hs.orderOf]

include h e hz hk in
/-- A commutator contained in the critical X-layer has trivial natural
image. Its two-group structure then removes the retained odd kernel E/Q,
placing it in the literal original Q rather than merely in E. -/
theorem critical_commutator_le_base_core (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (A B : Subgroup M)
    (hcomm : ⁅A,B⁆ ≤ (X T c).comap (embedM T)) : ⁅A,B⁆ ≤ pCore 2 M := by
  let : IsElementaryAbelian 2 (X T c) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((X T c).comap (embedM T)) :=
    IsElementaryAbelian.comap_of_injective _ (embedM_injective T) _
  let : IsElementaryAbelian 2 (⁅A,B⁆ : Subgroup M) := IsElementaryAbelian.of_le hcomm
  apply two_subgroup_le_core_of_le_extensionKernel h hz ⁅A,B⁆
    (IsElementaryAbelian.isPGroup 2 _) ?_
  rw [←projection_kernel h e hz hk]
  have heven : ⁅A,B⁆ ≤ (Equiv.Perm.sign.comp π).ker := by
    apply commutator_le.mpr
    intro a ha b hbB
    change Equiv.Perm.sign (π ⁅a,b⁆) = 1
    rw [map_commutatorElement,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  intro x hx
  change π x = 1
  by_contra hn
  have hs := (critical_image_isSwap h e hz hk hb c hc
    (mem_map_of_mem π (hcomm hx)) hn).sign_eq
  have ht : Equiv.Perm.sign (π x) = 1 := heven hx
  rw [ht] at hs
  cases hs

/-- The source Z-layer has the same critical image as X. This is an image
identity only; the two source subgroups remain distinct. -/
theorem critical_Z_image_eq (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    graphImage h e hz hk (Z T c) = graphImage h e hz hk (X T c) := by
  have hcol := critical_endpoint_color T (alpha T) rfl _ hc
  have hp : 0 < criticalDistance T c ((sourceGeometry h).exists_critical c hcol) := by
    rw [(sourceGeometry h).distance_constant c hcol]
    exact sourceDistance_pos h
  have hZX := (sourceGeometry h).omega_bound c hcol hp
  have hrev := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcol hc
  let A := (Z T c).comap (embedM T)
  have hAm : A.map (embedM T) = Z T c :=
    map_comap_eq_self ((hZX.trans (critical_X_le_vertex h e c hcol _ hrev)).trans_eq
      (stabilizer_m_base T))
  have hne : A.map π ≠ ⊥ := by
    intro hzero
    have hAE : A ≤ extensionKernel h :=
      (projection_kernel h e hz hk) ▸ ((Subgroup.map_eq_bot_iff A).mp hzero)
    let : IsElementaryAbelian 2 (X T c) := omegaCenter_elementary _
    let : IsElementaryAbelian 2 (Z T c) := IsElementaryAbelian.of_le hZX
    let : IsElementaryAbelian 2 A :=
      IsElementaryAbelian.comap_of_injective _ (embedM_injective T) _
    have hAQ := two_subgroup_le_core_of_le_extensionKernel h hz A
      (IsElementaryAbelian.isPGroup 2 A) hAE
    apply hrev.2
    rw [←hAm,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono hAQ
  have hle : graphImage h e hz hk (Z T c) ≤ graphImage h e hz hk (X T c) :=
    map_mono (comap_mono hZX)
  apply eq_of_le_of_card_ge hle
  rw [critical_image_card_two h e hz hk hb c hc]
  exact (one_lt_card_iff_ne_bot _).mpr hne

include h e hz hk in
/-- Source (3.3)'s literal Z-image also has order two under the actual
central quotient marking, with no replacement of the original layer. -/
theorem critical_Z_core_index_two (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    (Q T (alpha T)).relIndex (Z T c) = 2 := by
  have hcol := critical_endpoint_color T (alpha T) rfl _ hc
  have hrev := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcol hc
  have hZX := (sourceGeometry h).omega_bound c hcol (by
    rw [(sourceGeometry h).distance_constant c hcol]
    exact sourceDistance_pos h)
  have hcent : Z T c ⊓ centralizer (X T (alpha T) : Set (FreeAmalgam T)) =
      Z T c ⊓ Q T (alpha T) := by
    ext x
    constructor
    · rintro ⟨hx,hxc⟩
      exact ⟨hx,((critical_X_centralizer_intersection h e (alpha T) rfl c hc) ▸
        (show x ∈ X T c ⊓ centralizer (X T (alpha T) : Set (FreeAmalgam T)) from
          ⟨hZX hx,hxc⟩)).2⟩
    · exact fun ⟨hx,hxQ⟩ => ⟨hx,Q_le_centralizer_X T (alpha T) hxQ⟩
  have hcard := graphImage_card h e hz hk (Z T c)
    (hZX.trans (critical_X_le_vertex h e c hcol _ hrev))
  rw [critical_Z_image_eq h e hz hk hb c hc,
    critical_image_card_two h e hz hk hb c hc] at hcard
  rw [Offenders.displacement,←inf_relIndex_left (Z T c),hcent,inf_relIndex_left] at hcard
  exact hcard.symm

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
