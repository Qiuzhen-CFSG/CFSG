module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

/-!
# Coordinated critical paths retaining the cubic kernel

Every noncentral vector in the natural or augmentation cover belongs to a
faithful duad orbit. Duad stabilizers are maximal and the component acts
transitively. An actor escaping E therefore moves a suitable component
conjugate vector, whose centralizer generates the whole local group with
that actor. For critical seeds the escape from E follows from their being
two-groups and E/Q having odd order.

The construction supplies a single conjugate critical path whose full kernel
normalizer generates with a prescribed opposite seed. Its commutator line
is noncentral at every vertex of the comparison path. An element of that
opposite seed fixes the entire comparison path pointwise while displacing
the chosen kernel; both path transports use the literal conjugators.

The final applications put this construction on the original small-radius
branch and feed whole-core and literal C.1.32 alternatives. They preserve the
entire intrinsic core, both cover orders and E/Q of order three. Source
(5.11)'s specific shifted endpoints and intermediate R4/R6 identifications,
(5.12)'s distance-four exclusion, and both final reconstruction outcomes
remain with qt-e-ms-small-a6-reconstruction. The independent natural exhaustion
input remains with qt-e-ms-small-a6-exhaustion-large-distance.

Source: MS93 (3.3)(ii), pp.866--867, and (5.9)--(5.11), pp.920--924.
Adapts Natural.Exhaustion.LargeDistance.SectionFive.CoordinatedLines to the
original cubic-kernel group and its unchanged action marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "T" => edge L R
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev coverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private theorem coverAction_conjugate (g : M) (v : Additive W) :
    ((coverAction h e hz hk (π g) v).toMul : M) = g * (v.toMul : M) * g⁻¹ := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation_apply W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) g v

private theorem cover_point_orbit (v : W)
    (hv : (v : M) ∉ center M) :
    ∃ f : Duad → Additive (W), Function.Injective f ∧
      (∀ g j, coverAction h e hz hk g (f j) = f (g • j)) ∧
      ∃ j, f j = Additive.ofMul v := by
  have hnotfixed : ¬ ∀ g, coverAction h e hz hk g (Additive.ofMul v) = Additive.ofMul v := by
    intro hh
    apply hv
    apply mem_center_iff.mpr
    intro m
    have he := congrArg (fun w : Additive (W) => (w.toMul : M))
      (hh (π m))
    rw [coverAction_conjugate] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  rcases moved_subgroup_cover_model h e hz hk with ⟨E,hE⟩ | ⟨E,hE⟩
  · have hzero : E (Additive.ofMul v) ≠ 0 := by
      intro he
      apply hnotfixed
      intro g
      apply E.injective
      simpa only [MonoidHom.id_apply,he,map_zero] using hE g (Additive.ofMul v)
    obtain ⟨j,hj⟩ := natural_cases _ hzero
    refine ⟨fun j => E.symm (naturalDuad j),E.symm.injective.comp naturalDuad_injective,?_,j,?_⟩
    · intro g j
      apply E.injective
      rw [hE]
      simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply,naturalDuad_map]
    · exact E.injective (by simpa only [LinearEquiv.apply_symm_apply] using hj)
  · rcases cover_cases (E (Additive.ofMul v)) with he | he | ⟨j,he | he⟩
    · exfalso
      apply hnotfixed
      intro g
      apply E.injective
      simpa only [MonoidHom.id_apply,he,map_zero] using hE g (Additive.ofMul v)
    · exfalso
      apply hnotfixed
      intro g
      apply E.injective
      simpa only [MonoidHom.id_apply,he,coverOne_map] using hE g (Additive.ofMul v)
    · refine ⟨fun j => E.symm (coverDuad j),E.symm.injective.comp coverDuad_injective,?_,j,?_⟩
      · intro g j
        apply E.injective
        rw [hE]
        simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply,coverDuad_map]
      · exact E.injective (by simpa only [LinearEquiv.apply_symm_apply] using he.symm)
    · refine ⟨fun j => E.symm (complementaryDuad j),
        E.symm.injective.comp complementaryDuad_injective,?_,j,?_⟩
      · intro g j
        apply E.injective
        rw [hE]
        simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply,complementaryDuad_map]
      · exact E.injective (by simpa only [LinearEquiv.apply_symm_apply,complementaryDuad] using he.symm)

include h e hz hk in
/-- A noncentral cover vector has a component conjugate whose centralizer,
together with any actor escaping E, generates the whole local group.
The same conjugate is moved by that actor, for either cover order. -/
theorem exists_cover_conjugate_generator (v : W)
    (hv : (v : M) ∉ center M)
    (A : Subgroup M) (hA : ¬ A ≤ extensionKernel h) :
    ∃ g ∈ L.subgroupOf (L ⊔ R),
      centralizer ({g * (v : M) * g⁻¹} : Set M) ⊔ A = ⊤ ∧
      g * (v : M) * g⁻¹ ∉ centralizer (A : Set M) := by
  obtain ⟨f,hf,heq,j,hj⟩ := cover_point_orbit h e hz hk v hv
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hA
  have hat : π a ≠ 1 := by
    intro he
    apply han
    rw [←(CubicAction.projection_kernel h e hz hk)]
    exact he
  have hm : ∃ k : Duad, π a • k ≠ k := by
    by_contra! hh
    apply hat
    exact eq_of_smul_eq_smul (α := Duad) (fun k => (hh k).trans (one_smul _ _).symm)
  obtain ⟨k,hkMove⟩ := hm
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) j k
  have htL : t.val ∈ (L.subgroupOf (L ⊔ R)).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact t.property
  obtain ⟨g,hg,hgt⟩ := htL
  let w : Additive (W) := coverAction h e hz hk (π g) (Additive.ofMul v)
  have hw : w = f k := by
    dsimp only [w]
    rw [←hj,hgt,heq]
    exact congrArg f ht
  have hwval : (w.toMul : M) = g * (v : M) * g⁻¹ :=
    coverAction_conjugate h e hz hk g (Additive.ofMul v)
  have hC : centralizer ({g * (v : M) * g⁻¹} : Set M) =
      (MulAction.stabilizer S6 k).comap π := by
    ext m
    rw [mem_centralizer_singleton_iff]
    change _ ↔ π m • k = k
    have hh := coverAction_conjugate h e hz hk m w
    rw [hw,heq] at hh
    constructor
    · intro hm
      apply hf
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [←hwval] at hm
      rw [←hw] at hh ⊢
      exact hh.trans (by rw [hm,mul_inv_cancel_right])
    · intro hm
      rw [hm] at hh
      rw [←hw,hwval] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hmax : IsCoatom (centralizer ({g * (v : M) * g⁻¹} : Set M)) := by
    rw [hC]
    exact isCoatom_comap_of_surjective (CubicEven.projection_surjective h e hz hk)
      (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive S6 k)
  have haC : a ∉ centralizer ({g * (v : M) * g⁻¹} : Set M) := by
    rw [hC]
    exact hkMove
  refine ⟨g,hg,?_,?_⟩
  · apply hmax.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    exact haC (he.symm ▸ (show a ∈ centralizer ({g * (v : M) * g⁻¹} : Set M) ⊔ A from mem_sup_right ha))
  · intro hc
    apply haC
    rw [mem_centralizer_singleton_iff]
    exact hc a ha


include h e hz hk in
/-- The simultaneous generating-centralizer and noncentral-line choice on
the actual graph, with the conjugator in the original local two-residual. -/
theorem exists_cover_line_generator
    {a b : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a b)
    (H : Subgroup (FreeAmalgam T)) (hHU : H ≤ U T a)
    (hcard : Nat.card H = 2)
    (hcentral : ¬ H ≤ centralizer (stabilizer T a : Set (FreeAmalgam T))) :
    ∃ g ∈ Ltilde T a,
      (stabilizer T a ⊓ centralizer
        (H.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam T))) ⊔
          Z T b = stabilizer T a ∧
      ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer
        (Z T b : Set (FreeAmalgam T)) := by
  classical
  obtain ⟨z,hzn,hunique⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  have hznot : (z : FreeAmalgam T) ∉ centralizer
      (stabilizer T a : Set (FreeAmalgam T)) := by
    intro hz
    apply hcentral
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ one_mem _
    · have he : (⟨x,hx⟩ : H) = z := hunique _ (fun he => hx1 (congrArg Subtype.val he))
      have hxz : x = (z : FreeAmalgam T) := congrArg Subtype.val he
      rw [hxz]
      exact hz
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk a p.start_color
  obtain ⟨v,hv,hvz⟩ := (show (z : FreeAmalgam T) ∈ (W).map i from
    hiU.symm ▸ hHU z.property)
  have hvnot : v ∉ center M := by
    intro hv
    apply hznot
    intro m hm
    obtain ⟨m,rfl⟩ := hir.symm ▸ hm
    rw [←hvz,←map_mul,←map_mul]
    exact congrArg i (mem_center_iff.mp hv m)
  have hA : Z T b ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) p.critical
  let A := (Z T b).comap i
  have hmA : A.map i = Z T b := map_comap_eq_self hA
  have hnA : ¬ A ≤ extensionKernel h := by
    intro he
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) b p.end_color
    have ht : IsPGroup 2 A :=
      (IsElementaryAbelian.isPGroup 2 (Z T b)).comap_of_injective i hi
    have hh := map_mono (f := i)
      (two_subgroup_le_core_of_le_extensionKernel h hz A ht he)
    rw [hmA,hiQ] at hh
    have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
      b p.end_color p.critical
    exact hr.2 hh
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_conjugate_generator h e hz hk ⟨v,hv⟩ hvnot A hnA
  let j : M →* stabilizer T a :=
    i.codRestrict _ (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hgL : i g ∈ Ltilde T a := by
    have hg' : g ∈ pResidual 2 M := (h.relative_residual).symm ▸ hg
    exact mem_map_of_mem (stabilizer T a).subtype
      ((map_pResidual_le 2 j) (mem_map_of_mem j hg'))
  let C := centralizer ({g * v * g⁻¹} : Set M)
  let HC := H.map (MulAut.conj (i g)).toMonoidHom
  have hC : C.map i ≤ stabilizer T a ⊓
      centralizer (HC : Set (FreeAmalgam T)) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩),?_⟩
    rintro y ⟨w,hw,rfl⟩
    by_cases hw1 : w = 1
    · simp only [hw1,map_one,one_mul,mul_one]
    · have he : (⟨w,hw⟩ : H) = z := hunique _ (fun he => hw1 (congrArg Subtype.val he))
      have hwz : w = (z : FreeAmalgam T) := congrArg Subtype.val he
      rw [hwz,←hvz]
      change (i g * i v * (i g)⁻¹) * i x = i x * (i g * i v * (i g)⁻¹)
      simpa only [map_mul,map_inv] using congrArg i
        (mem_centralizer_singleton_iff.mp hx).symm
  refine ⟨i g,hgL,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left (hA.trans_eq hir))
    have hm := congrArg (Subgroup.map i) hgen
    rw [Subgroup.map_sup,hmA,←MonoidHom.range_eq_map,hir] at hm
    calc
      stabilizer T a = C.map i ⊔ Z T b := hm.symm
      _ ≤ _ := sup_le_sup_right hC _
  · intro hfix
    apply hmove
    intro x hx
    have hzH : i (g * v * g⁻¹) ∈ HC := by
      have hh := mem_map_of_mem (MulAut.conj (i g)).toMonoidHom z.property
      change (i g * (z : FreeAmalgam T) * (i g)⁻¹) ∈ HC at hh
      simpa only [←hvz,map_mul,map_inv] using hh
    apply hi
    simpa only [map_mul] using hfix hzH (i x) hx

include h e hz hk in
/-- Choose a critical-path conjugate whose full kernel normalizer generates
the starting stabilizer with the prescribed opposite seed. Every vertex of
the chosen path and its noncentral commutator use this one conjugator. -/
theorem exists_small_critical_path_generator
    {a a' b' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (q : CriticalPath T (sourceGeometry h) a b')
    (hsmall : (Q T a').relIndex (Z T a) < 4) :
    ∃ g ∈ Ltilde T a,
      ∃ r : CriticalPath T (sourceGeometry h) a (act T g a'),
        (∀ n, r.walk.getVert n = act T g (p.walk.getVert n)) ∧
        (Q T (act T g a')).relIndex (Z T a) = 2 ∧
        (stabilizer T a ⊓ normalizer
          (Z T a ⊓ Q T (act T g a') : Set (FreeAmalgam T))) ⊔
            Z T b' = stabilizer T a ∧
        ¬ ⁅Z T a,Z T (act T g a')⁆ ≤
          centralizer (Z T b' : Set (FreeAmalgam T)) := by
  obtain ⟨x,hx,hgen,hmove⟩ := exists_cover_line_generator h e hz hk q
    ⁅Z T a,Z T a'⁆
    (by
      rw [←small_critical_moving_commutator_eq h e hz hk p hsmall]
      apply le_normalizer_iff_commutator_le_left.mp
      exact (critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
        p.critical).trans (U_normalized (R := T) a))
    (small_critical_commutator_card h e hz hk p hsmall)
    (critical_commutator_not_central h e hz hk p)
  let g := x⁻¹
  have hg : g ∈ Ltilde T a := (Ltilde T a).inv_mem hx
  have hga : act T g a = a := Ltilde_le_stabilizer a hg
  have hpact : ∃ r : CriticalPath T (sourceGeometry h)
      (act T g a) (act T g a'),
      ∀ n, r.walk.getVert n = act T g (p.walk.getVert n) :=
    ⟨p.act g,fun n => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hga] at hpact
  obtain ⟨r,hr⟩ := hpact
  have hrsmall : (Q T (act T g a')).relIndex (Z T a) < 4 := by
    rw [←hga,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hsmall
  have hline : (⁅Z T a,Z T a'⁆ : Subgroup (FreeAmalgam T)).map
      (MulAut.conj x).toMonoidHom = ⁅Z T a,Z T (act T g a')⁆ := by
    have hgx : g⁻¹ = x := inv_inv x
    rw [←hgx,map_commutator,←Z_act,←Z_act,hga]
  rw [hline] at hgen hmove
  refine ⟨g,hg,r,hr,(small_critical_indices h e hz hk r hrsmall).1,?_,hmove⟩
  have he := small_critical_kernel_normalizer_eq_line_centralizer h e hz hk r hrsmall
  simp only [Subgroup.coe_inf] at he
  simp only [Set.inf_eq_inter]
  rw [he]
  exact hgen


include h in
private theorem endpoint_seed_le_path_stabilizer {a b : Vertex T}
    (q : CriticalPath T (sourceGeometry h) a b) (n : ℕ) :
    Z T b ≤ stabilizer T (q.walk.getVert n) := by
  apply Z_le_stabilizer_of_dist_le b ((sourceGeometry h).exists_critical b q.end_color)
  rw [(sourceGeometry h).distance_constant b q.end_color,
    SimpleGraph.dist_comm,q.dist_end]
  change q.walk.length - n ≤ sourceDistance h
  exact (Nat.sub_le _ _).trans_eq (show q.walk.length = sourceDistance h from q.length_eq_b)

include h e hz hk in
/-- Movement of the chosen line supplies an element of the opposite seed
which fixes its whole critical path pointwise and displaces the chosen full
kernel. The second path is transported by this exact element. -/
theorem exists_critical_kernel_displacement_fixing_path
    {a a' b' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (q : CriticalPath T (sourceGeometry h) a b')
    (hsmall : (Q T a').relIndex (Z T a) < 4)
    (hmove : ¬ ⁅Z T a,Z T a'⁆ ≤
      centralizer (Z T b' : Set (FreeAmalgam T))) :
    ∃ z ∈ Z T b',
      (∀ n, act T z (q.walk.getVert n) = q.walk.getVert n) ∧
      ∃ r : CriticalPath T (sourceGeometry h) a (act T z a'),
        (∀ n, r.walk.getVert n = act T z (p.walk.getVert n)) ∧
        Z T a ⊓ Q T (act T z a') ≠ Z T a ⊓ Q T a' := by
  let K := Z T a ⊓ Q T a'
  have hAG : Z T b' ≤ stabilizer T a :=
    critical_Z_le_stabilizer T (sourceGeometry h) a q.start_color
      (by rw [(sourceGeometry h).distance_constant a q.start_color]
          exact sourceDistance_pos h) q.critical
  have hn : ¬ Z T b' ≤ normalizer (K : Set (FreeAmalgam T)) := by
    intro hn
    apply hmove
    apply le_centralizer_iff.mp
    have hh := le_inf hAG hn
    rw [show K = Z T a ⊓ Q T a' from rfl,
      small_critical_kernel_normalizer_eq_line_centralizer h e hz hk p hsmall] at hh
    exact hh.trans inf_le_right
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hn
  let z := x⁻¹
  have hz : z ∈ Z T b' := (Z T b').inv_mem hx
  have hza : act T z a = a := hAG hz
  have hpact : ∃ r : CriticalPath T (sourceGeometry h)
      (act T z a) (act T z a'),
      ∀ n, r.walk.getVert n = act T z (p.walk.getVert n) :=
    ⟨p.act z,fun n => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hza] at hpact
  obtain ⟨r,hr⟩ := hpact
  refine ⟨z,hz,?_,r,hr,?_⟩
  · intro n
    exact endpoint_seed_le_path_stabilizer (h := h) q n hz
  · intro he
    apply hxn
    apply mem_normalizer_iff_map_conj_eq.mpr
    change K.map (MulAut.conj x).toMonoidHom = K
    dsimp only [K]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective]
    have hZ := Z_act T z a
    have hQ := Q_act T z a'
    simp only [z,inv_inv,hza] at hZ hQ
    rwa [←hZ,←hQ]



include h e hz hk in
/-- One component conjugate has the generating kernel normalizer. A second
conjugator from the opposite seed fixes the entire comparison path and
moves the same full kernel, retaining the original cubic action. -/
theorem small_opposite_radius_coordinated_paths
    {a a' b' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (q : CriticalPath T (sourceGeometry h) a b')
    (hsmall : (Q T a).relIndex (V T a') ≤ 8) :
    ∃ g ∈ Ltilde T a,
      ∃ r : CriticalPath T (sourceGeometry h) a (act T g a'),
        (∀ n, r.walk.getVert n = act T g (p.walk.getVert n)) ∧
        (Q T (act T g a')).relIndex (Z T a) = 2 ∧
        (stabilizer T a ⊓ normalizer
          (Z T a ⊓ Q T (act T g a') : Set (FreeAmalgam T))) ⊔
            Z T b' = stabilizer T a ∧
        (∀ n, ¬ ⁅Z T a,Z T (act T g a')⁆ ≤
          centralizer (stabilizer T (q.walk.getVert n) : Set (FreeAmalgam T))) ∧
        ∃ z ∈ Z T b',
          (∀ n, act T z (q.walk.getVert n) = q.walk.getVert n) ∧
          ∃ t : CriticalPath T (sourceGeometry h)
            a (act T z (act T g a')),
            (∀ n, t.walk.getVert n = act T z (r.walk.getVert n)) ∧
            Z T a ⊓ Q T (act T z (act T g a')) ≠
              Z T a ⊓ Q T (act T g a') := by
  have hb := distance_gt_two h e hz hk
  have hi := critical_index_two_of_small_opposite_radius h e hz hk hb p hsmall
  obtain ⟨g,hg,r,hr,hri,hgen,hmove⟩ := exists_small_critical_path_generator h e hz hk p q (by omega)
  refine ⟨g,hg,r,hr,hri,hgen,?_,?_⟩
  · intro n hn
    exact hmove (hn.trans (centralizer_le (endpoint_seed_le_path_stabilizer (h := h) q n)))
  · exact exists_critical_kernel_displacement_fixing_path h e hz hk r q (by omega) hmove


include h e hz hk in
/-- In the exact small-radius-four branch, the source yields a component
conjugate kernel displaced by a seed element fixing the original path. -/
theorem small_opposite_radius_path_fixed_displacement
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hsmall : (Q T a).relIndex (V T c) ≤ 4) :
    ∃ g ∈ Ltilde T a, ∃ z ∈ Z T c,
      (∀ n, act T z (p.walk.getVert n) = p.walk.getVert n) ∧
      (stabilizer T a ⊓ normalizer
        (Z T a ⊓ Q T (act T g c) : Set (FreeAmalgam T))) ⊔ Z T c = stabilizer T a ∧
      (∀ n, ¬ ⁅Z T a,Z T (act T g c)⁆ ≤
        centralizer (stabilizer T (p.walk.getVert n) : Set (FreeAmalgam T))) ∧
      Z T a ⊓ Q T (act T z (act T g c)) ≠ Z T a ⊓ Q T (act T g c) := by
  obtain ⟨g,hg,r,hr,hri,hgen,hmove,z,hz,hfix,t,ht,hdis⟩ :=
    small_opposite_radius_coordinated_paths h e hz hk p p (by omega)
  exact ⟨g,hg,z,hz,hfix,hgen,hmove,hdis⟩

omit hk in
include h e hz in
/-- Whole-core assembly now carries coordinated displacement on the original
small-radius critical path, retaining E/Q and the entire intrinsic core. -/
theorem coreExhaustion_or_cubic_coordinated_paths :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a c : Vertex T, ∀ p : CriticalPath T (sourceGeometry h) a c,
        (Q T a).relIndex (V T c) ≤ 4 →
        ∃ g ∈ Ltilde T a, ∃ z ∈ Z T c,
          (∀ n, act T z (p.walk.getVert n) = p.walk.getVert n) ∧
          (stabilizer T a ⊓ normalizer
            (Z T a ⊓ Q T (act T g c) : Set (FreeAmalgam T))) ⊔ Z T c = stabilizer T a ∧
          (∀ n, ¬ ⁅Z T a,Z T (act T g c)⁆ ≤
            centralizer (stabilizer T (p.walk.getVert n) : Set (FreeAmalgam T))) ∧
          Z T a ⊓ Q T (act T z (act T g c)) ≠ Z T a ⊓ Q T (act T g c) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,fun _ _ p hp =>
      small_opposite_radius_path_fixed_displacement h e hz hk p hp⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the coordinated critical-path family. The
source shifted-endpoint exclusion and distance-four contradiction remain
with this reconstruction owner. -/
theorem rankTwo_or_cubic_coordinated_paths :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a c : Vertex T, ∀ p : CriticalPath T (sourceGeometry h) a c,
        (Q T a).relIndex (V T c) ≤ 4 →
        ∃ g ∈ Ltilde T a, ∃ z ∈ Z T c,
          (∀ n, act T z (p.walk.getVert n) = p.walk.getVert n) ∧
          (stabilizer T a ⊓ normalizer
            (Z T a ⊓ Q T (act T g c) : Set (FreeAmalgam T))) ⊔ Z T c = stabilizer T a ∧
          (∀ n, ¬ ⁅Z T a,Z T (act T g c)⁆ ≤
            centralizer (stabilizer T (p.walk.getVert n) : Set (FreeAmalgam T))) ∧
          Z T a ⊓ Q T (act T z (act T g c)) ≠ Z T a ⊓ Q T (act T g c) :=
  (coreExhaustion_or_cubic_coordinated_paths h e hz).imp (rankTwo_of_exhaustion h e hz) id
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
