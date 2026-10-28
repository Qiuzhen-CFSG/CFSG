module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Residual
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.CubicSupplement

/-!
# The original plane centralizer and its exchange symmetry

The action kernel on I C_T(v) is a two-group: its intersection with I is
O₂(I), and its image in I C_T(v)/I is a two-group. The literal action
quotient is SL₅(2), so the cubic-residual supplement theorem for Sylow
overgroups applies to the centralizer of the original plane E. Embedding
its residual in O^{3′}(C_G(E)) and using the opposite point residual gives

  C_{I C_T(v)}(E) = O^{3′}(C_G(E)) C_T(v).

The original t normalizes both factors on the right, hence this entire
centralizer, and conjugation identifies it with the centralizer in I^t C_T(v).
Its actual action image is a proper flag parabolic. Properness follows
because u generates VI under I, so centralizing u would force I into M.
No natural or exterior module marking is assumed for VI in this argument.

These are the initial parabolic assertions of Aschbacher--Smith 10.2.9,
printed pp.752--753. The rank-five and rank-ten terminal contradictions
remain with qt-d-10-nona5-point-constrained, as does construction of the
supplied LinearFiveData from the original Context.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The kernel on the whole point join is an extension of two-groups. -/
theorem LinearFiveData.action_kernel_two {c : Context D t v I} (m : LinearFiveData c) :
    letI := c.reduced.normal
    IsPGroup 2 (actionMk (internalModule D v I)).ker := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let S := (pointSylow T v).subgroupOf H
  let := c.reduced.normal
  let q := actionMk (internalModule D v I)
  let f := q.subgroupMap K
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  have hKS : K ⊔ S = ⊤ := by
    rw [← subgroupOf_sup (show I ≤ H from le_sup_left)
      (show pointSylow T v ≤ H from le_sup_right), subgroupOf_self]
  have hquot : IsPGroup 2 (H ⧸ K) := isPGroup_quotient_of_sup_eq_top K S
    ((T.isPGroup'.to_le inf_le_left).comap_subtype) hKS
  intro x
  obtain ⟨n,hn⟩ := hquot (QuotientGroup.mk' K (x : H))
  have hxK : (x : H) ^ (2 ^ n) ∈ K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' K) ((x : H) ^ (2 ^ n)) = 1
    simpa only [map_pow] using hn
  let y : K := ⟨(x : H) ^ (2 ^ n), hxK⟩
  have hy : y ∈ f.ker := by
    apply Subtype.ext
    change q ((x : H) ^ (2 ^ n)) = 1
    rw [map_pow, show q (x : H) = 1 from x.property, one_pow]
  rw [show f.ker = pCore 2 K from m.kernel_eq] at hy
  obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := K)) ⟨y,hy⟩
  refine ⟨n+r, Subtype.ext ?_⟩
  have he := congrArg (fun a : pCore 2 K => ((a : K) : H)) hr
  change ((x : H) ^ (2 ^ n)) ^ (2 ^ r) = 1 at he
  change (x : H) ^ (2 ^ (n+r)) = 1
  simpa only [←pow_mul,←pow_add] using he

/-- The original quotient map followed by its actual binary-five marking. -/
noncomputable def LinearFiveData.joinAction {c : Context D t v I} (m : LinearFiveData c) :
    pointJoin T v I →* BinaryLinear.OuterCyclic.LinearGroup 5 := by
  let := c.reduced.normal
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let e : ActionQuotient (internalModule D v I) ≃* A :=
    (Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr m.actor_eq_top.symm)
  exact ((m.actor.trans (BinaryLinear.OuterCyclic.slEquivLinear 5)).toMonoidHom.comp
    e.toMonoidHom).comp (actionMk (internalModule D v I))

theorem LinearFiveData.joinAction_surjective {c : Context D t v I} (m : LinearFiveData c) :
    Function.Surjective m.joinAction := by
  let := c.reduced.normal
  exact ((BinaryLinear.OuterCyclic.slEquivLinear 5).surjective.comp m.actor.surjective).comp
    (((Subgroup.topEquiv).symm.trans
      (MulEquiv.subgroupCongr m.actor_eq_top.symm)).surjective.comp
        (QuotientGroup.mk'_surjective _))

theorem LinearFiveData.joinAction_ker {c : Context D t v I} (m : LinearFiveData c) :
    letI := c.reduced.normal
    m.joinAction.ker = (actionMk (internalModule D v I)).ker := by
  let := c.reduced.normal
  ext x
  simp [LinearFiveData.joinAction, MonoidHom.mem_ker]

theorem LinearFiveData.joinAction_kernel_two {c : Context D t v I} (m : LinearFiveData c) :
    IsPGroup 2 m.joinAction.ker := by
  let := c.reduced.normal
  rw [m.joinAction_ker]
  exact m.action_kernel_two

/-- Centralizing the original generator would centralize its entire I-orbit,
forcing I into M. Thus the actual plane centralizer is proper. -/
theorem LinearFiveData.plane_centralizer_ne_join {c : Context D t v I}
    (m : LinearFiveData c) :
    pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) ≠ pointJoin T v I := by
  intro he
  have hIu : I ≤ centralizer ({oppositePoint t v} : Set G) := by
    intro i hi
    have hh : i ∈ pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) :=
      he.symm ▸ (show i ∈ pointJoin T v I from (le_sup_left : I ≤ pointJoin T v I) hi)
    rw [c.join_plane_centralizer] at hh
    exact hh.2
  have hIz : I ≤ centralizer (zpowers (oppositePoint t v) : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro i hi
    exact mem_centralizer_singleton_iff.mp (hIu hi)
  have hI := le_centralizer_conjugateSpanBy_of_normalizes I
    (zpowers (oppositePoint t v)) I I.le_normalizer hIz
  rw [←m.orbit_eq_opposite_span] at hI
  exact c.escaping.escapes
    (hI.trans (c.actionFacts_of_linearFiveData m).prepared.centralizer_le)

/-- The model is attached to the literal point-join centralizer through its
actual action quotient, with a Sylow subgroup supplied by point saturation. -/
theorem LinearFiveData.plane_centralizer_isFlagParabolic {c : Context D t v I}
    (m : LinearFiveData c) : BinaryLinear.FiveFlagGeometry.IsFlagParabolic
      (((pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)).subgroupOf
        (pointJoin T v I)).map m.joinAction) := by
  obtain ⟨S,hS⟩ := c.join_sylow
  apply BinaryLinear.FiveFlagGeometry.isFlagParabolic_of_sylow_le
    (S.mapSurjective m.joinAction_surjective)
  apply map_mono
  intro s hs
  have hp : (s : G) ∈ pointSylow T v := hS ▸ mem_map_of_mem (pointJoin T v I).subtype hs
  exact ⟨s.property,m.pointSylow_centralizes_plane hp⟩

/-- The centralizer of the original involution plane is exactly the join
of the ambient plane residual with the prescribed point Sylow. -/
theorem LinearFiveData.plane_centralizer_eq {c : Context D t v I} (m : LinearFiveData c) :
    pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) =
      (primeToResidual 3 (centralizer (pointPlane t v : Set G))).map
        (centralizer (pointPlane t v : Set G)).subtype ⊔ pointSylow T v := by
  let H := pointJoin T v I
  let C := H ⊓ centralizer (pointPlane t v : Set G)
  let K := C.subgroupOf H
  obtain ⟨S,hS⟩ := c.join_sylow
  have hSK : (S : Subgroup H) ≤ K := by
    intro s hs
    have hp : (s : G) ∈ pointSylow T v := hS ▸ mem_map_of_mem H.subtype hs
    exact ⟨s.property,m.pointSylow_centralizes_plane hp⟩
  have hgen := BinaryLinear.FiveFlagGeometry.embedded_primeToResidual_sup_sylow_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S K hSK
  have hC : (primeToResidual 3 C).map C.subtype ⊔ pointSylow T v = C := by
    have hh := congrArg (Subgroup.map H.subtype) hgen
    rw [Subgroup.map_sup, map_embedded_primeToResidual_of_hom, hS,
      map_subgroupOf_eq_of_le (show C ≤ H from inf_le_left)] at hh
    exact hh
  apply le_antisymm
  · change C ≤ _
    rw [←hC]
    exact sup_le_sup (embedded_primeToResidual_mono 3 inf_le_right) le_rfl
  · exact m.plane_residual_supplement.2.trans inf_le_left

/-- The literal exchange normalizes the entire point-join plane centralizer. -/
theorem LinearFiveData.exchange_normalizes_plane_centralizer {c : Context D t v I}
    (m : LinearFiveData c) : t ∈ normalizer
      ((pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) : Subgroup G) : Set G) := by
  rw [m.plane_centralizer_eq]
  exact m.plane_residual_supplement.1

/-- The same centralizer is obtained in the conjugate point join. -/
theorem LinearFiveData.plane_centralizer_eq_conjugate {c : Context D t v I}
    (m : LinearFiveData c) :
    pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) =
      pointJoin T (oppositePoint t v) (I.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer (pointPlane t v : Set G) := by
  have he := mem_normalizer_iff_map_conj_eq.mp m.exchange_normalizes_plane_centralizer
  have hT := mem_normalizer_iff_map_conj_eq.mp (m.pointSylow_normalized c.escaping.t_mem)
  have hC := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_centralizer (pointPlane t v) m.exchange_normalizes_plane)
  change ((pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)).map
    (MulAut.conj t).toMonoidHom) = _ at he
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, pointJoin, Subgroup.map_sup] at he
  change (pointSylow T v).map (MulAut.conj t).toMonoidHom = _ at hT
  change (centralizer (pointPlane t v : Set G)).map (MulAut.conj t).toMonoidHom = _ at hC
  rw [hT,hC] at he
  change (I ⊔ pointSylow T v) ⊓ centralizer (pointPlane t v : Set G) =
    (I.map (MulAut.conj t).toMonoidHom ⊔ pointSylow T (oppositePoint t v)) ⊓
      centralizer (pointPlane t v : Set G)
  rw [m.opposite_pointSylow]
  exact he.symm

/-- The action kernel centralizes the literal plane: it fixes its orbit
coordinate u, while the whole point join fixes v. -/
theorem LinearFiveData.joinAction_kernel_le_plane_centralizer {c : Context D t v I}
    (m : LinearFiveData c) : m.joinAction.ker ≤
      (pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)).subgroupOf (pointJoin T v I) := by
  let H := pointJoin T v I
  let := c.reduced.normal
  rw [m.joinAction_ker]
  intro x hx
  rw [c.join_plane_centralizer]
  refine ⟨x.property,mem_centralizer_singleton_iff.mpr ?_⟩
  have hc : x ∈ centralizer (internalModule D v I : Set H) := by
    simpa only [actionMk,QuotientGroup.ker_mk'] using hx
  have he := hc ⟨oppositePoint t v,c.orbit_le_join m.opposite_mem_orbit⟩ m.opposite_mem_orbit
  exact (congrArg H.subtype he).symm

/-- The actual centralizer image is a proper flag parabolic of SL₅(2). -/
theorem LinearFiveData.plane_centralizer_image_ne_top {c : Context D t v I}
    (m : LinearFiveData c) :
    ((pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)).subgroupOf
      (pointJoin T v I)).map m.joinAction ≠ ⊤ := by
  intro htop
  have hK : (pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)).subgroupOf
      (pointJoin T v I) = ⊤ := by
    apply map_injective_of_ker_le m.joinAction m.joinAction_kernel_le_plane_centralizer le_top
    rw [htop,map_top_of_surjective _ m.joinAction_surjective]
  apply m.plane_centralizer_ne_join
  have he := congrArg (Subgroup.map (pointJoin T v I).subtype) hK
  rw [map_subgroupOf_eq_of_le inf_le_left, ←MonoidHom.range_eq_map, range_subtype] at he
  exact he

end CFSG.Quasithin.Chapter10.PointControl.Constrained
