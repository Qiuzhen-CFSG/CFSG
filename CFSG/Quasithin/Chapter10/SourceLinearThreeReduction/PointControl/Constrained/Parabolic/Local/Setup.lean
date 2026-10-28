module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalSelection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Plane

/-!
# The local plane and its binary-five orbit

At a point in the opposite local natural copy, the index-two point Sylow
and the original exchanger produce an elementary involution plane. The
other coordinate generates a reduced smaller orbit with full SL₅(2)
action, irreducible of dimension five or ten. Its action kernel equals
that of the original VI; the local three-space is not identified with the
full four-copy moved subgroup.

Every property is derived from the original four-natural marking and
local-point selection. This is the local version of the source's plane
construction, needed because source 10.2.7's removal of the four-copy row
is unavailable here. Source: Aschbacher--Smith, 10.2.9, pp.752--753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
open BinaryLinear.FiveFlagGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The retained original marking at a point in the opposite local copy.
All orbit, kernel and representation properties below are derived from these
three source conditions, not assumed as additional endgame inputs. -/
structure LocalFiveData (c : Context D t v I) where
  cover : FourNaturalCover D
  sylow_eq : pointSylow T v = (T : Subgroup G) ⊓ normalizer (L : Set G)
  local_point : v ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom

abbrev localFiveOrbit (t v : G) (I : Subgroup G) : Subgroup G :=
  conjugateSpanBy (zpowers (oppositePoint t v)) I
abbrev localFiveModule (T : Sylow 2 G) (t v : G) (I : Subgroup G) :=
  (localFiveOrbit t v I).subgroupOf (pointJoin T v I)

def LocalFiveData.quotient {c : Context D t v I} (m : LocalFiveData c) :
    (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2) := m.cover.choose

def LocalFiveData.natural {c : Context D t v I} (m : LocalFiveData c) :
    BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :=
  (c.local_natural_of_four_natural_cover m.quotient m.cover.choose_spec.some).some

/-- The local natural three-space has no component-fixed vector. -/
theorem LocalFiveData.moved_fixed_eq_bot {c : Context D t v I} (m : LocalFiveData c) :
    ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  rintro w ⟨hw,hc⟩
  let a : (⁅D.moduleSubgroup,L⁆ : Subgroup G) := ⟨w,hw⟩
  have hf : (m.natural.coordinates a).toAdd ∈
      Representation.OneCohomology.fixed (specialLinearNatural (k := ZMod 2) 3) := by
    intro g
    obtain ⟨l,hl⟩ := (m.quotient.surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 L))) g
    have hh := m.natural.equivariant l a
    have he : (⟨(l : G)*w*(l : G)⁻¹,
        (mem_normalizer_iff.mp (m.natural.normalized l.property) w).mp hw⟩ :
        (⁅D.moduleSubgroup,L⁆ : Subgroup G)) = a := by
      apply Subtype.ext
      change (l : G)*w*(l : G)⁻¹ = w
      rw [hc l l.property, mul_inv_cancel_right]
    rw [he] at hh
    change (m.natural.coordinates a).toAdd =
      specialLinearNatural 3 (m.quotient (QuotientGroup.mk' (pCore 2 L) l))
        (m.natural.coordinates a).toAdd at hh
    change m.quotient (QuotientGroup.mk' (pCore 2 L) l) = g at hl
    exact (hl ▸ hh).symm
  rw [Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hf
  exact (m.natural.coordinates_eq_one_iff a).mp (show m.natural.coordinates a = 1 from hf)

/-- The literal point Sylow has index two inside T. -/
theorem LocalFiveData.pointSylow_index {c : Context D t v I} (m : LocalFiveData c) :
    ((pointSylow T v).subgroupOf (T : Subgroup G)).index = 2 := by
  rw [m.sylow_eq]
  have h := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
    (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem))
  convert h using 1
  congr 1
  ext x
  exact and_iff_right x.property

/-- The exchange normalizes the full point Sylow. -/
theorem LocalFiveData.pointSylow_normalized {c : Context D t v I} (m : LocalFiveData c) :
    (T : Subgroup G) ≤ normalizer (pointSylow T v : Set G) := by
  have hn := normal_of_index_eq_two m.pointSylow_index
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

/-- The square of the original exchange already centralizes the original point. -/
theorem LocalFiveData.exchange_square_mem {c : Context D t v I} (m : LocalFiveData c) :
    t ^ 2 ∈ pointSylow T v :=
  ((pointSylow T v).subgroupOf (T : Subgroup G)).sq_mem_of_index_two
    m.pointSylow_index ⟨t,c.escaping.t_mem⟩

/-- Conjugation by the original t interchanges the two original points. -/
theorem LocalFiveData.exchange_opposite {c : Context D t v I} (m : LocalFiveData c) :
    oppositePoint t (oppositePoint t v) = v := by
  have hcomm := mem_centralizer_singleton_iff.mp m.exchange_square_mem.2
  change t*(t*v*t⁻¹)*t⁻¹ = v
  calc
    _ = t^2*v*(t^2)⁻¹ := by simp only [pow_two]; group
    _ = v := by rw [hcomm,mul_inv_cancel_right]

/-- The exchanged point belongs to the original local moved subgroup. -/
theorem LocalFiveData.opposite_mem_moved {c : Context D t v I} (m : LocalFiveData c) :
    oppositePoint t v ∈ ⁅D.moduleSubgroup,L⁆ := by
  obtain ⟨w,hw,hwt⟩ := m.local_point
  have htn : t^2 ∈ normalizer (L : Set G) := by
    have hh := m.exchange_square_mem
    rw [m.sylow_eq] at hh
    exact hh.2
  have hWn : t^2 ∈ normalizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G) :=
    c.halfJoin_normalizes_local_moved
      ((show (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ halfJoin T L from le_sup_right)
        ⟨(T : Subgroup G).pow_mem c.escaping.t_mem 2,htn⟩)
  have he : oppositePoint t v = (MulAut.conj (t^2)) w := by
    rw [←hwt]
    change t*(t*w*t⁻¹)*t⁻¹ = t^2*w*(t^2)⁻¹
    simp only [pow_two]
    group
  rw [he]
  exact (mem_normalizer_iff.mp hWn w).mp hw

/-- The local natural three-space is disjoint from its crossed partner. -/
theorem LocalFiveData.moved_disjoint_partner {c : Context D t v I} (m : LocalFiveData c) :
    Disjoint (⁅D.moduleSubgroup,L⁆ : Subgroup G)
      ((⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom) :=
  disjoint_iff.mpr (bot_unique ((inf_le_inf_left _ ((map_mono
    (commutator_mono (le_componentOrbit _ _) le_rfl)).trans c.escaping.crossed)).trans_eq
    m.moved_fixed_eq_bot))

/-- The two nonidentity original points are distinct. -/
theorem LocalFiveData.opposite_ne {c : Context D t v I} (m : LocalFiveData c) :
    oppositePoint t v ≠ v := by
  intro he
  have hvW := he ▸ m.opposite_mem_moved
  exact c.escaping.v_ne (mem_bot.mp (m.moved_disjoint_partner.eq_bot ▸
    (show v ∈ (⁅D.moduleSubgroup,L⁆ : Subgroup G) ⊓
      ((⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom) from ⟨hvW,m.local_point⟩)))

/-- Both points and their plane lie in the original elementary full module. -/
theorem LocalFiveData.plane_le_fullModule {c : Context D t v I} (m : LocalFiveData c) :
    pointPlane t v ≤ D.fullModule := by
  have hW : ⁅D.moduleSubgroup,L⁆ ≤ D.fullModule :=
    (le_normalizer_iff_commutator_le_left.mp
      ((le_componentOrbit L T).trans D.orbit_normalizes_module)).trans
        (le_componentOrbit _ _)
  exact sup_le (zpowers_le.mpr (hW m.opposite_mem_moved))
    (zpowers_le.mpr (partner_le_fullModule D c.escaping.t_mem c.escaping.v_mem))

/-- The original half-Sylow centralizes both coordinates of the plane. -/
theorem LocalFiveData.pointSylow_centralizes_plane {c : Context D t v I}
    (m : LocalFiveData c) : pointSylow T v ≤ centralizer (pointPlane t v : Set G) := by
  apply le_centralizer_iff.mpr
  apply sup_le
  · apply zpowers_le.mpr
    intro s hs
    have ht := m.pointSylow_normalized ((T : Subgroup G).inv_mem c.escaping.t_mem)
    have hsc : (MulAut.conj t⁻¹) s ∈ pointSylow T v := (mem_normalizer_iff.mp ht s).mp hs
    have hh := congrArg (MulAut.conj t) (mem_centralizer_singleton_iff.mp hsc.2)
    have he : (MulAut.conj t) ((MulAut.conj t⁻¹) s) = s := by
      change t*(t⁻¹*s*(t⁻¹)⁻¹)*t⁻¹ = s
      group
    simpa only [map_mul,he] using hh
  · exact zpowers_le.mpr (fun s hs => mem_centralizer_singleton_iff.mp hs.2)

/-- The original exchange normalizes the original plane. -/
theorem LocalFiveData.exchange_normalizes_plane {c : Context D t v I}
    (m : LocalFiveData c) : t ∈ normalizer (pointPlane t v : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [pointPlane, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change zpowers (oppositePoint t (oppositePoint t v)) ⊔ zpowers (oppositePoint t v) = _
  rw [m.exchange_opposite, sup_comm]

/-- The original plane is elementary abelian of order four. -/
theorem LocalFiveData.plane_elementary_card {c : Context D t v I} (m : LocalFiveData c) :
    IsElementaryAbelian 2 (pointPlane t v) ∧ Nat.card (pointPlane t v) = 4 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hE := IsElementaryAbelian.of_le (p := 2) m.plane_le_fullModule
  refine ⟨hE,?_⟩
  have hcomm : zpowers v ≤ centralizer (zpowers (oppositePoint t v) : Set G) :=
    (zpowers_le.mpr (partner_le_fullModule D c.escaping.t_mem c.escaping.v_mem)).trans
      (D.fullModule.le_centralizer.trans (centralizer_le
        ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left).trans
          m.plane_le_fullModule)))
  have hd : Disjoint (zpowers (oppositePoint t v)) (zpowers v) :=
    m.moved_disjoint_partner.mono (zpowers_le.mpr m.opposite_mem_moved)
      (zpowers_le.mpr m.local_point)
  rw [pointPlane,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hd,
    Nat.card_zpowers,Nat.card_zpowers]
  have ho : orderOf (oppositePoint t v) = orderOf v :=
    orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective v
  rw [ho,c.point_involution]

/-- The opposite point is fixed by the prescribed point Sylow in the local
three-space. Its orbit is the smaller module used in the parabolic argument. -/
theorem LocalFiveData.opposite_mem_seed {c : Context D t v I} (m : LocalFiveData c) :
    oppositePoint t v ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G) :=
  ⟨m.opposite_mem_moved,le_centralizer_iff.mp m.pointSylow_centralizes_plane
    ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))⟩

theorem LocalFiveData.reduced {c : Context D t v I} (m : LocalFiveData c) :
    IsPReduced 2 (localFiveModule T t v I) :=
  c.local_seed_orbit_reduced m.opposite_mem_seed

theorem LocalFiveData.orbit_le_original {c : Context D t v I} (m : LocalFiveData c) :
    localFiveOrbit t v I ≤ orbitModule D v I :=
  conjugateSpanBy_mono (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) m.opposite_mem_seed.1,
      m.opposite_mem_seed.2⟩) le_rfl

theorem LocalFiveData.orbit_le_join {c : Context D t v I} (m : LocalFiveData c) :
    localFiveOrbit t v I ≤ pointJoin T v I := m.orbit_le_original.trans c.orbit_le_join

theorem LocalFiveData.orbit_centralizer_le {c : Context D t v I} (m : LocalFiveData c) :
    centralizer (localFiveOrbit t v I : Set G) ≤ D.maximalLocal :=
  c.local_orbit_centralizer_le_of_four_natural_cover m.cover m.opposite_mem_seed
    (fun h => c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp h))

theorem LocalFiveData.kernel_detects_original {c : Context D t v I} (m : LocalFiveData c) :
    centralizer (localFiveModule T t v I : Set (pointJoin T v I)) =
      centralizer (internalModule D v I : Set (pointJoin T v I)) :=
  c.local_seed_centralizer_eq_of_four_natural_cover m.cover m.opposite_mem_seed
    (fun h => c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp h))

theorem LocalFiveData.opposite_mem_orbit {c : Context D t v I} (_m : LocalFiveData c) :
    oppositePoint t v ∈ localFiveOrbit t v I :=
  le_conjugateSpanBy _ _ (mem_zpowers _)

/-- This left-conjugation definition agrees with the source's right-conjugation
notation because t² fixes v. -/
theorem LocalFiveData.opposite_eq_right_conjugate {c : Context D t v I}
    (m : LocalFiveData c) : oppositePoint t v = t⁻¹*v*t := by
  have hh := congrArg (MulAut.conj t).symm m.exchange_opposite
  change (MulAut.conj t).symm ((MulAut.conj t) (oppositePoint t v)) = _ at hh
  simpa only [MulEquiv.symm_apply_apply, MulAut.conj_symm_apply] using hh


/-- The smaller orbit is generated by the literal opposite point. -/
theorem LocalFiveData.orbit_eq_opposite_span {c : Context D t v I}
    (_m : LocalFiveData c) :
    localFiveOrbit t v I = conjugateSpanBy (zpowers (oppositePoint t v)) I :=
  rfl

theorem LocalFiveData.five_action {c : Context D t v I} (m : LocalFiveData c) :
    letI := m.reduced.normal
    letI := m.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (localFiveModule T t v I))
    Nonempty (A ≃* SL(5,ZMod 2)) ∧ A = ⊤ ∧
      IsIrreducible ((action (localFiveModule T t v I)).comp A.subtype) ∧
      (Module.finrank (ZMod 2) (Additive (localFiveModule T t v I)) = 5 ∨
        Module.finrank (ZMod 2) (Additive (localFiveModule T t v I)) = 10) :=
  c.local_seed_five_of_local_four_natural_point m.cover m.local_point m.opposite_mem_seed
    (fun h => c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp h))

def LocalFiveData.actor {c : Context D t v I} (m : LocalFiveData c) :
    letI := m.reduced.normal
    ((I.subgroupOf (pointJoin T v I)).map (actionMk (localFiveModule T t v I))) ≃* SL(5,ZMod 2) :=
  m.five_action.1.some

theorem LocalFiveData.actor_eq_top {c : Context D t v I} (m : LocalFiveData c) :
    letI := m.reduced.normal
    (I.subgroupOf (pointJoin T v I)).map (actionMk (localFiveModule T t v I)) = ⊤ :=
  m.five_action.2.1

theorem LocalFiveData.irreducible {c : Context D t v I} (m : LocalFiveData c) :
    letI := m.reduced.normal
    letI := m.reduced.elementary
    IsIrreducible ((action (localFiveModule T t v I)).comp
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (localFiveModule T t v I))).subtype) :=
  m.five_action.2.2.1

theorem LocalFiveData.dimension {c : Context D t v I} (m : LocalFiveData c) :
    letI := m.reduced.elementary
    Module.finrank (ZMod 2) (Additive (localFiveModule T t v I)) = 5 ∨
      Module.finrank (ZMod 2) (Additive (localFiveModule T t v I)) = 10 := m.five_action.2.2.2

theorem LocalFiveData.kernel_eq {c : Context D t v I} (m : LocalFiveData c) :
    letI := m.reduced.normal
    ((actionMk (localFiveModule T t v I)).subgroupMap (I.subgroupOf (pointJoin T v I))).ker =
      pCore 2 (I.subgroupOf (pointJoin T v I)) :=
  c.local_seed_component_kernel_of_four_natural_cover m.cover m.opposite_mem_seed
    (fun h => c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp h))

end CFSG.Quasithin.Chapter10.PointControl.Constrained
