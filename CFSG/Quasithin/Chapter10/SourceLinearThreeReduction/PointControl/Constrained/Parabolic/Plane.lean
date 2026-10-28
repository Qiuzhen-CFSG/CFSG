module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Source
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original involution plane in the linear-five endgame

The saturated point Sylow is the index-two stabilizer of L. The square
of the original exchange therefore fixes v, and the exchange interchanges
v with u = t v t⁻¹ = t⁻¹ v t. Natural coordinates show that [V,L] has no
fixed vector and is disjoint from its crossed partner. Thus u and v span
an elementary plane of order four in the original full module.

The literal point Sylow centralizes this plane, while the original
exchange normalizes it. Its first coordinate u lies in the original
fixed seed and hence in VI. Inside I C_T(v), centralizing the
plane is exactly centralizing u. These are the source inputs to the
terminal parabolic argument, not its contradiction.

Source: Aschbacher--Smith, 10.2.9, printed pp.752--753, combined manuscript
of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

abbrev oppositePoint (t v : G) : G := (MulAut.conj t) v
abbrev pointPlane (t v : G) : Subgroup G := zpowers (oppositePoint t v) ⊔ zpowers v

/-- The natural marking has no fixed vector in the original moved factor. -/
theorem LinearFiveData.moved_fixed_eq_bot {c : Context D t v I} (m : LinearFiveData c) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  rintro w ⟨hw,hc⟩
  let a : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨w,hw⟩
  have hf : (m.natural.coordinates a).toAdd ∈
      Representation.OneCohomology.fixed (specialLinearNatural (k := ZMod 2) 3) := by
    intro g
    obtain ⟨l,hl⟩ := (m.quotient.surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 L))) g
    have hh := m.natural.equivariant l a
    have he : (⟨(l : G)*w*(l : G)⁻¹,
        (mem_normalizer_iff.mp (m.natural.normalized l.property) w).mp hw⟩ :
        (⁅D.fullModule,L⁆ : Subgroup G)) = a := by
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
theorem LinearFiveData.pointSylow_index {c : Context D t v I} (m : LinearFiveData c) :
    ((pointSylow T v).subgroupOf (T : Subgroup G)).index = 2 := by
  rw [c.pointSylow_eq_of_natural_three m.quotient m.natural]
  have h := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
    (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem))
  convert h using 1
  congr 1
  ext x
  exact and_iff_right x.property

/-- The exchange normalizes the full point Sylow. -/
theorem LinearFiveData.pointSylow_normalized {c : Context D t v I} (m : LinearFiveData c) :
    (T : Subgroup G) ≤ normalizer (pointSylow T v : Set G) := by
  have hn := normal_of_index_eq_two m.pointSylow_index
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

/-- The square of the original exchange already centralizes the original point. -/
theorem LinearFiveData.exchange_square_mem {c : Context D t v I} (m : LinearFiveData c) :
    t ^ 2 ∈ pointSylow T v :=
  ((pointSylow T v).subgroupOf (T : Subgroup G)).sq_mem_of_index_two
    m.pointSylow_index ⟨t,c.escaping.t_mem⟩

/-- Conjugation by the original t interchanges the two original points. -/
theorem LinearFiveData.exchange_opposite {c : Context D t v I} (m : LinearFiveData c) :
    oppositePoint t (oppositePoint t v) = v := by
  have hcomm := mem_centralizer_singleton_iff.mp m.exchange_square_mem.2
  change t*(t*v*t⁻¹)*t⁻¹ = v
  calc
    _ = t^2*v*(t^2)⁻¹ := by simp only [pow_two]; group
    _ = v := by rw [hcomm,mul_inv_cancel_right]

/-- The exchanged point is in the original moved factor, not a new model copy. -/
theorem LinearFiveData.opposite_mem_moved {c : Context D t v I} (m : LinearFiveData c) :
    oppositePoint t v ∈ ⁅D.fullModule,L⁆ := by
  obtain ⟨w,hw,hwt⟩ := c.escaping.v_mem
  have htn : t^2 ∈ normalizer (L : Set G) := by
    have hh := m.exchange_square_mem
    rw [c.pointSylow_eq_of_natural_three m.quotient m.natural] at hh
    exact hh.2
  have hWn : t^2 ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    source_moved_normalizer_local_containment D
      ⟨le_normalizer_componentOrbit L T ((T : Subgroup G).pow_mem c.escaping.t_mem 2),htn⟩
  have he : oppositePoint t v = (MulAut.conj (t^2)) w := by
    rw [←hwt]
    change t*(t*w*t⁻¹)*t⁻¹ = t^2*w*(t^2)⁻¹
    simp only [pow_two]
    group
  rw [he]
  exact (mem_normalizer_iff.mp hWn w).mp hw

/-- The literal natural three-space is disjoint from its crossed partner. -/
theorem LinearFiveData.moved_disjoint_partner {c : Context D t v I} (m : LinearFiveData c) :
    Disjoint (⁅D.fullModule,L⁆ : Subgroup G)
      ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :=
  disjoint_iff.mpr (bot_unique ((inf_le_inf_left _ c.escaping.crossed).trans_eq
    m.moved_fixed_eq_bot))

/-- The two nonidentity original points are distinct. -/
theorem LinearFiveData.opposite_ne {c : Context D t v I} (m : LinearFiveData c) :
    oppositePoint t v ≠ v := by
  intro he
  have hvW := he ▸ m.opposite_mem_moved
  exact c.escaping.v_ne (mem_bot.mp (m.moved_disjoint_partner.eq_bot ▸
    (show v ∈ (⁅D.fullModule,L⁆ : Subgroup G) ⊓
      ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) from ⟨hvW,c.escaping.v_mem⟩)))

/-- Both points and their plane lie in the original elementary full module. -/
theorem LinearFiveData.plane_le_fullModule {c : Context D t v I} (m : LinearFiveData c) :
    pointPlane t v ≤ D.fullModule := by
  have hW : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
  exact sup_le (zpowers_le.mpr (hW m.opposite_mem_moved))
    (zpowers_le.mpr (partner_le_fullModule D c.escaping.t_mem c.escaping.v_mem))

/-- The original half-Sylow centralizes both coordinates of the plane. -/
theorem LinearFiveData.pointSylow_centralizes_plane {c : Context D t v I}
    (m : LinearFiveData c) : pointSylow T v ≤ centralizer (pointPlane t v : Set G) := by
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
theorem LinearFiveData.exchange_normalizes_plane {c : Context D t v I}
    (m : LinearFiveData c) : t ∈ normalizer (pointPlane t v : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [pointPlane, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change zpowers (oppositePoint t (oppositePoint t v)) ⊔ zpowers (oppositePoint t v) = _
  rw [m.exchange_opposite, sup_comm]

/-- The original plane is elementary abelian of order four. -/
theorem LinearFiveData.plane_elementary_card {c : Context D t v I} (m : LinearFiveData c) :
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
      (zpowers_le.mpr c.escaping.v_mem)
  rw [pointPlane,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hd,
    Nat.card_zpowers,Nat.card_zpowers]
  have ho : orderOf (oppositePoint t v) = orderOf v :=
    orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective v
  rw [ho,c.point_involution]

/-- The opposite point lies in the literal orbit module and is fixed by its
prescribed point Sylow. This is the vector used in the terminal parabolic. -/
theorem LinearFiveData.opposite_mem_seed {c : Context D t v I} (m : LinearFiveData c) :
    oppositePoint t v ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (pointSylow T v : Set G) :=
  ⟨m.opposite_mem_moved,le_centralizer_iff.mp m.pointSylow_centralizes_plane
    ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))⟩

theorem LinearFiveData.opposite_mem_orbit {c : Context D t v I} (m : LinearFiveData c) :
    oppositePoint t v ∈ orbitModule D v I :=
  le_conjugateSpanBy _ _ m.opposite_mem_seed

/-- Inside the actual point join, centralizing E is exactly centralizing u. -/
theorem Context.join_plane_centralizer (c : Context D t v I) :
    pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) =
      pointJoin T v I ⊓ centralizer ({oppositePoint t v} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le
      (Set.singleton_subset_iff.mpr ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))))
  · intro g hg
    refine ⟨hg.1,?_⟩
    have hcv := (sup_le c.escaping.le_centralizer inf_le_right) hg.1
    have hE : pointPlane t v ≤ centralizer ({g} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hg.2).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hcv).symm))
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hE hx)

/-- This left-conjugation definition agrees with the source's right-conjugation
notation because t² fixes v. -/
theorem LinearFiveData.opposite_eq_right_conjugate {c : Context D t v I}
    (m : LinearFiveData c) : oppositePoint t v = t⁻¹*v*t := by
  have hh := congrArg (MulAut.conj t).symm m.exchange_opposite
  change (MulAut.conj t).symm ((MulAut.conj t) (oppositePoint t v)) = _ at hh
  simpa only [MulEquiv.symm_apply_apply, MulAut.conj_symm_apply] using hh


/-- The terminal module is generated by the orbit of the original opposite
point; no replacement of the module by a model vector is made. -/
theorem LinearFiveData.orbit_eq_opposite_span {c : Context D t v I}
    (m : LinearFiveData c) :
    orbitModule D v I = conjugateSpanBy (zpowers (oppositePoint t v)) I :=
  c.orbit_eq_of_natural_three_seed m.quotient m.natural m.opposite_mem_seed
    (fun h => c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp h))

end CFSG.Quasithin.Chapter10.PointControl.Constrained
