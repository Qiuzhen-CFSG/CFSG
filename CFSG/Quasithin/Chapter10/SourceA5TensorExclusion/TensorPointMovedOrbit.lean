module
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointOrbit
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointCentralGeometry
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The moved hyperplane inside the original tensor point orbit

The diagonal residual acts on the original full module through the literal
stabilizer of the nonsingular point. Its commutator image lies in the
perpendicular hyperplane. Any invariant subgroup containing a nonzero singular
moved vector contains that entire hyperplane: the additive matrix-orbit theorem
applies to its actual coordinate image, without assuming field-linearity.

The original Sylow supplies a central involution in the singular tensor line.
The point-Sylow placement puts this seed in the diagonal moved subgroup. Its
Omega-center orbit under any containing subgroup therefore contains both the
moved subgroup and the full tensor line, whose coordinates are field multiples
of the seed. The final theorem retains no orbit-generation premise.

Source: Aschbacher--Smith9.4.1, printed p.735, using9.1.2(4).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix PointOrbit Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The literal diagonal commutator maps into the perpendicular hyperplane. -/
theorem tensorPoint_moved_image_le (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    m.sectionData.imageSpace ⁅D.fullModule,m.tensorPointResidual v⁆ ≤
      (pointHyperplane (m.sectionData.coordinates v).toAdd).restrictScalars (ZMod 2) := by
  rw [commutator_comm,m.sectionData.imageSpace_commutator _ _
    (m.tensorPointResidual_le_orbit v) le_rfl]
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,w,hw,rfl⟩
  let a : pointStabilizer (m.sectionData.coordinates v).toAdd :=
    ⟨m.quotient g,(m.tensorPointCentralizer_coordinates v g).mp
      (m.tensorPointResidual_le v hg)⟩
  exact point_displacement_mem _ hv a w

private theorem imageSpace_normalized (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (U : Subgroup G) (hU : m.tensorPointResidual v ≤ normalizer (U : Set G)) :
    ∀ g : pointStabilizer (m.sectionData.coordinates v).toAdd,
      ∀ w ∈ m.sectionData.imageSpace U, matrixAction g.val w ∈ m.sectionData.imageSpace U := by
  intro g w hw
  obtain ⟨r,hr⟩ := m.tensorPointResidualQuotient_surjective v hv g
  let rO : localOrbit T L := ⟨r,m.tensorPointResidual_le_orbit v r.property⟩
  obtain ⟨a,ha,rfl⟩ := (m.sectionData.mem_imageSpace_iff U w).mp hw
  let b : D.fullModule := ⟨(r : G)*a*(r : G)⁻¹,
    (mem_normalizer_iff.mp (m.sectionData.normalized rO.property) a).mp a.property⟩
  have hb : (b : G) ∈ U := (mem_normalizer_iff.mp (hU r.property) a).mp ha
  refine (m.sectionData.mem_imageSpace_iff U _).mpr ⟨b,hb,?_⟩
  have he := m.sectionData.equivariant rO a
  change (m.sectionData.coordinates b).toAdd =
    matrixAction (m.quotient rO) (m.sectionData.coordinates a).toAdd at he
  have hq : m.quotient rO = g.val := congrArg Subtype.val hr
  rwa [hq] at he

/-- A singular moved seed in an invariant subgroup generates the entire
perpendicular hyperplane in the literal coordinates. -/
theorem tensorPoint_hyperplane_le_image_of_singular (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (U : Subgroup G) (hU : m.tensorPointResidual v ≤ normalizer (U : Set G))
    (z : D.fullModule) (hz : (z : G) ∈ U) (hz0 : z ≠ 1)
    (hzd : ((m.sectionData.coordinates z).toAdd).det = 0)
    (hzm : (z : G) ∈ ⁅D.fullModule,m.tensorPointResidual v⁆) :
    (pointHyperplane (m.sectionData.coordinates v).toAdd).restrictScalars (ZMod 2) ≤
      m.sectionData.imageSpace U := by
  have hzcoord : (m.sectionData.coordinates z).toAdd ≠ 0 := by
    intro he
    apply hz0
    apply m.coordinates_injective
    apply Multiplicative.toAdd.injective
    simpa using he
  have hzh : (m.sectionData.coordinates z).toAdd ∈
      pointHyperplane (m.sectionData.coordinates v).toAdd :=
    m.tensorPoint_moved_image_le v hv
      ((m.sectionData.mem_imageSpace_iff _ _).mpr ⟨z,hzm,rfl⟩)
  have hgeom := pointHyperplane_le_of_singular (m.sectionData.coordinates v).toAdd hv
    (m.sectionData.imageSpace U).toAddSubgroup (m.imageSpace_normalized v hv U hU)
    (m.sectionData.coordinates z).toAdd
    ((m.sectionData.mem_imageSpace_iff U _).mpr ⟨z,hz,rfl⟩) hzcoord hzd hzh
  exact hgeom

/-- Any invariant subgroup containing a nonzero singular element of the
literal diagonal commutator contains that entire commutator. -/
theorem tensorPoint_moved_le_of_singular (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (U : Subgroup G) (hU : m.tensorPointResidual v ≤ normalizer (U : Set G))
    (z : D.fullModule) (hz : (z : G) ∈ U) (hz0 : z ≠ 1)
    (hzd : ((m.sectionData.coordinates z).toAdd).det = 0)
    (hzm : (z : G) ∈ ⁅D.fullModule,m.tensorPointResidual v⁆) :
    ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ U := by
  have hgeom := m.tensorPoint_hyperplane_le_image_of_singular v hv U hU z hz hz0 hzd hzm
  have hmove : ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ D.fullModule := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)
  intro x hx
  let xV : D.fullModule := ⟨x,hmove hx⟩
  have hximage : (m.sectionData.coordinates xV).toAdd ∈ m.sectionData.imageSpace U :=
    hgeom (m.tensorPoint_moved_image_le v hv
      ((m.sectionData.mem_imageSpace_iff _ _).mpr ⟨xV,hx,rfl⟩))
  obtain ⟨y,hy,he⟩ := (m.sectionData.mem_imageSpace_iff U _).mp hximage
  have hyx : y = xV := m.coordinates_injective (Multiplicative.toAdd.injective he)
  have hyx' : (y : G) = x := congrArg (fun a : D.fullModule => (a : G)) hyx
  exact hyx' ▸ hy

/-- Every tensor-line coordinate is a field multiple of any of its nonzero
coordinates; this preserves the literal line chosen by the original Sylow. -/
theorem tensorLine_coordinates_span (z : D.fullModule)
    (hz : (z : G) ∈ m.tensorLine) (hz0 : z ≠ 1) :
    ∀ w ∈ m.sectionData.imageSpace m.tensorLine,
      w ∈ Submodule.span Binary.F ({(m.sectionData.coordinates z).toAdd} : Set Binary.V) := by
  obtain ⟨Q,hQ⟩ := m.exists_tensorLine_coordinates_sylow
  obtain ⟨g,hg⟩ := Binary.sylow_fixedSpace_conjugate_point Q
  have hzc : (m.sectionData.coordinates z).toAdd ∈ Binary.point.map (Binary.action g) := by
    rw [←hg,←hQ]
    exact (m.sectionData.mem_imageSpace_iff _ _).mpr ⟨z,hz,rfl⟩
  obtain ⟨_,⟨a,rfl⟩,ha⟩ := hzc
  have ha0 : a ≠ 0 := by
    intro he
    apply hz0
    apply m.coordinates_injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    change (m.sectionData.coordinates z).toAdd = (0 : Binary.V)
    have he0 : Binary.pointMap a = 0 := by rw [he,map_zero]
    simpa only [he0,map_zero] using ha.symm
  intro w hw
  rw [hQ,hg] at hw
  obtain ⟨_,⟨b,rfl⟩,rfl⟩ := hw
  apply Submodule.mem_span_singleton.mpr
  refine ⟨b/a,?_⟩
  rw [←ha]
  change (b/a) • matrixAction g (Binary.pointMap a) = matrixAction g (Binary.pointMap b)
  rw [←map_smul]
  apply congrArg (matrixAction g)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Binary.pointMap,div_mul_cancel₀ _ ha0]

/-- The source Sylow-center orbit contains both the diagonal moved subgroup
and the original singular tensor line. The central seed's membership in the
moved subgroup is supplied by the well-placed point-Sylow geometry. -/
theorem tensorPoint_centerOrbit_contains_moved_and_line (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (z : G) (hz2 : orderOf z = 2) (hzline : z ∈ m.tensorLine)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t*z = z*t)
    (hzm : z ∈ ⁅D.fullModule,m.tensorPointResidual v⁆) :
    ⁅D.fullModule,m.tensorPointResidual v⁆ ≤
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I ∧
    m.tensorLine ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I
  let zV : D.fullModule := ⟨z,m.tensorLine_le_fullModule hzline⟩
  have hz0 : zV ≠ 1 := by
    intro he
    have he' : z = 1 := congrArg Subtype.val he
    simp [he'] at hz2
  have hzd : ((m.sectionData.coordinates zV).toAdd).det = 0 :=
    m.tensorLine_singular ⟨z,hzline⟩
  have hzU : z ∈ U := (le_conjugateSpanBy _ I)
    ((mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨m.tensorLine_le_sylow hzline,hz2 ▸ pow_orderOf_eq_one z,hzcentral⟩)
  have hU : m.tensorPointResidual v ≤ normalizer (U : Set G) :=
    hLI.trans (le_normalizer_conjugateSpanBy _ I)
  refine ⟨m.tensorPoint_moved_le_of_singular v hv U hU zV hzU hz0 hzd hzm,?_⟩
  have hgeom := m.tensorPoint_hyperplane_le_image_of_singular v hv U hU zV hzU hz0 hzd hzm
  have hzh : (m.sectionData.coordinates zV).toAdd ∈
      pointHyperplane (m.sectionData.coordinates v).toAdd :=
    m.tensorPoint_moved_image_le v hv
      ((m.sectionData.mem_imageSpace_iff _ _).mpr ⟨zV,hzm,rfl⟩)
  intro x hx
  let xV : D.fullModule := ⟨x,m.tensorLine_le_fullModule hx⟩
  have hxs := m.tensorLine_coordinates_span zV hzline hz0
    (m.sectionData.coordinates xV).toAdd
    ((m.sectionData.mem_imageSpace_iff _ _).mpr ⟨xV,hx,rfl⟩)
  have hxh : (m.sectionData.coordinates xV).toAdd ∈
      pointHyperplane (m.sectionData.coordinates v).toAdd :=
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzh)) hxs
  obtain ⟨y,hy,he⟩ := (m.sectionData.mem_imageSpace_iff U _).mp (hgeom hxh)
  have hyx : y = xV := m.coordinates_injective (Multiplicative.toAdd.injective he)
  have hyx' : (y : G) = x := congrArg (fun a : D.fullModule => (a : G)) hyx
  exact hyx' ▸ hy

/-- Original source9.4.1 geometry: the Sylow-center orbit of any subgroup
containing the diagonal residual contains both its moved hyperplane and V₁.
The original point-Sylow placement discharges the seed's moved membership. -/
theorem tensorPoint_centerOrbit_contains_geometry (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    ⁅D.fullModule,m.tensorPointResidual v⁆ ≤
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I ∧
    m.tensorLine ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I := by
  obtain ⟨z,hz2,hzline,hzc⟩ := m.exists_central_involution_tensorLine
  exact m.tensorPoint_centerOrbit_contains_moved_and_line v hv hLI z hz2 hzline hzc
    (m.tensorPoint_central_mem_moved v hv hs ⟨z,m.tensorLine_le_fullModule hzline⟩ hzc)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
