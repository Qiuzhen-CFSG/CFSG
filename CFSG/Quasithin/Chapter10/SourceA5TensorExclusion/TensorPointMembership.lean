module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointFixedLine
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointDisplacement

/-!
The nonsingular vector belongs to the actual point residual, not merely
to the matrix quotient's moved space. Lift a matrix displacement through
the residual quotient and the original module coordinates. The full module
normalizes the residual, so this displacement is an element of the residual.
Consequently the point is an actual central element of every component
containing that residual inside its ambient point centralizer.

Source: Aschbacher--Smith 9.1.2(4) and 9.4.1, printed pp.729 and 735.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Every vector of V normalizes its literal point residual. -/
theorem tensorPointResidual_fullModule_normalized (v : D.fullModule) :
    D.fullModule ≤ normalizer (m.tensorPointResidual v : Set G) := by
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  have hVX : D.fullModule ≤ centralizer ({(v : G)} : Set G) :=
    (show D.fullModule ≤ centralizer (D.fullModule : Set G) from
      le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (Set.singleton_subset_iff.mpr v.property))
  exact (le_inf (m.fullModule_le_sylow.trans (le_normalizer_componentOrbit L T)) hVX).trans
    (m.tensorPointResidual_normalized v)

/-- The nonsingular vector belongs to its actual diagonal residual. -/
theorem tensorPoint_mem_residual (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    (v : G) ∈ m.tensorPointResidual v := by
  obtain ⟨g,w,hw⟩ := nonsingular_point_displacement (m.sectionData.coordinates v).toAdd hv
  obtain ⟨r,hr⟩ := m.tensorPointResidualQuotient_surjective v hv g
  obtain ⟨a,ha⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
  let rO : localOrbit T L := ⟨r,m.tensorPointResidual_le_orbit v r.property⟩
  let b : D.fullModule := ⟨(r : G) * a * (r : G)⁻¹,
    (mem_normalizer_iff.mp (m.sectionData.normalized rO.property) a).mp a.property⟩
  let c : D.fullModule := b * a⁻¹
  have he : c = v := by
    apply m.coordinates_injective
    apply Multiplicative.toAdd.injective
    change (m.sectionData.coordinates (b * a⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    change (m.sectionData.coordinates b).toAdd + -(m.sectionData.coordinates a).toAdd = _
    rw [←sub_eq_add_neg]
    have hb := m.sectionData.equivariant rO a
    change (m.sectionData.coordinates b).toAdd = matrixAction (m.quotient rO)
      (m.sectionData.coordinates a).toAdd at hb
    have hq : m.quotient rO = g.val := congrArg Subtype.val hr
    rw [hb,hq,ha]
    exact hw
  have hc : (c : G) ∈ m.tensorPointResidual v := by
    change (r : G) * (a : G) * (r : G)⁻¹ * (a : G)⁻¹ ∈ _
    have hn : (a : G) * (r : G)⁻¹ * (a : G)⁻¹ ∈ m.tensorPointResidual v :=
      (mem_normalizer_iff.mp (m.tensorPointResidual_fullModule_normalized v a.property)
        ((r : G)⁻¹)).mp ((m.tensorPointResidual v).inv_mem r.property)
    simpa only [mul_assoc] using (m.tensorPointResidual v).mul_mem r.property hn
  simpa only [he] using hc

/-- The central nonsingular vector is an actual element of every containing
component, with its original ambient value retained. -/
theorem tensorPoint_mem_center_of_containing (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G)) :
    (v : G) ∈ (center I).map I.subtype := by
  let vI : I := ⟨v,hLI (m.tensorPoint_mem_residual v hv)⟩
  refine ⟨vI,mem_center_iff.mpr ?_,rfl⟩
  intro i
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hIX i.property))

/-- Every point of the fixed field line belongs to the same actual residual. -/
theorem tensorPoint_fixed_le_residual (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) ≤
      m.tensorPointResidual v := by
  intro x hx
  let w : D.fullModule := ⟨x,hx.1⟩
  have hw := (m.tensorPointResidual_fixed_iff v w hv).mp hx.2
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
  by_cases hc0 : c = 0
  · have hw1 : w = 1 := by
      apply m.coordinates_injective
      apply Multiplicative.toAdd.injective
      rw [map_one]
      change (m.sectionData.coordinates w).toAdd = 0
      simpa only [hc0,zero_smul] using hc.symm
    have hx1 : x = 1 := congrArg (fun a : D.fullModule => (a : G)) hw1
    exact hx1 ▸ (m.tensorPointResidual v).one_mem
  · have hwdet : ((m.sectionData.coordinates w).toAdd).det ≠ 0 := by
      rw [←hc,Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hc0) hv
    have hcq := m.tensorPointCentralizer_eq_of_coordinates_smul v w hc0 hc.symm
    have hr : m.tensorPointResidual w = m.tensorPointResidual v := by
      unfold tensorPointResidual
      rw [hcq]
    exact hr ▸ m.tensorPoint_mem_residual w hwdet

/-- The full-module centralizer of a containing component embeds in its
actual center, giving the rank-seven refinement when that center has order two. -/
theorem tensorPoint_containing_fixed_le_center (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    D.fullModule ⊓ centralizer (I : Set G) ≤ (center I).map I.subtype := by
  intro x hx
  have hxI : x ∈ I := hLI (m.tensorPoint_fixed_le_residual v hv
    ⟨hx.1,centralizer_le hLI hx.2⟩)
  exact ⟨⟨x,hxI⟩,mem_center_iff.mpr (fun i => Subtype.ext (hx.2 i i.property)),rfl⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
