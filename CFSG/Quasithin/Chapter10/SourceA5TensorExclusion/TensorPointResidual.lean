module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import CFSG.Quasithin.Chapter3.Section02.FundamentalActor
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPoint
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.SpecificGroups.AlternatingFiveCore

/-!
For a vector in the original field-four tensor module, take the two-residual
of its centralizer in the component orbit. Its image is the literal matrix
point stabilizer, with a two-group kernel. At a nonsingular vector this gives
the A₅ quotient required by the diagonal local-component argument. The
residuals above two generating matrix stabilizers generate the component
orbit, since its two-core normalizes both and the orbit is two-perfect.

These results construct the actual subgroup used in source 9.4.1--2;
normality in the full ambient point centralizer is a separate source step.
Source: Aschbacher--Smith, printed pp.735--736.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

noncomputable def tensorPointCentralizer (_m : SourceA5TensorModel D e) (v : D.fullModule) : Subgroup G :=
  localOrbit T L ⊓ centralizer ({(v : G)} : Set G)

noncomputable def tensorPointResidual (v : D.fullModule) : Subgroup G :=
  (pResidual 2 (m.tensorPointCentralizer v)).map (m.tensorPointCentralizer v).subtype

theorem tensorPointResidual_le (v : D.fullModule) :
    m.tensorPointResidual v ≤ m.tensorPointCentralizer v := map_subtype_le _

theorem tensorPointResidual_le_orbit (v : D.fullModule) :
    m.tensorPointResidual v ≤ localOrbit T L := (m.tensorPointResidual_le v).trans inf_le_left

theorem tensorPointResidual_le_centralizer (v : D.fullModule) :
    m.tensorPointResidual v ≤ centralizer ({(v : G)} : Set G) :=
  (m.tensorPointResidual_le v).trans inf_le_right

theorem tensorPointResidual_isPPerfect (v : D.fullModule) :
    IsPPerfect 2 (m.tensorPointResidual v) :=
  isPPerfect_embedded_pResidual 2 _

theorem tensorPointResidual_normalized (v : D.fullModule) :
    D.maximalLocal ⊓ centralizer ({(v : G)} : Set G) ≤
      normalizer (m.tensorPointResidual v : Set G) :=
  ((le_inf (show D.maximalLocal ⊓ centralizer ({(v : G)} : Set G) ≤
      normalizer (localOrbit T L : Set G) from inf_le_left)
    (inf_le_right.trans (centralizer ({(v : G)} : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

theorem tensorPointResidual_normal_of_centralizer_le (v : D.fullModule)
    (hc : centralizer ({(v : G)} : Set G) ≤ D.maximalLocal) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G) :=
  (le_inf hc le_rfl).trans (m.tensorPointResidual_normalized v)

theorem tensorPointResidual_sylow_normalized (v : D.fullModule) :
    (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ≤
      normalizer (m.tensorPointResidual v : Set G) :=
  (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
    (m.tensorPointResidual_normalized v)

theorem tensorPointCentralizer_coordinates (v : D.fullModule) (g : localOrbit T L) :
    (g : G) ∈ m.tensorPointCentralizer v ↔
      m.quotient g ∈ pointStabilizer (m.sectionData.coordinates v).toAdd := by
  rw [mem_pointStabilizer]
  change (_ ∧ (g : G) ∈ centralizer ({(v : G)} : Set G)) ↔ _
  have hgmem : (g : G) ∈ ((localOrbit T L).toSubmonoid : Set G) := g.property
  rw [and_iff_right hgmem, mem_centralizer_singleton_iff]
  have he := m.sectionData.equivariant g v
  change (m.sectionData.coordinates
    (D.fullModule.normalizerMonoidHom ⟨g,m.sectionData.normalized g.property⟩ v)).toAdd =
      matrixAction (m.quotient g) (m.sectionData.coordinates v).toAdd at he
  rw [← he]
  constructor
  · intro hg
    apply congrArg (fun x : D.fullModule => (m.sectionData.coordinates x).toAdd)
    apply Subtype.ext
    change (g : G) * (v : G) * (g : G)⁻¹ = v
    rw [hg,mul_inv_cancel_right]
  · intro h
    have hsub := m.coordinates_injective (Multiplicative.toAdd.injective h)
    have hv := congrArg (fun x : D.fullModule => (x : G)) hsub
    exact mul_inv_eq_iff_eq_mul.mp hv

noncomputable def tensorPointQuotient (v : D.fullModule) :
    m.tensorPointCentralizer v →* pointStabilizer (m.sectionData.coordinates v).toAdd :=
  (m.quotient.comp (inclusion (show m.tensorPointCentralizer v ≤ localOrbit T L from inf_le_left))).codRestrict _
    (fun g => (m.tensorPointCentralizer_coordinates v ⟨g,g.property.1⟩).mp g.property)

theorem tensorPointQuotient_surjective (v : D.fullModule) :
    Function.Surjective (m.tensorPointQuotient v) := by
  intro a
  obtain ⟨g,hg⟩ := m.onto a.val
  have hc : (g : G) ∈ m.tensorPointCentralizer v :=
    (m.tensorPointCentralizer_coordinates v g).mpr (hg ▸ a.property)
  exact ⟨⟨g,hc⟩,Subtype.ext hg⟩

theorem tensorPointQuotient_kernel_isPGroup (v : D.fullModule) :
    IsPGroup 2 (m.tensorPointQuotient v).ker := by
  let f : (m.tensorPointQuotient v).ker →* pCore 2 (localOrbit T L) :=
    ((inclusion (show m.tensorPointCentralizer v ≤ localOrbit T L from inf_le_left)).comp
      (m.tensorPointQuotient v).ker.subtype).codRestrict _ (fun a => by
        rw [← m.kernel_eq]
        exact congrArg Subtype.val a.property)
  exact pCore_isPGroup.of_injective f (fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 (localOrbit T L) => (x.val : G)) h)))

theorem tensorPointCentralizer_eq_of_coordinates_smul
    (v w : D.fullModule) {c : Binary.F} (hc : c ≠ 0)
    (hw : (m.sectionData.coordinates w).toAdd = c • (m.sectionData.coordinates v).toAdd) :
    m.tensorPointCentralizer w = m.tensorPointCentralizer v := by
  apply le_antisymm
  · intro g hg
    have h := (m.tensorPointCentralizer_coordinates w ⟨g,hg.1⟩).mp hg
    rw [hw, pointStabilizer_smul c hc] at h
    exact (m.tensorPointCentralizer_coordinates v ⟨g,hg.1⟩).mpr h
  · intro g hg
    have h := (m.tensorPointCentralizer_coordinates v ⟨g,hg.1⟩).mp hg
    rw [← pointStabilizer_smul c hc, ← hw] at h
    exact (m.tensorPointCentralizer_coordinates w ⟨g,hg.1⟩).mpr h

noncomputable def tensorPointStabilizerEquiv (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    pointStabilizer (m.sectionData.coordinates v).toAdd ≃* alternatingGroup (Fin 5) :=
  (pointStabilizerEquiv _ hv).trans m.firstMarking.symm

theorem tensorPointStabilizer_residual (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    pResidual 2 (pointStabilizer (m.sectionData.coordinates v).toAdd) = ⊤ := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hp : IsPPerfect 2 (alternatingGroup (Fin 5)) := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (alternatingGroup (Fin 5) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (alternatingGroup (Fin 5) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (alternatingGroup (Fin 5) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5) ⧸ N) inferInstance
  apply (pResidual_eq_top_iff 2 _).mpr
  exact hp.of_surjective
    (m.tensorPointStabilizerEquiv v hv).symm.toMonoidHom
    (m.tensorPointStabilizerEquiv v hv).symm.surjective

noncomputable def tensorPointResidualQuotient (v : D.fullModule) :
    m.tensorPointResidual v →* pointStabilizer (m.sectionData.coordinates v).toAdd :=
  (m.tensorPointQuotient v).comp (inclusion (m.tensorPointResidual_le v))

theorem tensorPointResidualQuotient_surjective (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    Function.Surjective (m.tensorPointResidualQuotient v) := by
  have hmap := map_pResidual_of_surjective 2 (m.tensorPointQuotient v)
    (m.tensorPointQuotient_surjective v)
  rw [m.tensorPointStabilizer_residual v hv] at hmap
  intro a
  obtain ⟨g,hg,hga⟩ := hmap.ge (mem_top a)
  exact ⟨⟨g,mem_map.mpr ⟨g,hg,rfl⟩⟩,hga⟩

theorem tensorPointResidualQuotient_kernel_isPGroup (v : D.fullModule) :
    IsPGroup 2 (m.tensorPointResidualQuotient v).ker := by
  let f : (m.tensorPointResidualQuotient v).ker →* (m.tensorPointQuotient v).ker :=
    ((inclusion (m.tensorPointResidual_le v)).comp
      (m.tensorPointResidualQuotient v).ker.subtype).codRestrict _ (fun a => a.property)
  exact (m.tensorPointQuotient_kernel_isPGroup v).of_injective f (fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : (m.tensorPointQuotient v).ker => (x.val : G)) h)))

noncomputable def tensorPointResidualA5Equiv (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    (m.tensorPointResidual v ⧸ pCore 2 (m.tensorPointResidual v)) ≃*
      alternatingGroup (Fin 5) := by
  let f := (m.tensorPointStabilizerEquiv v hv).toMonoidHom.comp
    (m.tensorPointResidualQuotient v)
  have hf : Function.Surjective f := (m.tensorPointStabilizerEquiv v hv).surjective.comp
    (m.tensorPointResidualQuotient_surjective v hv)
  have hk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ (m.tensorPointStabilizerEquiv v hv).injective]
    exact m.tensorPointResidualQuotient_kernel_isPGroup v
  exact (f.pCoreQuotientEquiv hf hk).trans
    ((QuotientGroup.quotientMulEquivOfEq alternatingGroup.five_twoCore_eq_bot).trans
      QuotientGroup.quotientBot)


theorem tensorPointResidual_coordinateImage (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    ((m.tensorPointResidual v).subgroupOf (localOrbit T L)).map m.quotient =
      pointStabilizer (m.sectionData.coordinates v).toAdd := by
  apply le_antisymm
  · rintro a ⟨g,hg,rfl⟩
    exact (m.tensorPointCentralizer_coordinates v g).mp (m.tensorPointResidual_le v hg)
  · intro a ha
    obtain ⟨g,hg⟩ := m.tensorPointResidualQuotient_surjective v hv ⟨a,ha⟩
    exact ⟨⟨g,m.tensorPointResidual_le_orbit v g.property⟩,g.property,
      congrArg Subtype.val hg⟩

theorem tensorPointResidual_core_normalized (v : D.fullModule) :
    (localOrbit T L).pCoreIn 2 ≤ normalizer (m.tensorPointResidual v : Set G) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := hx
  apply m.tensorPointResidual_normalized v
  refine ⟨(localOrbit T L).le_normalizer a.property,?_⟩
  apply mem_centralizer_singleton_iff.mpr
  have hker : a ∈ m.quotient.ker := m.kernel_eq.symm ▸ ha
  exact ((m.centralizer_localOrbit_iff a).mpr hker v v.property).symm

theorem tensorPointResidual_sup_eq_of_stabilizers_generate (v w : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hw : ((m.sectionData.coordinates w).toAdd).det ≠ 0)
    (hgen : pointStabilizer (m.sectionData.coordinates v).toAdd ⊔
      pointStabilizer (m.sectionData.coordinates w).toAdd = ⊤) :
    m.tensorPointResidual v ⊔ m.tensorPointResidual w = localOrbit T L := by
  let J := m.tensorPointResidual v ⊔ m.tensorPointResidual w
  have hJ : J ≤ localOrbit T L :=
    sup_le (m.tensorPointResidual_le_orbit v) (m.tensorPointResidual_le_orbit w)
  have himage : (J.subgroupOf (localOrbit T L)).map m.quotient = ⊤ := by
    rw [subgroupOf_sup (m.tensorPointResidual_le_orbit v) (m.tensorPointResidual_le_orbit w),
      Subgroup.map_sup, m.tensorPointResidual_coordinateImage v hv,
      m.tensorPointResidual_coordinateImage w hw]
    exact hgen
  have hsup : J ⊔ (localOrbit T L).pCoreIn 2 = localOrbit T L := by
    have hh := congrArg (Subgroup.comap m.quotient) himage
    rw [comap_map_eq, comap_top, m.kernel_eq] at hh
    have hm := congrArg (Subgroup.map (localOrbit T L).subtype) hh
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hJ,
      ←MonoidHom.range_eq_map,range_subtype] at hm
  have hnorm : (localOrbit T L).pCoreIn 2 ≤ normalizer (J : Set G) :=
    (le_inf (m.tensorPointResidual_core_normalized v)
      (m.tensorPointResidual_core_normalized w)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact le_antisymm hJ (le_of_isPPerfect_of_le_sup_of_normalizes (localOrbit T L) J
    ((localOrbit T L).pCoreIn 2) ((pResidual_eq_top_iff 2 _).mp D.orbit_residual)
    (isPGroup_pCoreIn 2 _) hnorm hsup.ge)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
