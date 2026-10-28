module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointMembership
public import Theory.GroupTheory.SylowLocalCore
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointFFSource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaComplete
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionDisplacement

/-!
# Central geometry for the original tensor point argument

A Sylow subgroup of the literal diagonal point residual maps onto a Sylow
of its A₅ quotient. A nonidentity involution in that image has identical
fixed and displacement spaces on the eight-dimensional binary module.
Lifting a displacement therefore puts each central Sylow vector in the
actual moved subgroup [V,L_N]. Its two-perfect idempotence supplies the
central-involution commutator required by source 1.2.11, proving that the
nonquasisimple component join has characteristic two and its original
Omega-center orbit is two-reduced.

The separate outside-maximal guard in 9.2.2 places the entire Omega-center
seed in V, hence in [V,L_N] and every containing point component. Every
Sylow condition here is on the actual C_T(v), as required by 1.2.11.

Source: Aschbacher--Smith 9.4.1, printed p.735, using 9.1.2(4), 9.2.2,
1.2.11 and B.2.14.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual Sylow point centralizer contains a nonidentity involution
in the literal diagonal quotient. -/
theorem tensorPoint_sylow_residual_involution (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    ∃ r : m.tensorPointResidual v, (r : G) ∈ T ∧
      m.tensorPointResidualQuotient v r ≠ 1 ∧
      (m.tensorPointResidualQuotient v r) ^ 2 = 1 := by
  obtain ⟨S,hS⟩ := hs
  have hLM : m.tensorPointResidual v ≤
      D.maximalLocal ⊓ centralizer ({(v : G)} : Set G) :=
    le_inf ((m.tensorPointResidual_le_orbit v).trans (localOrbit T L).le_normalizer)
      (m.tensorPointResidual_le_centralizer v)
  obtain ⟨P,hP⟩ := S.exists_map_subtype_eq_inf_of_normalizes hLM
    (m.tensorPointResidual_normalized v)
  rw [hS] at hP
  let Q := P.mapSurjective (m.tensorPointResidualQuotient_surjective v hv)
  have hcard : Nat.card (pointStabilizer (m.sectionData.coordinates v).toAdd) = 60 := by
    rw [Nat.card_congr (m.tensorPointStabilizerEquiv v hv).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have htwo : 2 ∣ Nat.card Q := by
    apply (Nat.prime_two.dvd_mul.mp ?_).resolve_right Q.not_dvd_index
    rw [(Q : Subgroup (pointStabilizer (m.sectionData.coordinates v).toAdd)).card_mul_index,hcard]
    norm_num
  obtain ⟨q,hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 htwo
  obtain ⟨r,hr,hrq⟩ := q.property
  refine ⟨r,?_,?_,?_⟩
  · exact ((hP ▸ (mem_map.mpr ⟨r,hr,rfl⟩)) :
      (r : G) ∈ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) ⊓
        m.tensorPointResidual v).1.1
  · intro he
    have hq1 : q = 1 := Subtype.ext (hrq.symm.trans he)
    simp only [hq1,orderOf_one] at hq
    omega
  · rw [hrq]
    exact congrArg (fun a : Q => (a : pointStabilizer
      (m.sectionData.coordinates v).toAdd)) (hq ▸ pow_orderOf_eq_one q)


/-- A vector fixed by the actual residual Sylow belongs to the literal
diagonal moved subgroup at a well-placed nonsingular point. -/
theorem tensorPoint_residual_sylow_fixed_mem_moved (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (z : D.fullModule)
    (hzc : ∀ t ∈ (T : Subgroup G), t ∈ m.tensorPointResidual v →
      t * (z : G) = (z : G) * t) :
    (z : G) ∈ ⁅D.fullModule,m.tensorPointResidual v⁆ := by
  obtain ⟨r,hrT,hrne,hr2⟩ := m.tensorPoint_sylow_residual_involution v hv hs
  let rO : localOrbit T L := ⟨r,m.tensorPointResidual_le_orbit v r.property⟩
  have hrq : m.quotient rO = (m.tensorPointResidualQuotient v r).val := rfl
  have hg : m.quotient rO ≠ 1 := by
    intro he
    exact hrne (Subtype.ext (hrq.symm.trans he))
  have hg2 : m.quotient rO ^ 2 = 1 := congrArg Subtype.val hr2
  have hfix : Binary.action (m.quotient rO) (m.sectionData.coordinates z).toAdd =
      (m.sectionData.coordinates z).toAdd :=
    (m.tensorPointCentralizer_coordinates z rO).mp
      ⟨rO.property,mem_centralizer_singleton_iff.mpr (hzc r hrT r.property)⟩
  obtain ⟨w,hw⟩ := InvolutionDisplacement.exists_displacement_of_fixed _ hg hg2 _ hfix
  obtain ⟨a,ha⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
  let b : D.fullModule := ⟨(r : G) * a * (r : G)⁻¹,
    (mem_normalizer_iff.mp (m.sectionData.normalized rO.property) a).mp a.property⟩
  let c : D.fullModule := b * a⁻¹
  have he : c = z := by
    apply m.coordinates_injective
    apply Multiplicative.toAdd.injective
    change (m.sectionData.coordinates (b * a⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    change (m.sectionData.coordinates b).toAdd + -(m.sectionData.coordinates a).toAdd = _
    rw [←sub_eq_add_neg]
    have hb := m.sectionData.equivariant rO a
    change (m.sectionData.coordinates b).toAdd = Binary.action (m.quotient rO)
      (m.sectionData.coordinates a).toAdd at hb
    rw [hb,ha]
    exact hw
  have hc : (c : G) ∈ ⁅D.fullModule,m.tensorPointResidual v⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator r.property a.property
  simpa only [he] using hc

/-- Every central Sylow vector is a displacement at a well-placed point. -/
theorem tensorPoint_central_mem_moved (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (z : D.fullModule)
    (hzc : ∀ t ∈ (T : Subgroup G), t * (z : G) = (z : G) * t) :
    (z : G) ∈ ⁅D.fullModule,m.tensorPointResidual v⁆ :=
  m.tensorPoint_residual_sylow_fixed_mem_moved v hv hs z (fun t ht _ => hzc t ht)

/-- The point itself belongs to the diagonal moved subgroup. -/
theorem tensorPoint_mem_moved (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    (v : G) ∈ ⁅D.fullModule,m.tensorPointResidual v⁆ :=
  m.tensorPoint_residual_sylow_fixed_mem_moved v hv hs v
    (fun _ _ hr => mem_centralizer_singleton_iff.mp (m.tensorPointResidual_le_centralizer v hr))

/-- The moved subgroup is elementary and lies inside the point residual. -/
theorem tensorPoint_moved_elementary_and_le (v : D.fullModule) :
    IsElementaryAbelian 2 (⁅D.fullModule,m.tensorPointResidual v⁆ : Subgroup G) ∧
      ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ m.tensorPointResidual v := by
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  exact ⟨IsElementaryAbelian.of_le (le_normalizer_iff_commutator_le_left.mp
    ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)),
    le_normalizer_iff_commutator_le_right.mp (m.tensorPointResidual_fullModule_normalized v)⟩

include m in
/-- The standing outside-maximal guard puts the entire original Sylow
Omega center in the full tensor module. -/
theorem tensorPoint_omegaCenter_le_fullModule
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ D.fullModule := by
  have hQT : (localJoin T L).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)
  intro z hz
  obtain ⟨hzT,hz2,hzC⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzΩ : z ∈ omegaCenterIn (T : Subgroup G) :=
    (mem_omegaCenterIn_iff _ _).mpr ⟨hzT,hzC,hz2⟩
  rw [m.omegaCenter_eq_fullModule_inf hout (T : Subgroup G) hQT le_rfl] at hzΩ
  exact hzΩ.1

/-- The whole Omega seed lies in the actual diagonal moved subgroup. -/
theorem tensorPoint_omegaCenter_le_moved
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      ⁅D.fullModule,m.tensorPointResidual v⁆ := by
  intro z hz
  apply m.tensorPoint_central_mem_moved v hv hs
    ⟨z,m.tensorPoint_omegaCenter_le_fullModule hout hz⟩
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2

/-- The exact source Omega-center orbit is contained in every containing
point component. -/
theorem tensorPoint_centerOrbit_le_containing
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) I ≤ I :=
  conjugateSpanBy_le_self ((m.tensorPoint_omegaCenter_le_moved hout v hv hs).trans
    ((m.tensorPoint_moved_elementary_and_le v).2.trans hLI))

/-- Original 1.2.11 has a concrete central-involution commutator witness
at every well-placed nonsingular point. -/
theorem tensorPoint_join_mem_He_source (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hq : ¬ IsQuasisimple I)
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) ∈ Chapter1.He G := by
  obtain ⟨z,hz,hzline,hzc⟩ := m.exists_central_involution_tensorLine
  have hm := m.tensorPoint_central_mem_moved v hv hs
    ⟨z,m.tensorLine_le_fullModule hzline⟩ hzc
  rw [←m.tensorPoint_moved_idempotent v] at hm
  obtain ⟨hA,hAL⟩ := m.tensorPoint_moved_elementary_and_le v
  exact m.tensorPoint_join_mem_He_of_commutator v hv hLI hIX hI hq hs
    ⁅D.fullModule,m.tensorPointResidual v⁆ hA hAL
    (normalizer_commutator_ge_right _ _) z hz (m.tensorLine_le_sylow hzline) hzc hm

/-- The characteristic-two orbit U in source 9.4.1 is two-reduced,
with the literal Sylow placement and all elementary marks discharged. -/
theorem tensorPoint_centerOrbit_reduced_source (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hq : ¬ IsQuasisimple I)
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    IsPReduced 2 ((conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) I).subgroupOf
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))) := by
  have hHe := m.tensorPoint_join_mem_He_source v hv hLI hIX hI hq hs
  have hSyl := (m.tensor_centralizer_sylow v.property hs).restrict
    (show (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ≤
      I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) from le_sup_right)
    (sup_le hIX inf_le_right)
  exact m.tensorPoint_centerOrbit_reduced v hIN hSyl hHe

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
