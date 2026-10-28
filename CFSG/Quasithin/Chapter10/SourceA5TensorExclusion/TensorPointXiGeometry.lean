module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointCentralGeometry
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointFixedLine
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointXiFusion
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointXiAction
public import Theory.Representation.OrthogonalFourPlusMatrix.PointLineTranslation
public import Theory.GroupTheory.ConjugateOrbitIndexTwo

/-!
# The literal point translation for Xi fusion

At a nonsingular point whose centralizer meets T in a Sylow subgroup, a
nontrivial diagonal Sylow involution fixes the point and the singular Sylow
line. Its fixed space is its displacement space, so adding a central vector
of that line preserves determinant. A first-factor translation realizes this
addition while preserving the plane V₁V_N. The translated point is central
in the original point Sylow and lies outside V_N.

The independent factor-exchange witness gives generation of L₀ by its
point-Sylow conjugates, using the original index-two component stabilizer.
These are precisely the geometric inputs in Aschbacher--Smith 9.4.1, p.736.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original plane V₁V_N used in the point fusion. -/
def tensorPointXiPlane (v : D.fullModule) : Subgroup G :=
  m.tensorLine ⊔ (D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G))

theorem tensorPointXiPlane_le_fullModule (v : D.fullModule) :
    m.tensorPointXiPlane v ≤ D.fullModule := sup_le m.tensorLine_le_fullModule inf_le_left

private theorem coordinates_mem_image_iff (B : Subgroup G) (x : D.fullModule) :
    (m.sectionData.coordinates x).toAdd ∈ m.sectionData.imageSpace B ↔ (x : G) ∈ B := by
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := (m.sectionData.mem_imageSpace_iff B _).mp hx
    exact (m.coordinates_injective (Multiplicative.toAdd.injective he)) ▸ hy
  · intro hx
    exact (m.sectionData.mem_imageSpace_iff B _).mpr ⟨x,hx,rfl⟩

/-- Any nonzero vector spans the original singular Sylow line over F₄. -/
theorem tensorLine_imageSpace_eq_span (z : D.fullModule) (hz : (z : G) ∈ m.tensorLine)
    (hz0 : (m.sectionData.coordinates z).toAdd ≠ 0) :
    m.sectionData.imageSpace m.tensorLine =
      (Submodule.span Binary.F ({(m.sectionData.coordinates z).toAdd} : Set Binary.V)).restrictScalars
        (ZMod 2) := by
  obtain ⟨Q,hQ⟩ := m.exists_tensorLine_coordinates_sylow
  have hzfix := hQ ▸ (m.coordinates_mem_image_iff m.tensorLine z).mpr hz
  let U := (Submodule.span Binary.F
    ({(m.sectionData.coordinates z).toAdd} : Set Binary.V)).restrictScalars (ZMod 2)
  have hle : U ≤ m.sectionData.imageSpace m.tensorLine := by
    intro x hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [hQ]
    intro a
    change matrixAction a.val (c • (m.sectionData.coordinates z).toAdd) = _
    rw [map_smul]
    exact congrArg (c • ·) (hzfix a)
  have hcU : Nat.card U = 4 := by
    change Nat.card (Submodule.span Binary.F
      ({(m.sectionData.coordinates z).toAdd} : Set Binary.V)) = 4
    rw [Module.natCard_eq_pow_finrank (K := Binary.F),finrank_span_singleton hz0,
      pow_one,Nat.card_eq_fintype_card]
    exact SL2FourNatural.card_field
  have hcV : Nat.card (m.sectionData.imageSpace m.tensorLine) = 4 := by
    rw [m.sectionData.imageSpace_card_eq_relIndex m.tensorLine m.tensorLine_le_fullModule,
      relIndex_bot_left,m.card_tensorLine]
  have he : U = m.sectionData.imageSpace m.tensorLine := by
    apply SetLike.coe_injective
    exact Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle (by
      change Nat.card (m.sectionData.imageSpace m.tensorLine) ≤ Nat.card U
      rw [hcU,hcV])
  exact he.symm

/-- Adding the central singular vector preserves determinant at the actual
well-placed nonsingular point. -/
theorem tensorPoint_add_central_line_det (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (z : D.fullModule) (hz : (z : G) ∈ m.tensorLine) :
    ((m.sectionData.coordinates v).toAdd + (m.sectionData.coordinates z).toAdd).det =
      ((m.sectionData.coordinates v).toAdd).det := by
  obtain ⟨r,hrT,hrne,hr2⟩ := m.tensorPoint_sylow_residual_involution v hv hs
  let rO : localOrbit T L := ⟨r,m.tensorPointResidual_le_orbit v r.property⟩
  have hq : m.quotient rO = (m.tensorPointResidualQuotient v r).val := rfl
  have hne : m.quotient rO ≠ 1 := by
    intro he
    exact hrne (Subtype.ext (hq.symm.trans he))
  have htwo : m.quotient rO ^ 2 = 1 := congrArg Subtype.val hr2
  have hvfix : Binary.action (m.quotient rO) (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates v).toAdd :=
    (m.tensorPointCentralizer_coordinates v rO).mp (m.tensorPointResidual_le v r.property)
  have hzfix : Binary.action (m.quotient rO) (m.sectionData.coordinates z).toAdd =
      (m.sectionData.coordinates z).toAdd := by
    apply (m.tensorPointCentralizer_coordinates z rO).mp
    exact ⟨rO.property,mem_centralizer_singleton_iff.mpr (hz.2 r ⟨hrT,rO.property⟩)⟩
  exact PointLineTranslation.det_add_of_involution_fixed _ hne htwo _ _ hvfix hzfix
    (m.tensorLine_singular ⟨z,hz⟩)

/-- The source plane contains the original nonsingular point. -/
theorem tensorPoint_mem_XiPlane (v : D.fullModule) : (v : G) ∈ m.tensorPointXiPlane v := by
  apply (show D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) ≤
    m.tensorPointXiPlane v from le_sup_right)
  exact ⟨v.property, fun r hr => mem_centralizer_singleton_iff.mp
    (m.tensorPointResidual_le_centralizer v hr)⟩

/-- The literal plane-normalizing translation needed by elementary Xi fusion.
Its new point centralizes the original C_T(v), and lies on another field line. -/
theorem exists_tensorPoint_Xi_translation (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    ∃ (g : G) (w : D.fullModule),
      g ∈ L ∧ g ∈ normalizer (m.tensorPointXiPlane v : Set G) ∧
      MulAut.conj g (v : G) = (w : G) ∧
      ((m.sectionData.coordinates w).toAdd).det ≠ 0 ∧
      (m.sectionData.coordinates w).toAdd ∉
        Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V) ∧
      (w : G) ∈ (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ∧
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) ≤
        centralizer ({(w : G)} : Set G) := by
  obtain ⟨z,hz2,hzline,hzc⟩ := m.exists_central_involution_tensorLine
  let zV : D.fullModule := ⟨z,m.tensorLine_le_fullModule hzline⟩
  have hz0 : (m.sectionData.coordinates zV).toAdd ≠ 0 := by
    intro he
    have hz1 : zV = 1 := m.coordinates_injective (Multiplicative.toAdd.injective
      (he.trans (congrArg Multiplicative.toAdd m.sectionData.coordinates.map_one).symm))
    have hz1G : z = 1 := congrArg Subtype.val hz1
    simp only [hz1G,orderOf_one] at hz2
    omega
  have hzdet : ((m.sectionData.coordinates zV).toAdd).det = 0 :=
    m.tensorLine_singular ⟨z,hzline⟩
  have hadd := m.tensorPoint_add_central_line_det v hv hs zV hzline
  obtain ⟨a,hav,haz⟩ := PointLineTranslation.exists_first_translation
    (m.sectionData.coordinates v).toAdd (m.sectionData.coordinates zV).toAdd hv hzdet hadd
  obtain ⟨d,hd⟩ := ((m.firstMarking.surjective.comp e.surjective).comp
    (QuotientGroup.mk'_surjective (pCore 2 L))) a
  change m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) d)) = a at hd
  let dO : localOrbit T L := ⟨d,le_componentOrbit L T d.property⟩
  have hdO : m.quotient dO = (a,1) := (m.first_factor d).trans (by rw [hd])
  let τ := D.fullModule.normalizerMonoidHom ⟨d,m.sectionData.normalized dO.property⟩
  have he (x : D.fullModule) : (m.sectionData.coordinates (τ x)).toAdd =
      matrixAction (a,1) (m.sectionData.coordinates x).toAdd := by
    have hh := m.sectionData.equivariant dO x
    change (m.sectionData.coordinates (τ x)).toAdd =
      Binary.action (m.quotient dO) (m.sectionData.coordinates x).toAdd at hh
    rw [hdO] at hh
    exact hh
  let w := v*zV
  have hwcoord : (m.sectionData.coordinates w).toAdd =
      (m.sectionData.coordinates v).toAdd + (m.sectionData.coordinates zV).toAdd := by
    exact congrArg Multiplicative.toAdd (m.sectionData.coordinates.map_mul v zV)
  have hτv : τ v = w := m.coordinates_injective (Multiplicative.toAdd.injective
    ((he v).trans (hav.trans hwcoord.symm)))
  refine ⟨d,w,d.property,?_,congrArg Subtype.val hτv,?_,?_,?_,?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · change (m.tensorLine ⊔ (D.fullModule ⊓ centralizer
        (m.tensorPointResidual v : Set G))).map (MulAut.conj (d : G)).toMonoidHom ≤ _
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨x,hx,rfl⟩
        let xV : D.fullModule := ⟨x,m.tensorLine_le_fullModule hx⟩
        have hxspan := (m.coordinates_mem_image_iff m.tensorLine xV).mpr hx
        rw [m.tensorLine_imageSpace_eq_span zV hzline hz0] at hxspan
        obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hxspan
        have hfix : τ xV = xV := by
          apply m.coordinates_injective
          apply Multiplicative.toAdd.injective
          rw [he,←hc,map_smul,haz]
        change MulAut.conj (d : G) x ∈ m.tensorPointXiPlane v
        rw [show MulAut.conj (d : G) x = x from congrArg Subtype.val hfix]
        exact (show m.tensorLine ≤ m.tensorPointXiPlane v from le_sup_left) hx
      · rintro _ ⟨x,hx,rfl⟩
        let xV : D.fullModule := ⟨x,hx.1⟩
        obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp
          ((m.tensorPointResidual_fixed_iff v xV hv).mp hx.2)
        have hcz : c • (m.sectionData.coordinates zV).toAdd ∈
            m.sectionData.imageSpace m.tensorLine := by
          rw [m.tensorLine_imageSpace_eq_span zV hzline hz0]
          exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
        obtain ⟨y,hy,hyc⟩ := (m.sectionData.mem_imageSpace_iff m.tensorLine _).mp hcz
        have hxy : τ xV = xV*y := by
          apply m.coordinates_injective
          apply Multiplicative.toAdd.injective
          rw [he,map_mul]
          change matrixAction (a,1) (m.sectionData.coordinates xV).toAdd =
            (m.sectionData.coordinates xV).toAdd + (m.sectionData.coordinates y).toAdd
          rw [←hc,map_smul,hav,smul_add,hyc]
        change MulAut.conj (d : G) x ∈ m.tensorPointXiPlane v
        rw [show MulAut.conj (d : G) x = x*(y : G) from congrArg Subtype.val hxy]
        exact (m.tensorPointXiPlane v).mul_mem ((show D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) ≤
          m.tensorPointXiPlane v from le_sup_right) hx)
          ((show m.tensorLine ≤ m.tensorPointXiPlane v from le_sup_left) hy)
    · rw [card_map_of_injective (MulAut.conj (d : G)).injective]
  · rwa [hwcoord,hadd]
  · rw [hwcoord]
    exact PointLineTranslation.add_not_mem_span _ _ hv hzdet hz0
  · let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
    refine ⟨m.fullModule_le_sylow w.property,?_⟩
    exact ((show D.fullModule ≤ centralizer (D.fullModule : Set G) from
      le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (Set.singleton_subset_iff.mpr v.property))) w.property
  · intro t ht
    apply mem_centralizer_singleton_iff.mpr
    change t * ((v : G)*z) = ((v : G)*z)*t
    rw [←mul_assoc,mem_centralizer_singleton_iff.mp ht.2,mul_assoc,hzc t ht.1,mul_assoc]

include m in
/-- An actual factor exchange in the point Sylow gives the whole component orbit. -/
theorem tensorPoint_sylow_componentOrbit_eq {R : Subgroup G}
    (hRT : R ≤ (T : Subgroup G)) (t : G) (ht : t ∈ R)
    (htL : t ∉ normalizer (L : Set G)) :
    componentOrbit L R = localOrbit T L := by
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
        m.sylow_not_normalizes_component) inf_le_right (hRT ht) htL
  apply le_antisymm
  · apply iSup_le
    intro r
    exact le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj (s : G)).toMonoidHom)
      ⟨r,hRT r.property⟩
  · rw [hpair]
    exact sup_le (le_componentOrbit L R)
      (le_iSup (fun r : R => L.map (MulAut.conj (r : G)).toMonoidHom) ⟨t,ht⟩)

/-- The entire fixed field line lies in the actual diagonal moved subgroup. -/
theorem tensorPoint_fixedLine_le_moved (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) ≤
      ⁅D.fullModule,m.tensorPointResidual v⁆ := by
  intro z hz
  exact m.tensorPoint_residual_sylow_fixed_mem_moved v hv hs ⟨z,hz.1⟩
    (fun t _ ht => hz.2 t ht)

/-- The source inclusions of V₁ and [V,L_N] put the literal plane in U. -/
theorem tensorPointXiPlane_le_of_line_and_moved (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    {U : Subgroup G} (hline : m.tensorLine ≤ U)
    (hmoved : ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ U) :
    m.tensorPointXiPlane v ≤ U :=
  sup_le hline ((m.tensorPoint_fixedLine_le_moved v hv hs).trans hmoved)

/-- The complete source plane V₁V_N is contained in [V,L_N]. -/
theorem tensorPointXiPlane_le_moved (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    m.tensorPointXiPlane v ≤ ⁅D.fullModule,m.tensorPointResidual v⁆ := by
  apply sup_le ?_ (m.tensorPoint_fixedLine_le_moved v hv hs)
  intro z hz
  exact m.tensorPoint_residual_sylow_fixed_mem_moved v hv hs
    ⟨z,m.tensorLine_le_fullModule hz⟩
    (fun t ht hr => hz.2 t ⟨ht,m.tensorPointResidual_le_orbit v hr⟩)

/-- Both original Xi quotient shapes have their point-translation geometry discharged. -/
theorem tensorPoint_Xi_orbit_normalizes_source
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    {X : Subgroup G}
    (hX : Chapter1.XiMember ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) X)
    (hXW : X ≤ centralizer (m.tensorPointXiPlane v : Set G))
    (hNv : centralizer ({(v : G)} : Set G) ≤ normalizer (X : Set G)) :
    localOrbit T L ≤ normalizer (X : Set G) := by
  obtain ⟨g,w,_,hg,hconj,hw,hne,_hwR,hRw⟩ := m.exists_tensorPoint_Xi_translation v hv hs
  exact (m.tensorPoint_Xi_orbit_normalizes hX v w hv hw hne
    (m.tensorPoint_mem_XiPlane v) hXW hNv g hg hconj hRw).2

/-- The actual source plane and factor exchange finish the Xi contradiction. -/
theorem tensorPoint_Xi_contradiction_of_plane
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    {X : Subgroup G}
    (hX : Chapter1.XiMember ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) X)
    (hXW : X ≤ centralizer (m.tensorPointXiPlane v : Set G))
    (hNv : centralizer ({(v : G)} : Set G) ≤ normalizer (X : Set G))
    (t : G) (ht : t ∈ (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
    (htL : t ∉ normalizer (L : Set G)) (hmove : ⁅X,m.tensorPointResidual v⁆ = X) : False :=
  m.tensorPoint_Xi_action_contradiction hX
    (m.tensorPoint_Xi_orbit_normalizes_source v hv hs hX hXW hNv) t ht ht.1 htL
    (m.tensorPoint_sylow_componentOrbit_eq inf_le_left t ht htL) v hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
