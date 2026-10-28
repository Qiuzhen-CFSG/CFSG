module

public import Theory.AlgebraicGroup.Instance.Finite
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.Variety.Clopen

universe u

/-! Finite-index closed subgroups and their quotient fibers. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.withIdentityComponent
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup
    (H.toSubgroup ⊔ AlgebraicGroup.identityComponentSubgroup G) (by
      rw [← Variety.isClosed_iff_isZariskiClosed]
      apply Subgroup.isClosed_of_isOpen
      exact Subgroup.isOpen_mono le_sup_right
        (AlgebraicGroup.identityComponent_isOpen G))

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.withIdentityComponent_finiteIndex
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.withIdentityComponent.toSubgroup.FiniteIndex := by
  change (H.toSubgroup ⊔ AlgebraicGroup.identityComponentSubgroup G).FiniteIndex
  let : (AlgebraicGroup.identityComponentSubgroup G).FiniteIndex :=
    AlgebraicGroup.identityComponentSubgroup_finiteIndex G
  exact Subgroup.finiteIndex_of_le le_sup_right

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.withIdentityComponent_normal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    H.withIdentityComponent.toSubgroup.Normal := by
  let : H.toSubgroup.Normal := hN
  let : (AlgebraicGroup.identityComponentSubgroup G).Normal := by
    simpa [AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
  exact Subgroup.sup_normal H.toSubgroup
    (AlgebraicGroup.identityComponentSubgroup G)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.mem_withIdentityComponent_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (x : Variety.Point G) :
    x ∈ H.withIdentityComponent.toSubgroup ↔
      ∃ h ∈ H.toSubgroup, ∃ g ∈ AlgebraicGroup.identityComponentSubgroup G,
        h * g = x := by
  let : (AlgebraicGroup.identityComponentSubgroup G).Normal := by
    simpa [AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
  change x ∈ ((H.toSubgroup ⊔ AlgebraicGroup.identityComponentSubgroup G :
    Subgroup (Variety.Point G)) : Set (Variety.Point G)) ↔ _
  rw [Subgroup.mul_normal H.toSubgroup
    (AlgebraicGroup.identityComponentSubgroup G)]
  exact Set.mem_mul

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.exists_mem_same_connectedComponent_of_mem_withIdentityComponent
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (x : Variety.Point G) (hx : x ∈ H.withIdentityComponent.toSubgroup) :
    ∃ h ∈ H.toSubgroup, connectedComponent h = connectedComponent x := by
  obtain ⟨h, hh, g, hg, hprod⟩ := (H.mem_withIdentityComponent_iff x).mp hx
  refine ⟨h, hh, ?_⟩
  have hxmem : x ∈ connectedComponent h := by
    rw [connectedComponent_eq_leftCoset G h]
    exact ⟨g, hg, hprod⟩
  exact connectedComponent_eq hxmem

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.quotientFiber_isClopen
    {G : Variety k} [AlgebraicGroup G] (K : ClosedSubgroup G)
    [K.toSubgroup.FiniteIndex] [K.toSubgroup.Normal]
    (z : Variety.Point G ⧸ K.toSubgroup) :
    IsClopen {x : Variety.Point G | QuotientGroup.mk' K.toSubgroup x = z} := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K.toSubgroup z
  have hset :
      {x : Variety.Point G |
        QuotientGroup.mk' K.toSubgroup x = QuotientGroup.mk' K.toSubgroup g} =
        Set.image (fun h : Variety.Point G => g * h)
          (K.toSubgroup : Set (Variety.Point G)) := by
    ext x
    constructor
    · intro hx
      change QuotientGroup.mk' K.toSubgroup x = QuotientGroup.mk' K.toSubgroup g at hx
      rw [QuotientGroup.mk'_eq_mk'] at hx
      rcases hx with ⟨h, hh, hxh⟩
      refine ⟨h⁻¹, K.toSubgroup.inv_mem hh, ?_⟩
      calc
        g * h⁻¹ = (x * h) * h⁻¹ := by rw [hxh]
        _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]
    · rintro ⟨h, hh, rfl⟩
      change QuotientGroup.mk' K.toSubgroup (g * h) = QuotientGroup.mk' K.toSubgroup g
      rw [QuotientGroup.mk'_eq_mk']
      exact ⟨h⁻¹, K.toSubgroup.inv_mem hh, by simp [mul_assoc]⟩
  rw [hset]
  have hclosed : IsClosed (K.toSubgroup : Set (Variety.Point G)) := K.isClosed'
  have hopen : IsOpen (K.toSubgroup : Set (Variety.Point G)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex K.toSubgroup hclosed
  exact ⟨(Homeomorph.mulLeft g).isClosedMap _ hclosed,
    (Homeomorph.mulLeft g).isOpenMap _ hopen⟩

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.quotientRightTranslateFiber_isClopen
    {G : Variety k} [AlgebraicGroup G] (K : ClosedSubgroup G)
    [K.toSubgroup.FiniteIndex]
    (a : Variety.Point G) (z : Quotient (QuotientGroup.rightRel K.toSubgroup)) :
    IsClopen {x : Variety.Point G |
      @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (a * x) = z} := by
  let g := z.out
  have hz : @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) g = z := Quotient.out_eq z
  have hset :
      {x : Variety.Point G |
          @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (a * x) = z} =
        Set.image (fun h : Variety.Point G => a⁻¹ * h * g)
          (K.toSubgroup : Set (Variety.Point G)) := by
    ext x
    constructor
    · intro hx
      have hx' :
          @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (a * x) =
            @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) g := by
        simpa [hz] using hx
      have hrel : QuotientGroup.rightRel K.toSubgroup (a * x) g := Quotient.eq'.mp hx'
      have hmem : g * (a * x)⁻¹ ∈ K.toSubgroup :=
        QuotientGroup.rightRel_apply.mp hrel
      refine ⟨a * x * g⁻¹, by
        simpa [mul_assoc] using K.toSubgroup.inv_mem hmem, ?_⟩
      simp [mul_assoc]
    · rintro ⟨h, hh, rfl⟩
      have hmem : g * (h * g)⁻¹ ∈ K.toSubgroup := by
        simpa [mul_assoc] using K.toSubgroup.inv_mem hh
      have hq :
          @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup)
              (a * (a⁻¹ * h * g)) =
            @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) g := by
        apply Quotient.eq'.mpr
        exact QuotientGroup.rightRel_apply.mpr (by simpa [mul_assoc] using hmem)
      simpa [mul_assoc, hz] using hq
  rw [hset]
  have hclosed : IsClosed (K.toSubgroup : Set (Variety.Point G)) := K.isClosed'
  have hopen : IsOpen (K.toSubgroup : Set (Variety.Point G)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex K.toSubgroup hclosed
  have hclosed' :
      IsClosed ((fun h : Variety.Point G => h * g) ''
        (K.toSubgroup : Set (Variety.Point G))) :=
    (Homeomorph.mulRight g).isClosedMap _ hclosed
  have hopen' :
      IsOpen ((fun h : Variety.Point G => h * g) ''
        (K.toSubgroup : Set (Variety.Point G))) :=
    (Homeomorph.mulRight g).isOpenMap _ hopen
  exact ⟨by
      simpa only [Homeomorph.coe_mulLeft, Set.image_image, mul_assoc] using
        (Homeomorph.mulLeft a⁻¹).isClosedMap _ hclosed',
    by
      simpa only [Homeomorph.coe_mulLeft, Set.image_image, mul_assoc] using
        (Homeomorph.mulLeft a⁻¹).isOpenMap _ hopen'⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A finite-index closed subgroup still maps surjectively to a connected
target under a surjective morphism. -/
public theorem finiteIndex_subgroup_surjective_of_connected_target
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (P : ClosedSubgroup G) [AlgebraicGroup P.carrierVariety]
    (I : ClosedSubgroup P.carrierVariety) [I.toSubgroup.FiniteIndex]
    (R : ClosedSubgroup H)
    (g : AlgebraicGroup.Morphism P.carrierVariety R.carrierVariety)
    (hg : Function.Surjective g.onPoints)
    (hR : _root_.IsConnected (R : Set (Variety.Point H))) :
    Function.Surjective (fun x => g.onPoints (I.pointEquiv x).val) := by
  let hI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let : AlgebraicGroup I.carrierVariety := hI
  let iinc : AlgebraicGroup.Morphism I.carrierVariety P.carrierVariety :=
    I.inclusion
  let gI := g.comp iinc
  let J := gI.imageClosedSubgroup
  have hJmap : J.toSubgroup = I.toSubgroup.map g.onPoints := by
    ext y
    constructor
    · intro hy
      change y ∈ gI.image at hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨iinc.onPoints x, (I.pointEquiv x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      change g.onPoints x ∈ gI.image
      let z : Variety.Point I.carrierVariety := I.pointEquiv.symm ⟨x, hx⟩
      refine ⟨z, ?_⟩
      change g.onPoints (iinc.onPoints z) = g.onPoints x
      congr 2
  let : J.toSubgroup.FiniteIndex := by
    rw [hJmap]
    refine ⟨?_⟩
    intro hzero
    have hdvd := I.toSubgroup.index_map_dvd hg
    rw [hzero] at hdvd
    have hIzero : I.toSubgroup.index = 0 := by simpa using hdvd
    exact Subgroup.FiniteIndex.index_ne_zero (H := I.toSubgroup) hIzero
  have hRvar : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point H // x ∈ (R : Set (Variety.Point H))} :=
      Subtype.connectedSpace hR
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hRJ : (Set.univ : Set (Variety.Point R.carrierVariety)) ⊆ J := by
    rw [← (identityComponent_eq_univ_iff_isConnected R.carrierVariety).mpr hRvar]
    exact identityComponent_subset_of_finiteIndexSubgroup R.carrierVariety J
  change Function.Surjective gI.onPoints
  intro y
  have hyJ : y ∈ J := hRJ (by trivial)
  change y ∈ gI.image at hyJ
  exact hyJ

end

/-! Fibers of the quotient by the identity component are clopen components. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma identityComponentQuotientFiber_isClopen
    (G : Variety k) [AlgebraicGroup G] :
    let H := AlgebraicGroup.identityComponentSubgroup G
    let _ : H.Normal := by
      simpa [H, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
        AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
    ∀ z : Variety.Point G ⧸ H,
      IsClopen {x : Variety.Point G | QuotientGroup.mk' H x = z} := by
  dsimp only
  let H := AlgebraicGroup.identityComponentSubgroup G
  let : H.Normal := by
    simpa [H, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H z
  have hset : {x : Variety.Point G | QuotientGroup.mk' H x = QuotientGroup.mk' H g} =
      Set.image (fun h : Variety.Point G => g * h) (H : Set (Variety.Point G)) := by
    ext x
    constructor
    · intro hx
      change QuotientGroup.mk' H x = QuotientGroup.mk' H g at hx
      rw [QuotientGroup.mk'_eq_mk'] at hx
      rcases hx with ⟨h, hh, hxh⟩
      refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
      calc
        g * h⁻¹ = (x * h) * h⁻¹ := by rw [hxh]
        _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]
    · rintro ⟨h, hh, rfl⟩
      change QuotientGroup.mk' H (g * h) = QuotientGroup.mk' H g
      rw [QuotientGroup.mk'_eq_mk']
      exact ⟨h⁻¹, H.inv_mem hh, by simp [mul_assoc]⟩
  rw [hset, ← connectedComponent_eq_leftCoset G g]
  exact ⟨isClosed_connectedComponent, by
    rw [connectedComponent_eq_leftCoset G g]
    exact (isOpenMap_mul_left g) _ (AlgebraicGroup.identityComponent_isOpen G)⟩

end

/-! Finite constant quotients by finite-index normal closed subgroups. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.finiteQuotientProjection_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    [H.toSubgroup.FiniteIndex] [H.toSubgroup.Normal] :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (π : AlgebraicGroup.Morphism G Q),
      Finite (Variety.Point Q) ∧ Function.Surjective π.onPoints ∧
        π.kernel = H.toSubgroup := by
  classical
  let F := Variety.Point G ⧸ H.toSubgroup
  let : Finite F := Subgroup.finite_quotient_of_finiteIndex
  let : Fintype F := Fintype.ofFinite F
  let q : Variety.Point G →* F := QuotientGroup.mk' H.toSubgroup
  let p : F → MvPolynomial G.Coordinates k := fun z =>
    Classical.choose (exists_polynomial_eq_one_on_of_isClopen G
      {x : Variety.Point G | q x = z}
      (H.quotientFiber_isClopen z))
  have hp (z : F) := Classical.choose_spec
    (exists_polynomial_eq_one_on_of_isClopen G
      {x : Variety.Point G | q x = z}
      (H.quotientFiber_isClopen z))
  let π : AlgebraicGroup.Morphism G (finiteGroupVariety k F) :=
    { toVariety :=
        { toFun := fun x => finiteGroupPoint (k := k) F (q x)
          regular := by
            intro z
            refine ⟨p z, fun x => ?_⟩
            change @ite k (z = q x) (Classical.propDecidable _) 1 0 =
              evalPolynomial x.val (p z)
            by_cases hz : q x = z
            · rw [if_pos hz.symm]
              exact ((hp z).1 x hz).symm
            · rw [if_neg (fun h : z = q x => hz h.symm)]
              exact ((hp z).2 x hz).symm }
      map_one := by
        change finiteGroupPoint (k := k) F (q 1) = 1
        rw [q.map_one, finiteGroupPoint_one]
      map_mul := by
        intro x y
        change finiteGroupPoint (k := k) F (q (x * y)) =
          finiteGroupPoint (k := k) F (q x) * finiteGroupPoint (k := k) F (q y)
        rw [q.map_mul, finiteGroupPoint_mul] }
  let e := finiteGroupPointEquiv (k := k) F
  let : Finite (Variety.Point (finiteGroupVariety k F)) :=
    Finite.of_injective e e.injective
  refine ⟨finiteGroupVariety k F, inferInstance, π, inferInstance, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective H.toSubgroup (e y)
    refine ⟨x, ?_⟩
    change finiteGroupPoint (k := k) F (q x) = y
    rw [hx]
    exact e.symm_apply_apply y
  · ext x
    constructor
    · intro hx
      have hx1 := MonoidHom.mem_ker.mp hx
      have hq : q x = 1 := by
        change finiteGroupPoint (k := k) F (q x) = 1 at hx1
        calc
          q x = e (finiteGroupPoint (k := k) F (q x)) := (e.apply_symm_apply (q x)).symm
          _ = e 1 := congrArg e hx1
          _ = 1 := by
            rw [← finiteGroupPoint_one (k := k) F]
            exact e.apply_symm_apply 1
      exact (QuotientGroup.eq_one_iff x).mp hq
    · intro hx
      apply MonoidHom.mem_ker.mpr
      change finiteGroupPoint (k := k) F (q x) = 1
      have hq : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hq, finiteGroupPoint_one]

end

/-! Left-translated fibers of finite quotient projections are clopen. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
lemma ClosedSubgroup.quotientLeftTranslateFiber_isClopen
    {G : Variety k} [AlgebraicGroup G] (K : ClosedSubgroup G)
    [K.toSubgroup.FiniteIndex] [K.toSubgroup.Normal]
    (a : Variety.Point G) (z : Variety.Point G ⧸ K.toSubgroup) :
    IsClopen {x : Variety.Point G | QuotientGroup.mk' K.toSubgroup (a * x) = z} := by
  change IsClopen ((fun x : Variety.Point G => a * x) ⁻¹'
    {y : Variety.Point G | QuotientGroup.mk' K.toSubgroup y = z})
  exact (K.quotientFiber_isClopen z).preimage (Homeomorph.mulLeft a).continuous

end
end Theory.AlgebraicGroup
