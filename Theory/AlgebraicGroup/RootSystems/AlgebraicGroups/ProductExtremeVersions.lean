module

public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Borel.SemisimpleCenter
public import Theory.AlgebraicGroup.Foundations
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Semisimple.Product
public import Theory.AlgebraicGroup.Semisimple.Versions

/-!
# Product stability of extreme semisimple versions

This module proves that products preserve the universal and adjoint versions of
semisimple algebraic groups. Product semisimplicity is supplied by the lower
`Semisimple.Product` module, where radicals are projected to the two factors.
For universal versions, the factor retractions first lift through an arbitrary
isogeny; the two lifts commute because their commutator has connected source
and finite range. Their product is an isogeny because its composite with the
original map is the product of the factor isogenies.
For adjoint versions, the same finite-kernel argument is reduced to the
triviality of the product center. The result is the structural product step
used by the root-system decomposition of GLS3, Chapter 1, Theorem 1.10.6.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem variety_prod_isConnected
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : Variety.IsConnected G) (hH : Variety.IsConnected H) :
    Variety.IsConnected (Variety.prod G H) := by
  have hI := prodSet_irreducible_of_irreducible
    (connectedAlgebraicGroup_irreducible G hG)
    (connectedAlgebraicGroup_irreducible H hH)
  have hprod : Variety.prodSet
      (Set.univ : Set (Variety.Point G))
      (Set.univ : Set (Variety.Point H)) =
      (Set.univ : Set (Variety.Point (Variety.prod G H))) := by
    ext z
    simp [Variety.prodSet]
  rw [hprod] at hI
  exact hI.isConnected

omit [IsAlgClosed k] in
private theorem ClosedSubgroup.carrierVariety_isConnected
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : _root_.IsConnected (S : Set (Variety.Point G))) :
    Variety.IsConnected S.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
  let : ConnectedSpace
      {x : Variety.Point G // x ∈ (S : Set (Variety.Point G))} :=
    Subtype.connectedSpace hS
  let : ConnectedSpace (Variety.Point S.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private theorem isogeny_comp
    {A B C : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    [AlgebraicGroup C]
    (f : Morphism A B) (g : Morphism B C)
    (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (g.comp f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  let first : (g.comp f).kernel →* g.kernel :=
    { toFun := fun z =>
        ⟨f.onPoints z.1, by
          change g.onPoints (f.onPoints z.1) = 1
          exact MonoidHom.mem_ker.mp z.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  letI : Finite g.kernel := hg.2
  have hrange : Finite first.range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hker : Finite first.ker := by
    let embed : first.ker → f.kernel := fun z =>
      ⟨z.1.1, by
        change f.onPoints z.1.1 = 1
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp z.2)⟩
    letI : Finite f.kernel := hf.2
    exact Finite.of_injective embed (by
      intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : f.kernel => t.1) hzw)
  exact first.finite_iff_finite_ker_range.mpr ⟨hker, hrange⟩

private theorem isogeny_of_comp
    {A B C : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    [AlgebraicGroup C]
    (f : Morphism A B) (g : Morphism B C)
    (hAconnected : Variety.IsConnected A)
    (hBconnected : Variety.IsConnected B)
    (hg : IsIsogeny g) (hgf : IsIsogeny (g.comp f)) :
    IsIsogeny f := by
  have hkerfin : Finite g.kernel := hg.2
  let I := f.imageClosedSubgroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  have hIconn : _root_.IsConnected (I : Set (Variety.Point B)) :=
    f.imageClosedSubgroup_isConnected hAconnected
  have hcover : ∀ x : Variety.Point B, ∃ y : Variety.Point I.carrierVariety,
      ∃ z : g.kernel, z.1 * I.inclusion.onPoints y = x := by
    intro x
    obtain ⟨a, ha⟩ := hgf.1 (g.onPoints x)
    let y : Variety.Point I.carrierVariety := I.pointEquiv.symm
      ⟨f.onPoints a, ⟨a, rfl⟩⟩
    refine ⟨y, ?_⟩
    change g.onPoints (f.onPoints a) = g.onPoints x at ha
    have hzker : g.onPoints (x * (f.onPoints a)⁻¹) = 1 := by
      rw [g.onPoints.map_mul, g.onPoints.map_inv, ← ha, mul_inv_cancel]
    let z : g.kernel := ⟨x * (f.onPoints a)⁻¹, hzker⟩
    refine ⟨z, ?_⟩
    change x * (f.onPoints a)⁻¹ * f.onPoints a = x
    rw [mul_assoc, inv_mul_cancel, mul_one]
  letI : Finite g.kernel := hkerfin
  let q : g.kernel → (Variety.Point B ⧸ I.toSubgroup) := fun z =>
    QuotientGroup.mk z.1
  have hqsurj : Function.Surjective q := by
    intro c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨y, z, hxyz⟩ := hcover x
    refine ⟨z, ?_⟩
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    have hxy := congrArg (fun w => z.1⁻¹ * w) hxyz
    have heq : z.1⁻¹ * x = I.inclusion.onPoints y := by
      simpa [mul_assoc] using hxy.symm
    rw [heq]
    exact (I.pointEquiv y).property
  letI : Finite (Variety.Point B ⧸ I.toSubgroup) :=
    Finite.of_surjective q hqsurj
  letI : I.toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hItop : I.toSubgroup = ⊤ := by
    apply le_antisymm
    · exact le_top
    · intro x _
      have hxcomp : x ∈ AlgebraicGroup.identityComponent B := by
        rw [(identityComponent_eq_univ_iff_isConnected B).mpr hBconnected]
        trivial
      exact identityComponent_subset_of_finiteIndexSubgroup B I hxcomp
  have hfsurj : Function.Surjective f.onPoints := by
    intro x
    have hxI : x ∈ I.toSubgroup := by rw [hItop]; trivial
    change x ∈ f.image at hxI
    exact hxI
  refine ⟨hfsurj, ?_⟩
  let embed : f.kernel → (g.comp f).kernel := fun z =>
    ⟨z.1, by
      change g.onPoints (f.onPoints z.1) = 1
      rw [MonoidHom.mem_ker.mp z.2, g.onPoints.map_one]⟩
  letI : Finite (g.comp f).kernel := hgf.2
  exact Finite.of_injective embed (by
    intro z w hzw
    apply Subtype.ext
    exact congrArg (fun t : (g.comp f).kernel => t.1) hzw)

omit [IsAlgClosed k] in
private theorem isogeny_prod
    {A B C D : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    [AlgebraicGroup C] [AlgebraicGroup D]
    (f : Morphism A B) (g : Morphism C D)
    (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (Morphism.prod
      (f.comp (Morphism.fst A C)) (g.comp (Morphism.snd A C))) := by
  let e : Morphism (Variety.prod A C) (Variety.prod B D) :=
    Morphism.prod (f.comp (Morphism.fst A C)) (g.comp (Morphism.snd A C))
  have he_apply (z : Variety.Point (Variety.prod A C)) :
      (Variety.prodPointEquiv B D) (e.onPoints z) =
        (f.onPoints ((Variety.prodPointEquiv A C) z).1,
          g.onPoints ((Variety.prodPointEquiv A C) z).2) := by
    rfl
  refine ⟨?_, ?_⟩
  · intro z
    let b := ((Variety.prodPointEquiv B D) z).1
    let d := ((Variety.prodPointEquiv B D) z).2
    obtain ⟨a, ha⟩ := hf.1 b
    obtain ⟨c, hc⟩ := hg.1 d
    refine ⟨(Variety.prodPointEquiv A C).symm (a, c), ?_⟩
    apply (Variety.prodPointEquiv B D).injective
    rw [he_apply, (Variety.prodPointEquiv A C).apply_symm_apply]
    exact Prod.ext ha hc
  · let embed : e.kernel → f.kernel × g.kernel := fun z =>
      (⟨((Variety.prodPointEquiv A C) z.1).1, by
          have hz := MonoidHom.mem_ker.mp z.2
          have hz' := congrArg (Variety.prodPointEquiv B D) hz
          exact congrArg Prod.fst (by simpa [he_apply] using hz')⟩,
        ⟨((Variety.prodPointEquiv A C) z.1).2, by
          have hz := MonoidHom.mem_ker.mp z.2
          have hz' := congrArg (Variety.prodPointEquiv B D) hz
          exact congrArg Prod.snd (by simpa [he_apply] using hz')⟩)
    letI : Finite f.kernel := hf.2
    letI : Finite g.kernel := hg.2
    exact Finite.of_injective embed (by
      intro z w hzw
      apply Subtype.ext
      apply (Variety.prodPointEquiv A C).injective
      exact Prod.ext
        (congrArg (fun t : f.kernel × g.kernel => t.1.1) hzw)
        (congrArg (fun t : f.kernel × g.kernel => t.2.1) hzw))

omit [IsAlgClosed k] in
private theorem product_inl_mul_inr
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (x : Variety.Point G) (y : Variety.Point H) :
    (Morphism.inl G H).onPoints x * (Morphism.inr G H).onPoints y =
      (Variety.prodPointEquiv G H).symm (x, y) := by
  apply (Variety.prodPointEquiv G H).injective
  rw [(Variety.prodPointEquiv G H).apply_symm_apply]
  apply Prod.ext
  · change (Morphism.fst G H).onPoints
      ((Morphism.inl G H).onPoints x * (Morphism.inr G H).onPoints y) = x
    rw [map_mul, product_fst_inl]
    have hcross : (Morphism.fst G H).onPoints
        ((Morphism.inr G H).onPoints y) = 1 := by
      rfl
    rw [hcross, mul_one]
  · change (Morphism.snd G H).onPoints
      ((Morphism.inl G H).onPoints x * (Morphism.inr G H).onPoints y) = y
    rw [map_mul, product_snd_inr]
    have hcross : (Morphism.snd G H).onPoints
        ((Morphism.inl G H).onPoints x) = 1 := by
      rfl
    rw [hcross, one_mul]

omit [IsAlgClosed k] in
private theorem product_inl_commute_inr
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (x : Variety.Point G) (y : Variety.Point H) :
    (Morphism.inl G H).onPoints x * (Morphism.inr G H).onPoints y =
      (Morphism.inr G H).onPoints y * (Morphism.inl G H).onPoints x := by
  apply (Variety.prodPointEquiv G H).injective
  apply Prod.ext
  · change (Morphism.fst G H).onPoints
        ((Morphism.inl G H).onPoints x * (Morphism.inr G H).onPoints y) =
      (Morphism.fst G H).onPoints
        ((Morphism.inr G H).onPoints y * (Morphism.inl G H).onPoints x)
    rw [map_mul, map_mul, product_fst_inl]
    have hcross : (Morphism.fst G H).onPoints
        ((Morphism.inr G H).onPoints y) = 1 := by
      rfl
    rw [hcross, mul_one, one_mul]
  · change (Morphism.snd G H).onPoints
        ((Morphism.inl G H).onPoints x * (Morphism.inr G H).onPoints y) =
      (Morphism.snd G H).onPoints
        ((Morphism.inr G H).onPoints y * (Morphism.inl G H).onPoints x)
    rw [map_mul, map_mul, product_snd_inr]
    have hcross : (Morphism.snd G H).onPoints
        ((Morphism.inl G H).onPoints x) = 1 := by
      rfl
    rw [hcross, one_mul, mul_one]

private theorem IsUniversalVersion.exists_lift_of_retract
    {X K C : Variety k}
    [AlgebraicGroup X] [AlgebraicGroup K] [AlgebraicGroup C]
    (hX : IsUniversalVersion X)
    (i : Morphism X K) (p : Morphism K X)
    (hpi : Function.LeftInverse p.onPoints i.onPoints)
    (phi : Morphism C K) (hphi : IsIsogeny phi) :
    ∃ a : Morphism X C, ∃ e : Morphism X X,
      IsIsogeny e ∧
        ∀ x, phi.onPoints (a.onPoints x) = i.onPoints (e.onPoints x) := by
  let I := i.imageClosedSubgroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  have hIconnected : Variety.IsConnected I.carrierVariety :=
    I.carrierVariety_isConnected (i.imageClosedSubgroup_isConnected hX.1.1)
  let P := phi.closedSubgroupPreimage I
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let P0 := identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P0.carrierVariety := P0.carrierAlgebraicGroup
  let g : Morphism P0.carrierVariety I.carrierVariety :=
    (phi.preimageRestriction I).comp P0.inclusion
  let pI : Morphism I.carrierVariety X := p.comp I.inclusion
  let q : Morphism P0.carrierVariety X := pI.comp g
  have hgsurj : Function.Surjective g.onPoints := by
    exact phi.preimageRestriction_identityComponent_surjective
      hphi.1 I hIconnected
  have hreconstruct (y : Variety.Point I.carrierVariety) :
      i.onPoints (p.onPoints (I.inclusion.onPoints y)) =
        I.inclusion.onPoints y := by
    have hy : I.inclusion.onPoints y ∈ i.image := (I.pointEquiv y).property
    obtain ⟨x, hx⟩ := hy
    rw [← hx, hpi]
  have hqsurj : Function.Surjective q.onPoints := by
    intro x
    let xI : Variety.Point I.carrierVariety :=
      I.pointEquiv.symm ⟨i.onPoints x, ⟨x, rfl⟩⟩
    obtain ⟨z, hz⟩ := hgsurj xI
    refine ⟨z, ?_⟩
    change p.onPoints (I.inclusion.onPoints (g.onPoints z)) = x
    rw [hz]
    have hxI : I.inclusion.onPoints xI = i.onPoints x := by
      change (I.pointEquiv xI).val = i.onPoints x
      simp [xI]
    rw [hxI, hpi]
  let embed : q.kernel → phi.kernel := fun z =>
    ⟨P.inclusion.onPoints (P0.inclusion.onPoints z.1), by
      change phi.onPoints
          (P.inclusion.onPoints (P0.inclusion.onPoints z.1)) = 1
      rw [← phi.preimageRestriction_inclusion_apply I]
      change I.inclusion.onPoints (g.onPoints z.1) = 1
      have hqz : p.onPoints (I.inclusion.onPoints (g.onPoints z.1)) = 1 :=
        MonoidHom.mem_ker.mp z.2
      have hrec := hreconstruct (g.onPoints z.1)
      rw [hqz, map_one] at hrec
      exact hrec.symm⟩
  have hembed : Function.Injective embed := by
    intro z w hzw
    have hambient :
        P.inclusion.onPoints (P0.inclusion.onPoints z.1) =
          P.inclusion.onPoints (P0.inclusion.onPoints w.1) := by
      have := congrArg (fun t : phi.kernel => t.1) hzw
      change P.inclusion.onPoints (P0.inclusion.onPoints z.1) =
        P.inclusion.onPoints (P0.inclusion.onPoints w.1) at this
      exact this
    apply Subtype.ext
    apply P0.inclusion_injective
    exact P.inclusion_injective hambient
  let : Finite phi.kernel := hphi.2
  have hqfinite : Finite q.kernel := Finite.of_injective embed hembed
  have hP0connected : _root_.IsConnected
      (Set.univ : Set (Variety.Point P0.carrierVariety)) :=
    identityComponentClosedSubgroup_carrier_isConnected P.carrierVariety
  have hq : IsIsogeny q := ⟨hqsurj, hqfinite⟩
  obtain ⟨s, hs⟩ := hX.exists_isogeny hP0connected q hq
  let e : Morphism X X := q.comp s
  have he : IsIsogeny e := isogeny_comp s q hs hq
  let a : Morphism X C := P.inclusion.comp (P0.inclusion.comp s)
  refine ⟨a, e, he, ?_⟩
  intro x
  change phi.onPoints
      (P.inclusion.onPoints (P0.inclusion.onPoints (s.onPoints x))) =
    i.onPoints (q.onPoints (s.onPoints x))
  rw [← phi.preimageRestriction_inclusion_apply I]
  exact (hreconstruct (g.onPoints (s.onPoints x))).symm

private theorem universalVersion_product
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : IsUniversalVersion G) (hH : IsUniversalVersion H) :
    IsUniversalVersion (Variety.prod G H) := by
  refine ⟨semisimple_product hG.1 hH.1, ?_⟩
  intro C _ hCconnected phi hphi
  obtain ⟨a, eG, heG, ha⟩ := hG.exists_lift_of_retract
    (Morphism.inl G H) (Morphism.fst G H)
    (product_fst_inl G H) phi hphi
  obtain ⟨b, eH, heH, hb⟩ := hH.exists_lift_of_retract
    (Morphism.inr G H) (Morphism.snd G H)
    (product_snd_inr G H) phi hphi
  let av : Variety.Morphism (Variety.prod G H) C :=
    a.toVariety.comp (Variety.Morphism.fst G H)
  let bv : Variety.Morphism (Variety.prod G H) C :=
    b.toVariety.comp (Variety.Morphism.snd G H)
  let c : Variety.Morphism (Variety.prod G H) C :=
    (AlgebraicGroup.commutatorMorphism C).comp (av.pair bv)
  have hc_apply (x : Variety.Point G) (y : Variety.Point H) :
      c.toFun ((Variety.prodPointEquiv G H).symm (x, y)) =
        a.onPoints x * b.onPoints y * (a.onPoints x)⁻¹ *
          (b.onPoints y)⁻¹ := by
    change (AlgebraicGroup.commutatorMorphism C).toFun
      ((Variety.prodPointEquiv C C).symm (a.onPoints x, b.onPoints y)) = _
    exact AlgebraicGroup.commutatorMorphism_apply C _ _
  have hcrange : Set.range c.toFun ⊆
      (phi.kernel : Set (Variety.Point C)) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨⟨x, y⟩, rfl⟩ :=
      (Variety.prodPointEquiv G H).symm.surjective z
    change phi.onPoints
      (c.toFun ((Variety.prodPointEquiv G H).symm (x, y))) = 1
    rw [hc_apply, map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb]
    rw [product_inl_commute_inr]
    group
  let : Finite phi.kernel := hphi.2
  have hcfinite : (Set.range c.toFun).Finite :=
    (Set.toFinite (phi.kernel : Set (Variety.Point C))).subset hcrange
  have hcsub := connected_finite_morphism_range_subsingleton c
    (variety_prod_isConnected hG.1.1 hH.1.1) hcfinite
  have hcomm (x : Variety.Point G) (y : Variety.Point H) :
      a.onPoints x * b.onPoints y = b.onPoints y * a.onPoints x := by
    have heq := hcsub
      (Set.mem_range_self ((Variety.prodPointEquiv G H).symm (x, y)))
      (Set.mem_range_self ((Variety.prodPointEquiv G H).symm (1, 1)))
    rw [hc_apply, hc_apply] at heq
    have hcOne :
        a.onPoints x * b.onPoints y * (a.onPoints x)⁻¹ *
            (b.onPoints y)⁻¹ = 1 := by
      simpa using heq
    exact commutatorElement_eq_one_iff_mul_comm.mp (by
      simpa [commutatorElement_def] using hcOne)
  let sVar : Variety.Morphism (Variety.prod G H) C :=
    (AlgebraicGroup.mulMorphism C).comp (av.pair bv)
  let s : Morphism (Variety.prod G H) C :=
    { toVariety := sVar
      map_one := by
        change a.onPoints 1 * b.onPoints 1 = 1
        simp
      map_mul := by
        intro z w
        obtain ⟨⟨x1, y1⟩, rfl⟩ :=
          (Variety.prodPointEquiv G H).symm.surjective z
        obtain ⟨⟨x2, y2⟩, rfl⟩ :=
          (Variety.prodPointEquiv G H).symm.surjective w
        change a.onPoints (x1 * x2) * b.onPoints (y1 * y2) =
          (a.onPoints x1 * b.onPoints y1) *
            (a.onPoints x2 * b.onPoints y2)
        rw [map_mul, map_mul]
        calc
          a.onPoints x1 * a.onPoints x2 *
                (b.onPoints y1 * b.onPoints y2) =
              a.onPoints x1 * (a.onPoints x2 * b.onPoints y1) *
                b.onPoints y2 := by group
          _ = a.onPoints x1 * (b.onPoints y1 * a.onPoints x2) *
                b.onPoints y2 := by rw [hcomm x2 y1]
          _ = (a.onPoints x1 * b.onPoints y1) *
                (a.onPoints x2 * b.onPoints y2) := by group }
  let e : Morphism (Variety.prod G H) (Variety.prod G H) :=
    Morphism.prod
      (eG.comp (Morphism.fst G H))
      (eH.comp (Morphism.snd G H))
  have he : IsIsogeny e := isogeny_prod eG eH heG heH
  have hcomp : phi.comp s = e := by
    apply Morphism.ext
    funext z
    obtain ⟨⟨x, y⟩, rfl⟩ :=
      (Variety.prodPointEquiv G H).symm.surjective z
    change phi.onPoints (a.onPoints x * b.onPoints y) =
      (Variety.prodPointEquiv G H).symm
        (eG.onPoints x, eH.onPoints y)
    rw [map_mul, ha, hb]
    exact product_inl_mul_inr (eG.onPoints x) (eH.onPoints y)
  have hphis : IsIsogeny (phi.comp s) := by
    rw [hcomp]
    exact he
  exact ⟨s, isogeny_of_comp s phi
    (variety_prod_isConnected hG.1.1 hH.1.1) hCconnected hphi hphis⟩

private theorem adjointVersion_center_eq_bot
    {G : Variety k} [AlgebraicGroup G] (hG : IsAdjointVersion G) :
    Subgroup.center (Variety.Point G) = ⊥ := by
  let Z : ClosedSubgroup G := (ClosedSubgroup.top (G := G)).centralizer
  have hZ : Z.toSubgroup = Subgroup.center (Variety.Point G) := by
    change Subgroup.centralizer
      ((ClosedSubgroup.top (G := G)).toSubgroup : Set (Variety.Point G)) = _
    rw [show (ClosedSubgroup.top (G := G)).toSubgroup = ⊤ by rfl,
      Subgroup.coe_top, Subgroup.centralizer_univ]
  have hZnormal : Z.toSubgroup.Normal := by
    rw [hZ]
    infer_instance
  obtain ⟨Q, _, q, hqsurj, hqker, _⟩ := theorem_1_1_2_b Z hZnormal
  letI : Finite (Subgroup.center (Variety.Point G)) :=
    connectedSemisimple_center_finite hG.1
  have hqfinite : Finite q.kernel := by
    rw [hqker, hZ]
    infer_instance
  have hqinjective : Function.Injective q.onPoints :=
    hG.2 q ⟨hqsurj, hqfinite⟩
  have hqbot : q.kernel = ⊥ :=
    (MonoidHom.ker_eq_bot_iff q.onPoints).mpr hqinjective
  calc
    Subgroup.center (Variety.Point G) = Z.toSubgroup := hZ.symm
    _ = q.kernel := hqker.symm
    _ = ⊥ := hqbot

omit [IsAlgClosed k] in
private theorem center_product_eq_bot
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : Subgroup.center (Variety.Point G) = ⊥)
    (hH : Subgroup.center (Variety.Point H) = ⊥) :
    Subgroup.center (Variety.Point (Variety.prod G H)) = ⊥ := by
  apply le_antisymm
  · intro z hz
    apply Subgroup.mem_bot.mpr
    let pG := Morphism.fst G H
    let pH := Morphism.snd G H
    have hpGcenter : pG.onPoints z ∈ Subgroup.center (Variety.Point G) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hzcomm := Subgroup.mem_center_iff.mp hz
        ((Morphism.inl G H).onPoints x)
      have := congrArg pG.onPoints hzcomm
      simpa only [map_mul, pG, product_fst_inl G H] using this
    have hpHcenter : pH.onPoints z ∈ Subgroup.center (Variety.Point H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hzcomm := Subgroup.mem_center_iff.mp hz
        ((Morphism.inr G H).onPoints y)
      have := congrArg pH.onPoints hzcomm
      simpa only [map_mul, pH, product_snd_inr G H] using this
    have hpGz : pG.onPoints z = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hG]
      exact hpGcenter
    have hpHz : pH.onPoints z = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hH]
      exact hpHcenter
    apply (Variety.prodPointEquiv G H).injective
    exact Prod.ext hpGz hpHz
  · exact bot_le

private theorem adjointVersion_product
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : IsAdjointVersion G) (hH : IsAdjointVersion H) :
    IsAdjointVersion (Variety.prod G H) := by
  have hsemisimple := semisimple_product hG.1 hH.1
  refine ⟨hsemisimple, ?_⟩
  intro Q _ phi hphi
  have hcenter :
      Subgroup.center (Variety.Point (Variety.prod G H)) = ⊥ :=
    center_product_eq_bot
      (adjointVersion_center_eq_bot hG)
      (adjointVersion_center_eq_bot hH)
  have hkernel : phi.kernel = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subgroup.mem_bot.mp
      rw [← hcenter]
      exact isogeny_kernel_le_center_of_connected phi hphi hsemisimple.1 x hx
    · exact bot_le
  exact (MonoidHom.ker_eq_bot_iff phi.onPoints).mp hkernel

public theorem extremeVersion_product
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H] :
    (IsUniversalVersion G → IsUniversalVersion H →
      IsUniversalVersion (Variety.prod G H)) ∧
    (IsAdjointVersion G → IsAdjointVersion H →
      IsAdjointVersion (Variety.prod G H)) :=
  ⟨universalVersion_product, adjointVersion_product⟩

end Theory.AlgebraicGroup
