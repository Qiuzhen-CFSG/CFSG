module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.PluckerOrbit.Eigenvalue
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Semisimple.Defs

universe u v

/-!
GLS3, Chapter 1, Proposition 1.10.3.

For an isogeny with connected source, the kernel is central and the source
center maps onto the target center.  The final theorem packages that image
equality as a surjective homomorphism after identifying the source center with
an arbitrary group.  This is the reusable transfer used by the center table in
GLS3, Theorem 1.12.5(d).
-/

namespace Theory.AlgebraicGroup

section

open scoped commutatorElement

variable {k : Type u} [Field k]

private lemma connected_finite_range_subsingleton
    {K H : Variety k} (f : Variety.Morphism K H)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (hfinite : (Set.range f.toFun).Finite) :
    (Set.range f.toFun).Subsingleton := by
  have hrangeConnected : _root_.IsConnected (Set.range f.toFun) := by
    simpa only [Set.image_univ] using
      hK.image f.toFun f.continuous.continuousOn
  let : T1Space (Variety.Point H) :=
    ⟨fun y => Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton H y)⟩
  rw [← Set.not_nontrivial_iff]
  intro hnontrivial
  exact hfinite.not_infinite
    (hrangeConnected.isPreconnected.infinite_of_nontrivial hnontrivial)

/-- Proposition 1.10.3(a): the kernel of an isogeny from a connected
algebraic group is central. -/
public theorem isogeny_kernel_le_center_of_connected
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K))) :
    ∀ x, x ∈ φ.kernel → x ∈ Subgroup.center (Variety.Point K) := by
  let : Finite φ.kernel := hφ.2
  intro x hx
  let c : Variety.Morphism K K := AlgebraicGroup.conjugateMorphism K x
  have hcrange : Set.range c.toFun ⊆ (φ.kernel : Set (Variety.Point K)) := by
    rintro y ⟨z, rfl⟩
    rw [AlgebraicGroup.conjugateMorphism_apply]
    change φ.onPoints (z * x * z⁻¹) = 1
    rw [map_mul, map_mul, map_inv, (show φ.onPoints x = 1 from hx)]
    simp
  have hcfinite : (Set.range c.toFun).Finite :=
    (Set.toFinite (φ.kernel : Set (Variety.Point K))).subset hcrange
  have hcsub := connected_finite_range_subsingleton c hK hcfinite
  rw [Subgroup.mem_center_iff]
  intro z
  have heq := hcsub (Set.mem_range_self z)
    (Set.mem_range_self (1 : Variety.Point K))
  rw [AlgebraicGroup.conjugateMorphism_apply,
    AlgebraicGroup.conjugateMorphism_apply] at heq
  simp only [one_mul, inv_one, mul_one] at heq
  calc
    z * x = (z * x * z⁻¹) * z := by group
    _ = x * z := congrArg (fun w => w * z) heq

/-- Proposition 1.10.3(b): an isogeny between connected algebraic groups maps
the source center onto the target center. -/
public theorem isogeny_image_center_eq_center_of_connected
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K))) :
    φ.onPoints '' (Subgroup.center (Variety.Point K) : Set (Variety.Point K)) =
      (Subgroup.center (Variety.Point H) : Set (Variety.Point H)) := by
  let : Finite φ.kernel := hφ.2
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    change x ∈ Subgroup.center (Variety.Point K) at hx
    change φ.onPoints x ∈ Subgroup.center (Variety.Point H)
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro z
    obtain ⟨w, rfl⟩ := hφ.1 z
    rw [← map_mul, hx, map_mul]
  · intro y hy
    obtain ⟨x, rfl⟩ := hφ.1 y
    refine ⟨x, ?_, rfl⟩
    change x ∈ Subgroup.center (Variety.Point K)
    change φ.onPoints x ∈ Subgroup.center (Variety.Point H) at hy
    let c : Variety.Morphism K K :=
      (AlgebraicGroup.rightMulMorphism K x⁻¹).comp
        (AlgebraicGroup.conjugateMorphism K x)
    have hcapply (z : Variety.Point K) :
        c.toFun z = z * x * z⁻¹ * x⁻¹ := by
      simp [c, Variety.Morphism.comp,
        AlgebraicGroup.rightMulMorphism_apply,
        AlgebraicGroup.conjugateMorphism_apply]
    have hcrange : Set.range c.toFun ⊆
        (φ.kernel : Set (Variety.Point K)) := by
      rintro w ⟨z, rfl⟩
      rw [hcapply]
      change φ.onPoints (z * x * z⁻¹ * x⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have hcenter := Subgroup.mem_center_iff.mp hy (φ.onPoints z)
      rw [hcenter]
      simp
    have hcfinite : (Set.range c.toFun).Finite :=
      (Set.toFinite (φ.kernel : Set (Variety.Point K))).subset hcrange
    have hcsub := connected_finite_range_subsingleton c hK hcfinite
    rw [Subgroup.mem_center_iff]
    intro z
    have heq := hcsub (Set.mem_range_self z)
      (Set.mem_range_self (1 : Variety.Point K))
    rw [hcapply, hcapply] at heq
    simp only [one_mul, inv_one, mul_one, mul_inv_cancel] at heq
    exact commutatorElement_eq_one_iff_mul_comm.mp (by
      simpa [commutatorElement_def] using heq)

/-- If the center of the connected source of an isogeny is identified with a
group `A`, then the target center is a homomorphic image of `A`.

This is the homomorphism-level form of
`isogeny_image_center_eq_center_of_connected`: restrict the point map to the
source and target centers, then compose it with the supplied equivalence. -/
public theorem center_homomorphic_image_of_isogeny
    {A : Type v} [Group A]
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (sourceCenterEquiv : A ≃* Subgroup.center (Variety.Point K)) :
    ∃ f : A →* Subgroup.center (Variety.Point H),
      Function.Surjective f := by
  let centerMap : Subgroup.center (Variety.Point K) →*
      Subgroup.center (Variety.Point H) :=
    { toFun := fun z => ⟨φ.onPoints z, by
          apply Subgroup.mem_center_iff.mpr
          intro y
          obtain ⟨x, rfl⟩ := hφ.1 y
          rw [← φ.onPoints.map_mul, ← φ.onPoints.map_mul,
            Subgroup.mem_center_iff.mp z.property x]⟩
      map_one' := by
        apply Subtype.ext
        exact φ.onPoints.map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact φ.onPoints.map_mul x y }
  let f : A →* Subgroup.center (Variety.Point H) :=
    centerMap.comp sourceCenterEquiv.toMonoidHom
  refine ⟨f, ?_⟩
  intro z
  have hz : (z : Variety.Point H) ∈
      (Subgroup.center (Variety.Point H) : Set (Variety.Point H)) :=
    z.property
  rw [← isogeny_image_center_eq_center_of_connected φ hφ hK] at hz
  obtain ⟨x, hx, hxeq⟩ := hz
  refine ⟨sourceCenterEquiv.symm ⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  change φ.onPoints
      (sourceCenterEquiv (sourceCenterEquiv.symm ⟨x, hx⟩)) = z
  rw [sourceCenterEquiv.apply_symm_apply]
  exact hxeq

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
set_option maxHeartbeats 800000 in
public theorem centerPluckerConjugationMorphism_kernel_eq
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K) :
    let Z : ClosedSubgroup K := (ClosedSubgroup.top (G := K)).centralizer
    Z.rightTranslateVanishingPluckerConjugationMorphism.kernel =
      Subgroup.center (Variety.Point K) := by
  let Z : ClosedSubgroup K := (ClosedSubgroup.top (G := K)).centralizer
  have hZ : Z.toSubgroup = Subgroup.center (Variety.Point K) := by
    change Subgroup.centralizer
      ((ClosedSubgroup.top (G := K)).toSubgroup : Set (Variety.Point K)) = _
    rw [show (ClosedSubgroup.top (G := K)).toSubgroup = ⊤ by rfl,
      Subgroup.coe_top, Subgroup.centralizer_univ]
  have hZnormal : Z.toSubgroup.Normal := by
    constructor
    intro z hz g
    have hzCenter : z ∈ Subgroup.center (Variety.Point K) := hZ ▸ hz
    have hcomm := Subgroup.mem_center_iff.mp hzCenter g
    rw [hcomm]
    simpa using hz
  exact
    (Z.rightTranslateVanishingPluckerConjugationMorphism_kernel_eq_of_connected
      hK.1 hZnormal).trans hZ

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- An exact pointwise `T · U(P)` decomposition identifies the underlying
subgroup with the supremum of the corresponding root-generated subgroup and
the torus. -/
public theorem closedSubgroup_eq_rootSubgroupGenerated_sup_torus_of_decomposition
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    (D : RootGroupData K T) (P : Set D.Root)
    (hBform : ∀ x, x ∈ B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u) :
    B.toSubgroup = RootSubgroupGenerated D P ⊔ T.toSubgroup := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, u, ht, hu, rfl⟩ := (hBform x).mp hx
    exact (RootSubgroupGenerated D P ⊔ T.toSubgroup).mul_mem
      (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hu)
  · apply sup_le
    · intro u hu
      exact (hBform u).mpr
        ⟨1, u, T.one_mem, hu, (one_mul u).symm⟩
    · intro t ht
      exact (hBform t).mpr
        ⟨t, 1, ht, (RootSubgroupGenerated D P).one_mem, (mul_one t).symm⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A subgroup with a `T · U(P)` decomposition lies in the subgroup generated
by the torus and all root subgroups. -/
public theorem closedSubgroup_le_rootSubgroupGenerated_sup_torus_of_decomposition
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    (D : RootGroupData K T) (P : Set D.Root)
    (hBform : ∀ x, x ∈ B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u) :
    B.toSubgroup ≤ RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup := by
  have hrootMono :
      RootSubgroupGenerated D P ≤ RootSubgroupGenerated D Set.univ := by
    rw [RootSubgroupGenerated, RootSubgroupGenerated]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨α, hα, hx⟩ := hx
    exact ⟨α, Set.mem_univ α, hx⟩
  intro x hx
  obtain ⟨t, u, ht, hu, rfl⟩ := (hBform x).mp hx
  exact (RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup).mul_mem
    (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hrootMono hu))

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def HasActualRootPairingSubsetType
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (roots : Set ι) (K : Variety k) [AlgebraicGroup K] : Prop :=
  ∃ T : ClosedSubgroup K, ∃ D : RootGroupData K T,
    IsMaximalTorus T ∧ D.IsRealization ∧
      ∃ e : D.Root ≃ roots,
        (∀ α β, (D.pairing α β : R) = P.pairing (e α).1 (e β).1) ∧
        (∀ α β, (e (D.reflect α β)).1 =
          P.reflectionPerm (e α).1 (e β).1) ∧
        ∀ α, (e (D.neg α)).1 = P.reflectionPerm (e α).1 (e α).1

public abbrev HasActualRootPairingType
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (K : Variety k) [AlgebraicGroup K] : Prop :=
  HasActualRootPairingSubsetType P Set.univ K

@[expose]
public def IsPairingIrreducible {ι S : Type*} [Zero S]
    (pairing : ι → ι → S) (roots : Set ι) : Prop :=
  roots.Nonempty ∧
    ∀ roots₁ roots₂ : Set ι,
      roots = roots₁ ∪ roots₂ → Disjoint roots₁ roots₂ →
      roots₁.Nonempty → roots₂.Nonempty →
      ∃ α ∈ roots₁, ∃ β ∈ roots₂,
        pairing α β ≠ 0 ∨ pairing β α ≠ 0

end

/-! GLS3, Chapter 1, Definition 1.10.2.

`IsIsogeny` is defined directly in the shared statement infrastructure; this
owner has no theorem-shaped characterization wrapper.
-/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A global algebraic-group isomorphism restricting pointwise to a morphism
induces an isomorphism from a closed subgroup onto its closed image. -/
public theorem isogeny_borel_restriction_iso_of_iso
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (B : ClosedSubgroup K)
    (e : AlgebraicGroup.Iso K H)
    (he : ∀ x, e.hom.onPoints x = φ.onPoints x) :
    let φB := φ.comp B.inclusion
    let imageB := φB.imageClosedSubgroup
    ∃ eB : AlgebraicGroup.Iso B.carrierVariety imageB.carrierVariety,
      ∀ x, imageB.inclusion.onPoints (eB.hom.onPoints x) =
        φ.onPoints (B.inclusion.onPoints x) := by
  dsimp only
  let φB := φ.comp B.inclusion
  let imageB := φB.imageClosedSubgroup
  have hφBmem (x : Variety.Point B.carrierVariety) :
      φB.onPoints x ∈ imageB.toSubgroup := by
    change φB.onPoints x ∈ φB.image
    exact ⟨x, rfl⟩
  let homB : AlgebraicGroup.Morphism B.carrierVariety imageB.carrierVariety :=
    φB.codRestrictClosedSubgroup imageB hφBmem
  have hinvMem (y : Variety.Point imageB.carrierVariety) :
      e.inv.onPoints (imageB.inclusion.onPoints y) ∈ B.toSubgroup := by
    have hy : imageB.inclusion.onPoints y ∈ φB.image :=
      (imageB.pointEquiv y).property
    rcases hy with ⟨x, hx⟩
    let bx : Variety.Point B.carrierVariety := x
    have hxe : imageB.inclusion.onPoints y =
        e.hom.onPoints (B.inclusion.onPoints bx) := by
      rw [← hx]
      exact (he (B.inclusion.onPoints bx)).symm
    rw [hxe, e.hom_inv_id]
    exact (B.pointEquiv bx).property
  let invB : AlgebraicGroup.Morphism imageB.carrierVariety B.carrierVariety :=
    (e.inv.comp imageB.inclusion).codRestrictClosedSubgroup B hinvMem
  let eB : AlgebraicGroup.Iso B.carrierVariety imageB.carrierVariety := by
    refine
      { hom := homB
        inv := invB
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · intro x
      apply B.inclusion_injective
      change e.inv.onPoints
        (imageB.inclusion.onPoints (homB.onPoints x)) = B.inclusion.onPoints x
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      change e.inv.onPoints (φ.onPoints (B.inclusion.onPoints x)) =
        B.inclusion.onPoints x
      rw [← he, e.hom_inv_id]
    · intro y
      apply imageB.inclusion_injective
      change φ.onPoints (B.inclusion.onPoints (invB.onPoints y)) =
        imageB.inclusion.onPoints y
      rw [← he]
      have hinv_apply :
          B.inclusion.onPoints (invB.onPoints y) =
            e.inv.onPoints (imageB.inclusion.onPoints y) := by
        exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
          (e.inv.comp imageB.inclusion) B hinvMem y
      rw [hinv_apply, e.inv_hom_id]
  refine ⟨eB, ?_⟩
  intro x
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  rfl

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- An isogeny becomes an algebraic-group isomorphism once point injectivity
and regular inverse data from pullback surjectivity are available. -/
public theorem isogeny_iso_of_injective_of_pullback_surjective
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hinj : Function.Injective φ.onPoints)
    (hpull : Function.Surjective φ.toVariety.pullbackRingHom) :
    ∃ e : AlgebraicGroup.Iso K H, e.hom = φ := by
  exact algebraicGroupIso_of_bijective_morphism_of_pullback_surjective
    φ ⟨hinj, hφ.1⟩ hpull

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The closed image of a torus-invariant subgroup remains invariant under the
closed image of the torus. -/
public theorem morphism_image_rootSubgroup_invariant
    {K Q : Variety k} [AlgebraicGroup K] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism K Q) (T X : ClosedSubgroup K)
    (hInv : IsClosedSubgroupInvariant T X) :
    IsClosedSubgroupInvariant
      (q.comp T.inclusion).imageClosedSubgroup
      (q.comp X.inclusion).imageClosedSubgroup := by
  intro t ht x hx
  change t⁻¹ * x * t ∈ (q.comp X.inclusion).image
  change t ∈ (q.comp T.inclusion).image at ht
  change x ∈ (q.comp X.inclusion).image at hx
  rcases ht with ⟨s, rfl⟩
  rcases hx with ⟨y, rfl⟩
  let z : Variety.Point X.carrierVariety :=
    X.pointEquiv.symm
      ⟨_, hInv _ (T.pointEquiv s).property _ (X.pointEquiv y).property⟩
  refine ⟨z, ?_⟩
  change q.onPoints (X.inclusion.onPoints z) =
    (q.onPoints (T.inclusion.onPoints s))⁻¹ *
      q.onPoints (X.inclusion.onPoints y) * q.onPoints (T.inclusion.onPoints s)
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- If the torus and all root subgroups generate the ambient group, then the
subgroup generated by all root subgroups is normal. -/
public theorem rootSubgroupGenerated_normal_of_sup_torus_eq_top
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T)
    (hInv : ∀ α, IsClosedSubgroupInvariant T (D.rootSubgroup α))
    (hgen : RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤) :
    (RootSubgroupGenerated D Set.univ).Normal := by
  let N := RootSubgroupGenerated D Set.univ
  have hTnormalizes :
      T.toSubgroup ≤ Subgroup.normalizer (N : Set (Variety.Point K)) := by
    dsimp [N, RootSubgroupGenerated]
    rw [Subgroup.le_normalizer_closure_iff]
    intro t ht x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨α, _, hx⟩ := hx
    have htinv : t⁻¹ ∈ T := T.inv_mem ht
    have hconj := hInv α t⁻¹ htinv x hx
    simp only [inv_inv] at hconj
    change t * x * t⁻¹ ∈ (D.rootSubgroup α).toSubgroup at hconj
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion]
    exact ⟨α, Set.mem_univ α, hconj⟩
  rw [← Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [← hgen]
  exact sup_le Subgroup.le_normalizer hTnormalizes

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A positive system and its negative preimage together generate all root
subgroups. -/
public theorem rootSubgroupGenerated_sup_negPreimage_eq_univ_of_isPositiveSystem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (P : Set D.Root)
    (hP : IsPositiveSystem D P) :
    RootSubgroupGenerated D P ⊔
        RootSubgroupGenerated D (D.neg ⁻¹' P) =
      RootSubgroupGenerated D Set.univ := by
  apply le_antisymm
  · apply sup_le
    · rw [RootSubgroupGenerated, RootSubgroupGenerated]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨α, _, hx⟩ := hx
      exact ⟨α, Set.mem_univ α, hx⟩
    · rw [RootSubgroupGenerated, RootSubgroupGenerated]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨α, _, hx⟩ := hx
      exact ⟨α, Set.mem_univ α, hx⟩
  · rw [RootSubgroupGenerated, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨α, _, hx⟩ := hx
    have hα : α ∈ P ∪ D.neg ⁻¹' P := by
      rw [hP.2.1]
      exact Set.mem_univ α
    rcases hα with hα | hα
    · apply Subgroup.mem_sup_left
      apply Subgroup.subset_closure
      simp only [Set.mem_iUnion]
      exact ⟨α, hα, hx⟩
    · apply Subgroup.mem_sup_right
      apply Subgroup.subset_closure
      simp only [Set.mem_iUnion]
      exact ⟨α, hα, hx⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A root subgroup with nontrivial root weight intersects the ambient center
trivially. -/
public theorem rootSubgroup_inf_center_eq_bot_of_weight_ne_one
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (χ : TorusWeight T) (hX : IsTorusRootSubgroup T X)
    (hEq : RootWeightEquation T X χ) (hχ : χ ≠ 1) :
    X.toSubgroup ⊓ Subgroup.center (Variety.Point K) = ⊥ := by
  apply le_antisymm
  · intro g hg
    apply Subgroup.mem_bot.mpr
    let y : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨g, hg.1⟩
    let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
    let qy : Variety.Point (KPlus k) := x.inv.onPoints y
    let a : k := Multiplicative.toAdd (additiveGroupPointEquiv k qy)
    have hqa : kPlusPoint a = qy := by
      apply (additiveGroupPointEquiv k).injective
      exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k qy)
    have hxa : X.includePoint (x.value a) = g := by
      change (X.pointEquiv (x.hom.onPoints (kPlusPoint a))).val = g
      rw [hqa, x.inv_hom_id]
      exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨g, hg.1⟩)
    have hpointNe : χ.pointCharacter ≠ (1 : TorusWeight T).pointCharacter := by
      intro heq
      exact hχ (TorusCharacter.pointCharacter_injective heq)
    have hexists :
        ∃ s, χ.pointCharacter s ≠ (1 : TorusWeight T).pointCharacter s := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      apply hpointNe
      ext s
      exact hall s
    obtain ⟨s, hs⟩ := hexists
    have hsone : (1 : TorusWeight T).pointCharacter s = 1 := rfl
    rw [hsone] at hs
    have heq := hEq x a s
    have hgcomm := Subgroup.mem_center_iff.mp hg.2 (T.includePoint s)
    have hleft :
        (T.includePoint s)⁻¹ * g * T.includePoint s = g := by
      calc
        (T.includePoint s)⁻¹ * g * T.includePoint s =
            (T.includePoint s)⁻¹ * (g * T.includePoint s) := by rw [mul_assoc]
        _ = (T.includePoint s)⁻¹ * (T.includePoint s * g) := by rw [← hgcomm]
        _ = g := by simp
    rw [hxa, hleft] at heq
    rw [← hxa] at heq
    have hxval : x.value a = x.value (χ.pointCharacter s * a) := by
      apply X.inclusion_injective
      exact heq
    have hkplus : kPlusPoint a = kPlusPoint (χ.pointCharacter s * a) := by
      have h := congrArg x.inv.onPoints hxval
      simpa only [OneParameterParametrization.value, x.hom_inv_id] using h
    have ha : a = χ.pointCharacter s * a :=
      congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) hkplus
    by_cases ha0 : a = 0
    · rw [← hxa, ha0]
      change X.inclusion.onPoints (x.hom.onPoints (kPlusPoint 0)) = 1
      rw [show kPlusPoint 0 = (1 : Variety.Point (KPlus k)) by
        apply (additiveGroupPointEquiv k).injective
        rfl]
      rw [map_one, map_one]
    · have hmul : χ.pointCharacter s * a = 1 * a := by
        simpa using ha.symm
      have hscalar : χ.pointCharacter s = 1 :=
        mul_right_cancel₀ ha0 hmul
      exact (hs hscalar).elim
  · exact bot_le

end

open scoped commutatorElement

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma adjointCenter_kPlusPoint_mul (s t : k) :
    kPlusPoint s * kPlusPoint t = kPlusPoint (s + t) := by
  apply (additiveGroupPointEquiv k).injective
  change Multiplicative.ofAdd (s + t) =
    Multiplicative.ofAdd s * Multiplicative.ofAdd t
  rfl

omit [IsAlgClosed k] in
private lemma kPlusPoint_neg (t : k) :
    (kPlusPoint t)⁻¹ = kPlusPoint (-t) := by
  apply (additiveGroupPointEquiv k).injective
  change (Multiplicative.ofAdd t)⁻¹ = Multiplicative.ofAdd (-t)
  rfl

omit [IsAlgClosed k] in
private lemma OneParameterParametrization.value_add
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (a b : k) :
    x.value (a + b) = x.value a * x.value b := by
  dsimp only [OneParameterParametrization.value]
  rw [← x.hom.onPoints.map_mul, adjointCenter_kPlusPoint_mul]

omit [IsAlgClosed k] in
private lemma OneParameterParametrization.value_neg
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (a : k) :
    (x.value a)⁻¹ = x.value (-a) := by
  dsimp only [OneParameterParametrization.value]
  rw [← x.hom.onPoints.map_inv, kPlusPoint_neg]

omit [IsAlgClosed k] in
/-– A root subgroup with nontrivial weight lies in the derived subgroup. -/
public theorem rootSubgroup_le_commutator_of_weight_ne_one
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (χ : TorusWeight T)
    (hX : IsTorusRootSubgroup T X)
    (hEq : RootWeightEquation T X χ)
    (hχ : χ ≠ 1) :
    X.toSubgroup ≤ _root_.commutator (Variety.Point K) := by
  let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
  have hs : ∃ s : Variety.Point T.carrierVariety, χ.pointCharacter s ≠ 1 := by
    by_contra h
    apply hχ
    apply TorusCharacter.pointCharacter_injective
    ext s
    simp only [not_exists, not_not] at h
    exact h s
  obtain ⟨s, hs⟩ := hs
  intro g hg
  let y : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨g, hg⟩
  let z : Variety.Point (KPlus k) := x.inv.onPoints y
  let t : k := Multiplicative.toAdd (additiveGroupPointEquiv k z)
  have hz : kPlusPoint t = z := by
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd
        (Multiplicative.toAdd (additiveGroupPointEquiv k z)) =
      additiveGroupPointEquiv k z
    exact Multiplicative.ofAdd.apply_symm_apply _
  have hxy : x.value t = y := by
    change x.hom.onPoints (kPlusPoint t) = y
    rw [hz]
    exact x.inv_hom_id y
  have hgy : X.includePoint y = g := by
    change (X.pointEquiv y).1 = g
    dsimp [y]
    rw [X.pointEquiv.apply_symm_apply]
  let c := χ.pointCharacter s
  let a := (c - 1)⁻¹ * t
  have hca : (c - 1) * a = t := by
    dsimp [a]
    rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]
  have hconj := hEq x a s
  have hcomm : ⁅(T.includePoint s)⁻¹, X.includePoint (x.value a)⁆ =
      X.includePoint (x.value t) := by
    rw [commutatorElement_def]
    simp only [inv_inv]
    rw [hconj]
    change X.inclusion.onPoints (x.value _) *
      (X.inclusion.onPoints (x.value a))⁻¹ = _
    rw [← X.inclusion.onPoints.map_inv]
    rw [OneParameterParametrization.value_neg]
    rw [← X.inclusion.onPoints.map_mul]
    rw [← OneParameterParametrization.value_add]
    have hparam : χ.pointCharacter s * a + -a = t := by
      rw [show -a = (-1) * a by ring, ← add_mul]
      dsimp [c] at hca
      simpa [sub_eq_add_neg] using hca
    rw [hparam]
    rfl
  rw [← hgy, ← hxy, ← hcomm]
  exact Subgroup.commutator_mem_commutator (by simp) (by simp)

end

end Theory.AlgebraicGroup
