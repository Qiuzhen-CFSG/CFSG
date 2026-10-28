module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.FixedPoints
public import Theory.AlgebraicGroup.Unipotent.SolvableTorusDecomposition
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
# Algebraic blocks over projected root rays

For a map sending each absolute root to its projected vector, `rayPreimage`
is the full inverse image of a positive ray. Its root-generated subgroup is
closed and connected, and is unipotent whenever the roots lie in a supplied
unipotent subgroup. Root transport induces transport of these blocks; scalar
changes of the projected vectors by positive factors preserve each block.
No abelianness, reducedness, or crystallographic condition is imposed on the
projected vectors.

Independently, the actual Borel and its unipotent radical supply the relative
normality and torus decomposition needed by the finite Sylow consumer. An
endomorphism preserving the Borel preserves its radical, by taking the closed
unipotent image and using maximality in the connected solvable Borel.

The final escape reduction uses a nonidentity fixed block element, transports
it into a subgroup disjoint from the positive group, and places it in the
literal prime-to-p residual. It uses neither finite Bruhat coverage nor Sylow
maximality. Construction of the projected vectors from the Steinberg setup,
the nonidentity fixed elements, and the ordered block and commutator formulas
remain separate obligations; the conditional results here do not assert the
complete source theorems from the sigma-setup alone.

Sources: GLS3, 2.3.1, 2.3.6--2.3.8 and Table 2.4; 1.9.5 and 1.12.7.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.FiniteBruhatSylow

open FiniteParabolicRealization

variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

section Borel

variable [IsAlgClosed k] {B U T : ClosedSubgroup K}

omit [IsAlgClosed k] in
/-- Relative normality is inside the specified Borel. -/
theorem borel_radical_normal (hU : IsUnipotentRadicalOf B U) :
    (U.toSubgroup.subgroupOf B.toSubgroup).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (Subgroup.le_normalizer_iff.mpr hU.2.2.1)

/-- An endomorphism preserving a Borel also preserves its actual radical. -/
theorem borel_radical_invariant (σ : AlgebraicEndomorphism K)
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hσB : ∀ b ∈ B.toSubgroup, σ.onPoints b ∈ B.toSubgroup) :
    ∀ u ∈ U.toSubgroup, σ.onPoints u ∈ U.toSubgroup := by
  let f := σ.comp U.inclusion
  have himageB : f.imageClosedSubgroup ≤ B := by
    rintro x ⟨u, rfl⟩
    exact hσB _ (hU.1 (U.pointEquiv u).property)
  have himageU : IsUnipotentAlgebraicGroup f.imageClosedSubgroup.carrierVariety := by
    let q := f.codRestrictClosedSubgroup f.imageClosedSubgroup (fun x => ⟨x, rfl⟩)
    exact hU.2.1.of_surjective q
      (f.codRestrictImageClosedSubgroup_surjective (fun x => ⟨x, rfl⟩))
  have hle := hU.contains_unipotent_closedSubgroup hB.connected hB.solvable
    himageB himageU
  intro u hu
  apply hle
  exact ⟨U.pointEquiv.symm ⟨u, hu⟩,
    congrArg σ.onPoints (congrArg Subtype.val (U.pointEquiv.apply_symm_apply _))⟩

/-- The decomposition input is a consequence of the source Borel hypotheses. -/
theorem borel_torus_radical_decomposition
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hT : IsMaximalTorus T) (hTB : T ≤ B) :
    ∀ b ∈ B.toSubgroup, ∃ t ∈ T.toSubgroup, ∃ u ∈ U.toSubgroup,
      b = t * u := by
  intro b hb
  obtain ⟨t, u, ht, hu, htu⟩ :=
    (maximalTorus_unipotentRadical_decomposition_of_connected_solvable
      hB.connected hB.solvable hU hT hTB).1 b hb
  exact ⟨t, ht, u, hu, htu⟩

/-- Actual invariant Borel data discharge the algebraic decomposition inputs
of the finite-parabolic consumer. Coverage and root escape remain explicit. -/
theorem finiteParabolic_contains_sylow_of_borel_root_escape
    (σ : AlgebraicEndomorphism K) (p : ℕ) [Fact p.Prime] [CharP k p]
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hσB : ∀ b ∈ B.toSubgroup, σ.onPoints b ∈ B.toSubgroup)
    (hσT : ∀ t ∈ T.toSubgroup, σ.onPoints t ∈ T.toSubgroup)
    (hcover : ∀ g : definingGroup σ p, ∃ u ∈ positive σ p U,
      ∃ n ∈ normalizer σ p T, ∃ v ∈ positive σ p U, g = u * n * v)
    (hescape : ∀ n ∈ normalizer σ p T, n ∉ borel σ p B →
      ∃ u ∈ positive σ p U, n * u * n⁻¹ ∉ positive σ p U)
    {P : Subgroup (definingGroup σ p)} (hP : IsFiniteParabolic σ p B P) :
    ∃ S : Sylow p (definingGroup σ p), (S : Subgroup _) ≤ P :=
  finiteParabolic_contains_sylow_of_root_factorization σ p B U T
    hU.1 hTB hU.2.1 hT.1 (borel_radical_normal hU)
    (borel_radical_invariant σ hB hU hσB) hσT
    (borel_torus_radical_decomposition hB hU hT hTB) hcover hescape hP

end Borel

section Rays

variable {R V A : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- All absolute roots whose projected vectors lie on the ray of `α`.
In the source application `v` is orthogonal projection onto the fixed space
of the standard-position isometry. It is not an orbit quotient. -/
def rayPreimage (v : A → V) (α : A) : Set A :=
  {β | ∃ c : R, 0 < c ∧ v β = c • v α}

theorem mem_rayPreimage_self (v : A → V) (α : A) : α ∈ rayPreimage (R := R) v α :=
  ⟨1, zero_lt_one, (one_smul R (v α)).symm⟩

/-- Positive rescaling of a projected vector preserves its full ray fiber. -/
theorem rayPreimage_eq_of_mem (v : A → V) {α β : A}
    (hβ : β ∈ rayPreimage (R := R) v α) : rayPreimage (R := R) v β = rayPreimage (R := R) v α := by
  obtain ⟨c, hc, hβ⟩ := hβ
  ext γ
  constructor
  · rintro ⟨d, hd, hγ⟩
    exact ⟨d * c, mul_pos hd hc, by rw [hγ, hβ, mul_smul]⟩
  · rintro ⟨d, hd, hγ⟩
    refine ⟨d / c, div_pos hd hc, ?_⟩
    rw [hβ, smul_smul, div_mul_cancel₀ d hc.ne', hγ]

/-- The projected-ray condition is stable under any positive rescaling
permutation, including the unequal-root-length Suzuki--Ree action. -/
theorem rayPreimage_mapsTo_of_pos_smul (v : A → V) (ρ : A → A)
    (hρ : ∀ β, ∃ c : R, 0 < c ∧ v (ρ β) = c • v β) (α : A) :
    Set.MapsTo ρ (rayPreimage (R := R) v α) (rayPreimage (R := R) v α) := by
  rintro β ⟨c, hc, hβ⟩
  obtain ⟨d, hd, hρβ⟩ := hρ β
  exact ⟨d * c, mul_pos hd hc, by rw [hρβ, hβ, mul_smul]⟩

omit [IsStrictOrderedRing R] in
/-- Linear transport acts on entire ray fibers. -/
theorem rayPreimage_transport (v : A → V) (w : Equiv.Perm A)
    (L : V ≃ₗ[R] V) (hw : ∀ β, v (w β) = L (v β)) (α β : A) :
    w β ∈ rayPreimage (R := R) v (w α) ↔ β ∈ rayPreimage (R := R) v α := by
  constructor
  · rintro ⟨c, hc, heq⟩
    refine ⟨c, hc, L.injective ?_⟩
    simpa only [hw, map_smul] using heq
  · rintro ⟨c, hc, heq⟩
    exact ⟨c, hc, by rw [hw, hw, heq, map_smul]⟩

/-- The full ray preimage is closed under every root addition respected by
the projection, including when distinct absolute-root orbits share a ray. -/
theorem rayPreimage_add_closed (v : A → V) (add : A → A → Option A)
    (hadd : ∀ a b c, add a b = some c → v c = v a + v b) (α : A) :
    ∀ a ∈ rayPreimage (R := R) v α, ∀ b ∈ rayPreimage (R := R) v α,
      ∀ c, add a b = some c → c ∈ rayPreimage (R := R) v α := by
  rintro a ⟨s, hs, ha⟩ b ⟨t, ht, hb⟩ c hc
  exact ⟨s + t, add_pos hs ht, by rw [hadd a b c hc, ha, hb, add_smul]⟩

/-- Support of the source commutator formula, using strictly positive real
coefficients rather than a crystallographic relative-root hypothesis. -/
def projectedConePreimage (v : A → V) (α β : A) : Set A :=
  {γ | ∃ s t : R, 0 < s ∧ 0 < t ∧ v γ = s • v α + t • v β}

end Rays

section Blocks

variable [IsAlgClosed k] {T : ClosedSubgroup K} (D : RootGroupData K T)

private theorem root_family_connected (hD : D.IsRealization) (a : D.Root) :
    _root_.IsConnected (D.rootSubgroup a : Set (Variety.Point K)) := by
  have hconn := (hD.2.2.1 a).1.2.isConnected
  let : ConnectedSpace (Variety.Point (D.rootSubgroup a).carrierVariety) :=
    connectedSpace_iff_univ.mpr hconn
  change _root_.IsConnected ((D.rootSubgroup a).toSubgroup : Set (Variety.Point K))
  rw [← (D.rootSubgroup a).range_inclusion]
  exact isConnected_range (D.rootSubgroup a).inclusion.toVariety.continuous

private theorem root_generated_closed (hD : D.IsRealization) (s : Set D.Root) :
    IsZariskiClosed K (RootSubgroupGenerated D s : Set (Variety.Point K)) := by
  have h := closure_iUnion_connected_closedSubgroup_isZariskiClosed
    (fun a : s => D.rootSubgroup a.1) (fun a => root_family_connected D hD a.1)
  rw [RootSubgroupGenerated]
  rwa [Set.iUnion_subtype] at h

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- The actual closed subgroup generated by the full projected-ray preimage.
Its ordered-product identification is an additional theorem. -/
noncomputable def rootRayBlock (hD : D.IsRealization) (v : D.Root → V)
    (α : D.Root) : ClosedSubgroup K :=
  ClosedSubgroup.ofSubgroup (RootSubgroupGenerated D (rayPreimage (R := R) v α))
    (by exact root_generated_closed D hD (rayPreimage (R := R) v α))

omit [IsStrictOrderedRing R] in
@[simp] theorem rootRayBlock_toSubgroup (hD : D.IsRealization)
    (v : D.Root → V) (α : D.Root) :
    (rootRayBlock (R := R) D hD v α).toSubgroup =
      RootSubgroupGenerated D (rayPreimage (R := R) v α) := rfl

omit [IsStrictOrderedRing R] in
theorem rootRayBlock_connected (hD : D.IsRealization)
    (v : D.Root → V) (α : D.Root) :
    _root_.IsConnected (rootRayBlock (R := R) D hD v α : Set (Variety.Point K)) := by
  have h := closure_iUnion_connected_closedSubgroup_isConnected
    (fun a : rayPreimage (R := R) v α => D.rootSubgroup a.1)
    (fun a => root_family_connected D hD a.1)
  change _root_.IsConnected
    (Subgroup.closure (⋃ a ∈ rayPreimage (R := R) v α,
      (D.rootSubgroup a : Set (Variety.Point K))) : Set (Variety.Point K))
  rwa [Set.iUnion_subtype] at h

theorem rootRayBlock_eq_of_mem (hD : D.IsRealization) (v : D.Root → V)
    {α β : D.Root} (hβ : β ∈ rayPreimage (R := R) v α) :
    rootRayBlock (R := R) D hD v β = rootRayBlock (R := R) D hD v α := by
  apply SetLike.coe_injective
  change (RootSubgroupGenerated D (rayPreimage (R := R) v β) : Set (Variety.Point K)) = _
  rw [rayPreimage_eq_of_mem v hβ]
  rfl

/-- Every algebraic ray block contains an actual nontrivial root group.
This does not by itself establish nontriviality of its fixed subgroup. -/
theorem rootRayBlock_ne_bot (hD : D.IsRealization) (v : D.Root → V)
    (α : D.Root) : (rootRayBlock (R := R) D hD v α).toSubgroup ≠ ⊥ := by
  intro hbot
  apply (hD.2.2.1 α).1.invariant_unipotent_ne_bot.2.2
  apply le_bot_iff.mp
  rw [← hbot]
  exact rootSubgroup_le_RootSubgroupGenerated D (mem_rayPreimage_self v α)

omit [IsStrictOrderedRing R] in
theorem rootRayBlock_le (hD : D.IsRealization) (v : D.Root → V)
    (α : D.Root) (U : ClosedSubgroup K)
    (hroots : ∀ β ∈ rayPreimage (R := R) v α, D.rootSubgroup β ≤ U) :
    rootRayBlock (R := R) D hD v α ≤ U :=
  RootSubgroupGenerated_le_of_rootSubgroup_le D _ _ hroots

omit [IsStrictOrderedRing R] in
/-- Positive blocks inherit unipotence from the actual Borel radical. -/
theorem rootRayBlock_unipotent (hD : D.IsRealization) (v : D.Root → V)
    (α : D.Root) (U : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hroots : ∀ β ∈ rayPreimage (R := R) v α, D.rootSubgroup β ≤ U) :
    IsUnipotentAlgebraicGroup (rootRayBlock (R := R) D hD v α).carrierVariety := by
  let Y := rootRayBlock (R := R) D hD v α
  have hYU : Y ≤ U := rootRayBlock_le D hD v α U hroots
  intro y
  have hyY : Y.includePoint y ∈ Y := (Y.pointEquiv y).property
  have hyU := hYU hyY
  have hy := (closedSubgroup_unipotentElement_iff U hyU).mpr
    (hU (U.pointEquiv.symm ⟨Y.includePoint y, hyU⟩))
  have h := (closedSubgroup_unipotentElement_iff Y hyY).mp hy
  have heq : Y.pointEquiv.symm ⟨Y.includePoint y, hyY⟩ = y := by
    apply Y.pointEquiv.injective
    apply Subtype.ext
    exact congrArg Subtype.val (Y.pointEquiv.apply_symm_apply _)
  rwa [heq] at h

omit [IsAlgClosed k] in
private theorem root_generated_map_le (f : Variety.Point K →* Variety.Point K)
    (s t : Set D.Root) (ρ : D.Root → D.Root) (hs : Set.MapsTo ρ s t)
    (hρ : ∀ a ∈ s, ∀ x ∈ (D.rootSubgroup a).toSubgroup,
      f x ∈ (D.rootSubgroup (ρ a)).toSubgroup) :
    (RootSubgroupGenerated D s).map f ≤ RootSubgroupGenerated D t := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply RootSubgroupGenerated_le_of_rootSubgroup_le
  intro a ha x hx
  exact rootSubgroup_le_RootSubgroupGenerated D (hs ha) (hρ a ha x hx)

/-- Absolute-root transport preserving projected rays gives block invariance. -/
theorem rootRayBlock_invariant (hD : D.IsRealization) (v : D.Root → V)
    (σ : AlgebraicEndomorphism K) (ρ : D.Root → D.Root)
    (hρ : ∀ β, ∃ c : R, 0 < c ∧ v (ρ β) = c • v β)
    (hσ : ∀ β x, x ∈ (D.rootSubgroup β).toSubgroup →
      σ.onPoints x ∈ (D.rootSubgroup (ρ β)).toSubgroup) (α : D.Root) :
    ∀ x ∈ (rootRayBlock (R := R) D hD v α).toSubgroup,
      σ.onPoints x ∈ (rootRayBlock (R := R) D hD v α).toSubgroup := by
  intro x hx
  exact root_generated_map_le D σ.onPoints _ _ ρ
    (rayPreimage_mapsTo_of_pos_smul v ρ hρ α)
    (fun a _ y hy => hσ a y hy) ⟨x, hx, rfl⟩

omit [IsStrictOrderedRing R] in
/-- The full algebraic torus normalizes every projected-root block. -/
theorem torus_normalizes_rootRayBlock (hD : D.IsRealization)
    (v : D.Root → V) (α : D.Root) :
    T.toSubgroup ≤ Subgroup.normalizer
      ((rootRayBlock (R := R) D hD v α).toSubgroup : Set (Variety.Point K)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro t ht x hx
  apply root_generated_map_le D (MulAut.conj t).toMonoidHom
    (rayPreimage (R := R) v α) (rayPreimage (R := R) v α) id (fun _ h => h) ?_ ⟨x, hx, rfl⟩
  intro a _ y hy
  have h := (hD.2.2.1 a).1.1 t⁻¹ (T.inv_mem ht) y hy
  change t * y * t⁻¹ ∈ (D.rootSubgroup a).toSubgroup
  change (t⁻¹)⁻¹ * y * t⁻¹ ∈ (D.rootSubgroup a).toSubgroup at h
  rwa [inv_inv] at h

omit [IsStrictOrderedRing R] in
/-- Conjugation on actual absolute root groups induces conjugation on the
closed blocks of entire projected rays. The action convention is `n*x*n⁻¹`. -/
theorem rootRayBlock_map_conj (hD : D.IsRealization) (v : D.Root → V)
    (n : Variety.Point K) (w : Equiv.Perm D.Root) (L : V ≃ₗ[R] V)
    (hw : ∀ β, v (w β) = L (v β))
    (hconj : ∀ β, (D.rootSubgroup β).toSubgroup.map (MulAut.conj n).toMonoidHom =
      (D.rootSubgroup (w β)).toSubgroup) (α : D.Root) :
    (rootRayBlock (R := R) D hD v α).toSubgroup.map (MulAut.conj n).toMonoidHom =
      (rootRayBlock (R := R) D hD v (w α)).toSubgroup := by
  apply le_antisymm
  · apply root_generated_map_le D (MulAut.conj n).toMonoidHom _ _ w
    · intro β hβ
      exact (rayPreimage_transport v w L hw α β).mpr hβ
    · intro β _ x hx
      rw [← hconj β]
      exact ⟨x, hx, rfl⟩
  · apply RootSubgroupGenerated_le_of_rootSubgroup_le
    intro β hβ
    have hβ' : w.symm β ∈ rayPreimage (R := R) v α :=
      (rayPreimage_transport v w L hw α (w.symm β)).mp (by simpa using hβ)
    have hle := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom)
      (rootSubgroup_le_RootSubgroupGenerated D hβ')
    rw [hconj] at hle
    simpa using hle

end Blocks

section OrderedDescent

variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p]
  {T : ClosedSubgroup K} (D : RootGroupData K T)
  {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- Ordered algebraic ray products descend without making any block abelian.
This applies the fixed-coordinate theorem to the literal closed ray blocks;
only the algebraic ordered-product theorem remains an explicit premise. -/
theorem existsUnique_restricted_rootRay_factors
    (hD : D.IsRealization) (v : D.Root → V) {m : ℕ} (a : Fin m → D.Root)
    (U : ClosedSubgroup K) (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hroots : ∀ i β, β ∈ rayPreimage (R := R) v (a i) → D.rootSubgroup β ≤ U)
    (ρ : D.Root → D.Root)
    (hρ : ∀ β, ∃ c : R, 0 < c ∧ v (ρ β) = c • v β)
    (hσ : ∀ β x, x ∈ (D.rootSubgroup β).toSubgroup →
      σ.onPoints x ∈ (D.rootSubgroup (ρ β)).toSubgroup)
    (hinj : Function.Injective (Subgroup.orderedProduct
      (fun i => (rootRayBlock (R := R) D hD v (a i)).toSubgroup)))
    (hprod : ∀ x ∈ U.toSubgroup,
      ∃ b : ∀ i, (rootRayBlock (R := R) D hD v (a i)).toSubgroup,
        Subgroup.orderedProduct (fun i => (rootRayBlock (R := R) D hD v (a i)).toSubgroup) b = x)
    (x : positive σ p U) :
    ∃! b : ∀ i, restrict σ p (rootRayBlock (R := R) D hD v (a i)).toSubgroup,
      Subgroup.orderedProduct
        (fun i => restrict σ p (rootRayBlock (R := R) D hD v (a i)).toSubgroup) b = x.val :=
  existsUnique_restricted_ordered_factors σ p
    (fun i => rootRayBlock (R := R) D hD v (a i))
    (fun i => rootRayBlock_unipotent D hD v (a i) U hU (hroots i))
    (fun i => rootRayBlock_invariant D hD v σ ρ hρ hσ (a i))
    hinj x.val (hprod _ x.property)

end OrderedDescent

section Escape

variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p]

/-- A fixed block element transported into a subgroup disjoint from the
positive radical gives escape in the actual source residual. -/
theorem positive_escape_of_fixed_block
    (U Y : ClosedSubgroup K) (Z : Subgroup (Variety.Point K))
    (hY : IsUnipotentAlgebraicGroup Y.carrierVariety) (hYU : Y ≤ U)
    (hZU : Disjoint Z U.toSubgroup) (n : definingGroup σ p)
    (htransport : Y.toSubgroup.map
      (MulAut.conj (pointEmbedding σ p n)).toMonoidHom ≤ Z)
    (hfixed : ∃ x ∈ Y.toSubgroup, σ.onPoints x = x ∧ x ≠ 1) :
    ∃ u ∈ positive σ p U, n * u * n⁻¹ ∉ positive σ p U := by
  obtain ⟨x, hxY, hfix, hx1⟩ := hfixed
  let u : definingGroup σ p :=
    ⟨⟨x, hfix⟩, fixed_unipotent_le_definingGroup σ p Y hY hxY⟩
  refine ⟨u, hYU hxY, ?_⟩
  intro hmem
  have hz : pointEmbedding σ p (n * u * n⁻¹) ∈ Z := by
    change pointEmbedding σ p n * x * (pointEmbedding σ p n)⁻¹ ∈ Z
    exact htransport ⟨x, hxY, rfl⟩
  have hone : pointEmbedding σ p (n * u * n⁻¹) = 1 :=
    disjoint_iff_inf_le.mp hZU ⟨hz, hmem⟩
  have hu : n * u * n⁻¹ = 1 :=
    pointEmbedding_injective σ p (hone.trans (map_one (pointEmbedding σ p)).symm)
  have hu1 : u = 1 := (MulAut.conj n).injective (by simpa using hu)
  exact hx1 (congrArg (pointEmbedding σ p) hu1)

/-- The actual Borel consumer, with the local escape premise replaced by
root-block transport, nonidentity fixed elements, and geometric separation.
The coverage premise belongs to the independent finite Tits-system argument. -/
theorem finiteParabolic_contains_sylow_of_fixed_blocks
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    {B U T : ClosedSubgroup K}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hσB : ∀ b ∈ B.toSubgroup, σ.onPoints b ∈ B.toSubgroup)
    (hσT : ∀ t ∈ T.toSubgroup, σ.onPoints t ∈ T.toSubgroup)
    (hcover : ∀ g : definingGroup σ p, ∃ u ∈ positive σ p U,
      ∃ n ∈ normalizer σ p T, ∃ v ∈ positive σ p U, g = u * n * v)
    {A : Type*} (Y : A → ClosedSubgroup K)
    (hY : ∀ a, IsUnipotentAlgebraicGroup (Y a).carrierVariety)
    (hfixed : ∀ a, ∃ x ∈ (Y a).toSubgroup, σ.onPoints x = x ∧ x ≠ 1)
    (hinversion : ∀ n ∈ normalizer σ p T, n ∉ borel σ p B →
      ∃ a b, Y a ≤ U ∧ Disjoint (Y b).toSubgroup U.toSubgroup ∧
        (Y a).toSubgroup.map (MulAut.conj (pointEmbedding σ p n)).toMonoidHom =
          (Y b).toSubgroup)
    {P : Subgroup (definingGroup σ p)} (hP : IsFiniteParabolic σ p B P) :
    ∃ S : Sylow p (definingGroup σ p), (S : Subgroup _) ≤ P := by
  apply finiteParabolic_contains_sylow_of_borel_root_escape σ p hB hU hT hTB
    hσB hσT hcover ?_ hP
  intro n hn hnB
  obtain ⟨a, b, ha, hb, hab⟩ := hinversion n hn hnB
  exact positive_escape_of_fixed_block σ p U (Y a) (Y b).toSubgroup
    (hY a) ha hb n hab.le (hfixed a)

end Escape

end Theory.AlgebraicGroup.FiniteBruhatSylow

end
