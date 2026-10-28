module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.RootRays
public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.RootRays.Products.Regroup
public import Theory.AlgebraicGroup.Borel.RootStructure.UnipotentProduct

/-!
# Ordered products of full projected-root fibers

A linear projection makes each positive ray preimage closed under root
addition. The absolute closed-subset collector identifies its generated
subgroup with its root factors in every order. Disjoint ray fibers partition
the positive roots, so concatenating internal orders and separating absolute
coordinates gives a unique ordered product of the blocks. Applying fixed
coordinate descent gives the literal restricted-root factors in the
prime-to-characteristic residual.

These results use a marked Chevalley system as an explicit earlier-source
input. They do not assert its existence from the algebraic-group hypotheses.
The source-existence obligation remains with the assembly task.

Sources: GLS3 1.12.7(a),(c), 2.3.6--2.3.7. No abelianness or reducedness of
projected ray blocks is required, including in the odd-unitary and Ree cases.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.FiniteBruhatSylow

section RayPartition

variable {R V A : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- Representatives enumerate distinct full ray fibers, whose union is exactly
`roots`. In the Borel application `roots` is the chosen positive system. -/
def EnumeratesRayFibers (v : A → V) (roots : Set A) {m : ℕ}
    (a : Fin m → A) : Prop :=
  Function.Injective (fun i => rayPreimage (R := R) v (a i)) ∧
    ∀ β, β ∈ roots ↔ ∃ i, β ∈ rayPreimage (R := R) v (a i)

theorem rayPreimage_disjoint_of_ne (v : A → V) {α β : A}
    (hne : rayPreimage (R := R) v α ≠ rayPreimage (R := R) v β) :
    Disjoint (rayPreimage (R := R) v α) (rayPreimage (R := R) v β) := by
  apply Set.disjoint_left.mpr
  intro γ hγα hγβ
  exact hne ((rayPreimage_eq_of_mem v hγα).symm.trans
    (rayPreimage_eq_of_mem v hγβ))

theorem EnumeratesRayFibers.pairwise_disjoint (v : A → V) (roots : Set A)
    {m : ℕ} {a : Fin m → A} (ha : EnumeratesRayFibers (R := R) v roots a) :
    Pairwise (fun i j => Disjoint (rayPreimage (R := R) v (a i))
      (rayPreimage (R := R) v (a j))) := by
  intro i j hij
  exact rayPreimage_disjoint_of_ne v (fun h => hij (ha.1 h))

omit [IsStrictOrderedRing R] in
theorem EnumeratesRayFibers.fiber_subset (v : A → V) (roots : Set A)
    {m : ℕ} {a : Fin m → A} (ha : EnumeratesRayFibers (R := R) v roots a)
    (i : Fin m) : rayPreimage (R := R) v (a i) ⊆ roots :=
  fun _ h => (ha.2 _).mpr ⟨i, h⟩

/-- Every ray through an interior-cone root remains in that cone. -/
theorem projectedConePreimage_ray_subset (v : A → V) {α β γ : A}
    (hγ : γ ∈ projectedConePreimage (R := R) v α β) :
    rayPreimage (R := R) v γ ⊆ projectedConePreimage (R := R) v α β := by
  obtain ⟨s, t, hs, ht, hγ⟩ := hγ
  rintro δ ⟨c, hc, hδ⟩
  exact ⟨c * s, c * t, mul_pos hc hs, mul_pos hc ht,
    by rw [hδ, hγ, smul_add, smul_smul, smul_smul]⟩

/-- The strictly positive projected cone is closed under root addition. -/
theorem projectedConePreimage_add_closed (v : A → V) (add : A → A → Option A)
    (hadd : ∀ a b c, add a b = some c → v c = v a + v b) (α β : A) :
    ∀ a ∈ projectedConePreimage (R := R) v α β,
      ∀ b ∈ projectedConePreimage (R := R) v α β,
        ∀ c, add a b = some c → c ∈ projectedConePreimage (R := R) v α β := by
  rintro a ⟨s, t, hs, ht, ha⟩ b ⟨s', t', hs', ht', hb⟩ c hc
  refine ⟨s + s', t + t', add_pos hs hs', add_pos ht ht', ?_⟩
  rw [hadd a b c hc, ha, hb]
  module

end RayPartition

section AbsoluteProducts

variable {k : Type*} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K] {T B U : ClosedSubgroup K}
  (D : RootGroupData K T) (C : ChevalleyData K D) [Fintype D.Root]
  {ι R M N V : Type*} [Finite ι] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V]
  (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  (e : D.Root ≃ ι) (base : P.Base)
  (hActual : IsRootSystemRealization D P e base)
  (hAdd : IsRootAdditionRealization D P e)
  (hC : IsChevalleySystem D C P e base)
  (v : M →ₗ[R] V)

include hAdd in
omit [IsAlgClosed k] [Fintype D.Root] [Finite ι] [LinearOrder R]
  [IsStrictOrderedRing R] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
/-- Linearity of the projection transfers exact absolute-root addition. -/
theorem projected_root_add (a b c : D.Root) (hc : D.add a b = some c) :
    v (P.root (e c)) = v (P.root (e a)) + v (P.root (e b)) := by
  rw [(hAdd a b c).mp hc, map_add]

omit [IsAlgClosed k] [Fintype D.Root] in
private theorem rootProduct_function_iff (roots : Set D.Root) (order : List D.Root)
    (ho : EnumeratesRootSet roots order) (x : Variety.Point K) :
    x ∈ OrderedRootSubgroupProductFin D order ↔
      ∃ f : D.Root → Variety.Point K,
        (∀ a ∈ roots, f a ∈ (D.rootSubgroup a).toSubgroup) ∧
          (order.map f).prod = x := by
  classical
  constructor
  · rintro ⟨f, hf, rfl⟩
    let g := Function.extend order.get f (fun _ => 1)
    have hg (i) : g (order.get i) = f i := ho.1.injective_get.extend_apply _ _ i
    refine ⟨g, ?_, ?_⟩
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ((ho.2 a).mpr ha)
      rw [hg]
      exact hf i
    · have heq : List.ofFn (g ∘ order.get) = order.map g := by
        rw [← List.map_ofFn, List.ofFn_get]
      calc
        (order.map g).prod = (List.ofFn (g ∘ order.get)).prod := congrArg List.prod heq.symm
        _ = (List.ofFn f).prod := congrArg (fun q => (List.ofFn q).prod) (funext hg)
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun i => f (order.get i), fun i => hf _ ((ho.2 _).mp (List.get_mem ..)), ?_⟩
    change (order.map f).prod = (List.ofFn (f ∘ order.get)).prod
    rw [← List.map_ofFn, List.ofFn_get]

include hActual hAdd hC in
/-- The actual full ray block is the ordered product of all its absolute
root groups. The ray may contain several absolute-root orbits. -/
theorem rootRayBlock_eq_orderedRootSubgroupProductFin
    (positiveRoots : Set D.Root) (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hGen : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (α : D.Root)
    (hpositive : rayPreimage (R := R) (fun a => v (P.root (e a))) α ⊆ positiveRoots)
    (order : List D.Root)
    (ho : EnumeratesRootSet (rayPreimage (R := R) (fun a => v (P.root (e a))) α) order) :
    (rootRayBlock (R := R) D hSetup.2.1 (fun a => v (P.root (e a))) α :
      Set (Variety.Point K)) = OrderedRootSubgroupProductFin D order := by
  obtain ⟨pkg⟩ := unipotentRootProductPackage T B U D C positiveRoots hSetup hGen
    P e base hActual hAdd hC
  have hclosed : IsClosedRootSubset D
      (rayPreimage (R := R) (fun a => v (P.root (e a))) α) :=
    rayPreimage_add_closed _ D.add (projected_root_add D P e hAdd v) α
  obtain ⟨block⟩ := pkg.closed_subset _ hpositive hclosed
  have hcar : (block.carrier : Set (Variety.Point K)) =
      (rootRayBlock (R := R) D hSetup.2.1 (fun a => v (P.root (e a))) α :
        Set (Variety.Point K)) :=
    congrArg (fun H : Subgroup (Variety.Point K) => (H : Set (Variety.Point K))) block.generated
  exact hcar.symm.trans (block.every_order order ho)

include hActual hAdd hC in
/-- Arbitrarily ordered, distinct full positive-ray fibers give precisely the
injectivity and coverage premises of `existsUnique_restricted_rootRay_factors`.
The marked absolute Chevalley system remains an explicit source obligation. -/
theorem rootRayBlock_orderedProduct_inputs
    (positiveRoots : Set D.Root) (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hGen : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    {m : ℕ} (a : Fin m → D.Root)
    (ha : EnumeratesRayFibers (R := R) (fun b => v (P.root (e b))) positiveRoots a) :
    Function.Injective (Subgroup.orderedProduct
      (fun i => (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b)))
        (a i)).toSubgroup)) ∧
    ∀ x ∈ U.toSubgroup,
      ∃ b : ∀ i, (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b)))
        (a i)).toSubgroup,
        Subgroup.orderedProduct
          (fun i => (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b)))
            (a i)).toSubgroup) b = x := by
  classical
  obtain ⟨pkg⟩ := unipotentRootProductPackage T B U D C positiveRoots hSetup hGen
    P e base hActual hAdd hC
  apply orderedProduct_regroup_partition
    (fun b => (D.rootSubgroup b).toSubgroup) _ U.toSubgroup positiveRoots
    (fun i => rayPreimage (R := R) (fun b => v (P.root (e b))) (a i))
    (ha.pairwise_disjoint _ _) ha.2
  · intro order ho f g hf hg hfg
    have hparams (f : D.Root → Variety.Point K)
        (hf : ∀ b ∈ positiveRoots, f b ∈ (D.rootSubgroup b).toSubgroup) :
        ∃ t : Fin order.length → k, ∀ i, C.x (order.get i) (t i) = f (order.get i) := by
      have hx : ∀ i : Fin order.length, ∃ t, C.x (order.get i) t = f (order.get i) := by
        intro i
        have hi := hf (order.get i) ((ho.2 (order.get i)).mp (List.get_mem order i))
        change f (order.get i) ∈ (D.rootSubgroup (order.get i) : Set (Variety.Point K)) at hi
        rw [← (hC.1 (order.get i)).2] at hi
        exact hi
      exact Classical.axiomOfChoice hx
    obtain ⟨t, ht⟩ := hparams f hf
    obtain ⟨u, hu⟩ := hparams g hg
    have hpt : orderedChevalleyProduct C order t = (order.map f).prod := by
      simp only [orderedChevalleyProduct, ht]
      change (List.ofFn (f ∘ order.get)).prod = _
      rw [← List.map_ofFn, List.ofFn_get]
    have hpu : orderedChevalleyProduct C order u = (order.map f).prod := by
      rw [hfg]
      simp only [orderedChevalleyProduct, hu]
      change (List.ofFn (g ∘ order.get)).prod = _
      rw [← List.map_ofFn, List.ofFn_get]
    have hmem : (order.map f).prod ∈ U := by
      change _ ∈ U.toSubgroup
      rw [hGen]
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact rootSubgroup_le_RootSubgroupGenerated D ((ho.2 b).mp hb)
        (hf b ((ho.2 b).mp hb))
    have htu : t = u := ((pkg.ordered_factorization order ho _).mp hmem).unique hpt hpu
    intro b hb
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ((ho.2 b).mpr hb)
    rw [← ht, ← hu, htu]
  · intro order ho x hx
    obtain ⟨t, ht, -⟩ := (pkg.ordered_factorization order ho x).mp hx
    apply (rootProduct_function_iff D positiveRoots order ho x).mp
    refine ⟨fun i => C.x (order.get i) (t i), ?_, ht.symm⟩
    intro i
    change C.x (order.get i) (t i) ∈ (D.rootSubgroup (order.get i) : Set (Variety.Point K))
    rw [← (hC.1 (order.get i)).2]
    exact Set.mem_range_self _
  · intro i order ho x
    have heq := rootRayBlock_eq_orderedRootSubgroupProductFin D C P e base
      hActual hAdd hC v positiveRoots hSetup hGen (a i) (ha.fiber_subset _ _ i) order ho
    change x ∈ (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b)))
      (a i) : Set (Variety.Point K)) ↔ _
    rw [heq]
    exact rootProduct_function_iff D _ order ho x

include hActual hAdd hC in
/-- The range of the complete ordered ray-block product is exactly the
specified Borel radical. -/
theorem rootRayBlock_orderedProduct_range
    (positiveRoots : Set D.Root) (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hGen : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    {m : ℕ} (a : Fin m → D.Root)
    (ha : EnumeratesRayFibers (R := R) (fun b => v (P.root (e b))) positiveRoots a) :
    Set.range (Subgroup.orderedProduct
      (fun i => (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b)))
        (a i)).toSubgroup)) = (U : Set (Variety.Point K)) := by
  obtain ⟨_, hprod⟩ := rootRayBlock_orderedProduct_inputs D C P e base
    hActual hAdd hC v positiveRoots hSetup hGen a ha
  have hle (i : Fin m) :
      (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b)))
        (a i)).toSubgroup ≤ U.toSubgroup := by
    rw [rootRayBlock_toSubgroup, hGen]
    exact RootSubgroupGenerated_mono D (ha.fiber_subset _ _ i)
  apply Set.Subset.antisymm
  · rintro x ⟨b, rfl⟩
    apply Subgroup.list_prod_mem U.toSubgroup
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact hle i (b i).property
  · exact fun x hx => hprod x hx

include hActual hAdd hC in
/-- Application to the literal restricted blocks: the algebraic injectivity
and product-coverage hypotheses have been discharged by absolute collection. -/
theorem existsUnique_restricted_rootRay_factors_of_chevalley
    (positiveRoots : Set D.Root) (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hGen : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (σ : AlgebraicEndomorphism K) (p : ℕ) [Fact p.Prime] [CharP k p]
    {m : ℕ} (a : Fin m → D.Root)
    (ha : EnumeratesRayFibers (R := R) (fun b => v (P.root (e b))) positiveRoots a)
    (ρ : D.Root → D.Root)
    (hρ : ∀ β, ∃ c : R, 0 < c ∧ v (P.root (e (ρ β))) = c • v (P.root (e β)))
    (hσ : ∀ β x, x ∈ (D.rootSubgroup β).toSubgroup →
      σ.onPoints x ∈ (D.rootSubgroup (ρ β)).toSubgroup)
    (x : positive σ p U) :
    ∃! b : ∀ i, FiniteParabolicRealization.restrict σ p
        (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b))) (a i)).toSubgroup,
      Subgroup.orderedProduct
        (fun i => FiniteParabolicRealization.restrict σ p
          (rootRayBlock (R := R) D hSetup.2.1 (fun b => v (P.root (e b)))
            (a i)).toSubgroup) b = x.val := by
  obtain ⟨hinj, hprod⟩ := rootRayBlock_orderedProduct_inputs D C P e base
    hActual hAdd hC v positiveRoots hSetup hGen a ha
  apply existsUnique_restricted_rootRay_factors σ p D hSetup.2.1
    (fun b => v (P.root (e b))) a U hU _ ρ hρ hσ hinj hprod x
  intro i β hβ
  change (D.rootSubgroup β).toSubgroup ≤ U.toSubgroup
  rw [hGen]
  exact rootSubgroup_le_RootSubgroupGenerated D (ha.fiber_subset _ _ i hβ)

end AbsoluteProducts

end Theory.AlgebraicGroup.FiniteBruhatSylow
