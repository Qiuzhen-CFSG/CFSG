module

public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration
public import Theory.AlgebraicGroup.Bor1.InvariantPullbackSurjective
public import Theory.AlgebraicGroup.Bor1.QuotientUniversal
public import Theory.AlgebraicGroup.Product

/-!
# Regularity from connected generators and their tangents

A point homomorphism whose restrictions to connected algebraic generators are
regular has a closed algebraic graph: the regular paired restrictions generate
that graph as an abstract group, and connected generation is Zariski closed.
If the generator differentials span the source tangent, the first graph
projection has surjective differential. Its coordinate pullback therefore
surjects onto the invariants of its trivial kernel. Descending the second
projection constructs the prescribed global morphism.

The tangent hypothesis is essential in positive characteristic. This argument
uses actual polynomial-function descent, not an inverse to a point bijection.
It is a general form of the root-product argument used in Steinberg (6.2),
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

@[expose] public section
noncomputable section
universe u v
namespace Theory.AlgebraicGroup
open Bor1
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]

/-- The abstract graph embedding in the actual product variety's point group. -/
def pointGraphHom (f : Variety.Point G →* Variety.Point H) :
    Variety.Point G →* Variety.Point (Variety.prod G H) where
  toFun x := (Variety.prodPointEquiv G H).symm (x, f x)
  map_one' := by
    apply (Variety.prodPointEquiv G H).injective
    exact Prod.ext rfl f.map_one
  map_mul' x y := by
    apply (Variety.prodPointEquiv G H).injective
    exact Prod.ext rfl (f.map_mul x y)

/-- Regular restrictions on connected generators make the abstract graph closed. -/
theorem pointGraphHom_range_isZariskiClosed
    (f : Variety.Point G →* Variety.Point H)
    {ι : Type v} (A : ι → Variety k) [∀ i, AlgebraicGroup (A i)]
    (a : ∀ i, Morphism (A i) G) (b : ∀ i, Morphism (A i) H)
    (hconnected : ∀ i, Variety.IsConnected (A i))
    (hgen : Subgroup.closure (⋃ i, Set.range (a i).onPoints) = ⊤)
    (hab : ∀ i x, f ((a i).onPoints x) = (b i).onPoints x) :
    IsZariskiClosed (Variety.prod G H) (pointGraphHom f).range := by
  let C : ι → ClosedSubgroup (Variety.prod G H) :=
    fun i => ((a i).prod (b i)).imageClosedSubgroup
  let S := Subgroup.closure (⋃ i, (C i : Set (Variety.Point (Variety.prod G H))))
  have heq (i) (x : Variety.Point (A i)) :
      ((a i).prod (b i)).onPoints x = pointGraphHom f ((a i).onPoints x) := by
    apply (Variety.prodPointEquiv G H).injective
    exact Prod.ext rfl (hab i x).symm
  have hS : S = (pointGraphHom f).range := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨x, rfl⟩ := hi
      exact ⟨(a i).onPoints x, (heq i x).symm⟩
    · have hpre : (⊤ : Subgroup (Variety.Point G)) ≤ S.comap (pointGraphHom f) := by
        rw [← hgen]
        apply (Subgroup.closure_le _).mpr
        intro z hz
        obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hz
        change pointGraphHom f ((a i).onPoints x) ∈ S
        rw [← heq]
        exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, x, rfl⟩)
      rintro z ⟨x, rfl⟩
      exact hpre (Subgroup.mem_top x)
  rw [← hS]
  exact closure_iUnion_connected_closedSubgroup_isZariskiClosed C
    (fun i => ((a i).prod (b i)).imageClosedSubgroup_isConnected (hconnected i))

/-- A homomorphism is regular when regular connected generators generate its
points and their actual identity differentials span its tangent space. -/
theorem Morphism.exists_of_connected_generators_of_tangent_span
    (f : Variety.Point G →* Variety.Point H)
    {ι : Type v} (A : ι → Variety k) [∀ i, AlgebraicGroup (A i)]
    (a : ∀ i, Morphism (A i) G) (b : ∀ i, Morphism (A i) H)
    (hconnected : ∀ i, Variety.IsConnected (A i))
    (hgen : Subgroup.closure (⋃ i, Set.range (a i).onPoints) = ⊤)
    (hab : ∀ i x, f ((a i).onPoints x) = (b i).onPoints x)
    (hspan : (⨆ i, LinearMap.range (identityTangentMorphismLinearMap (a i))) = ⊤) :
    ∃ F : Morphism G H, F.onPoints = f := by
  let E := ClosedSubgroup.ofSubgroup (pointGraphHom f).range
    (pointGraphHom_range_isZariskiClosed f A a b hconnected hgen hab)
  let : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
  let p : Morphism E.carrierVariety G := (Morphism.fst G H).comp E.inclusion
  let q : Morphism E.carrierVariety H := (Morphism.snd G H).comp E.inclusion
  have hp (x : Variety.Point E.carrierVariety) :
      f (p.onPoints x) = q.onPoints x := by
    obtain ⟨y, hy⟩ := (E.pointEquiv x).property
    have h := congrArg (Variety.prodPointEquiv G H) hy
    exact congrArg f (congrArg Prod.fst h).symm |>.trans (congrArg Prod.snd h)
  have hsurj : Function.Surjective p.onPoints := by
    intro x
    refine ⟨E.pointEquiv.symm ⟨pointGraphHom f x, ⟨x, rfl⟩⟩, ?_⟩
    change (Variety.prodPointEquiv G H
      (E.pointEquiv (E.pointEquiv.symm _)).val).1 = x
    rw [E.pointEquiv.apply_symm_apply]
    rfl
  have hinj : Function.Injective p.onPoints := by
    intro x y hxy
    apply E.inclusion_injective
    apply (Variety.prodPointEquiv G H).injective
    exact Prod.ext hxy ((hp x).symm.trans ((congrArg f hxy).trans (hp y)))
  have hker : p.kernel = ⊥ := (MonoidHom.ker_eq_bot_iff p.onPoints).mpr hinj
  have hdf : Function.Surjective (identityTangentMorphismLinearMap p) := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    rw [← hspan]
    apply iSup_le
    intro i
    let c : Morphism (A i) E.carrierVariety :=
      ((a i).prod (b i)).codRestrictClosedSubgroup E (fun x =>
        ⟨(a i).onPoints x, by
          apply (Variety.prodPointEquiv G H).injective
          exact Prod.ext rfl (hab i x)⟩)
    have hc : p.comp c = a i := by
      apply Morphism.ext
      funext x
      change (Variety.prodPointEquiv G H (E.inclusion.onPoints (c.onPoints x))).1 = _
      exact congrArg (fun z => (Variety.prodPointEquiv G H z).1)
        (((a i).prod (b i)).codRestrictClosedSubgroup_inclusion_apply E _ x)
    rw [← hc, identityTangentMorphismLinearMap_comp]
    exact LinearMap.range_comp_le_range _ _
  let N := p.kernelClosedSubgroup
  have hN : N.toSubgroup.Normal := by
    change p.onPoints.ker.Normal
    infer_instance
  have hq : N.toSubgroup ≤ q.kernel := by
    change p.kernel ≤ q.kernel
    rw [hker]
    exact bot_le
  obtain ⟨F, hF, -⟩ := quotient_universal_of_surjective_invariant_pullback N hN p
    hsurj rfl (pullbackToRightInvariantCoordinateRing_surjective N p hsurj rfl hdf)
    (inferInstance : AlgebraicGroup H) q hq
  refine ⟨F, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact (congrArg (fun m : Morphism E.carrierVariety H => m.onPoints y) hF).trans
    (hp y).symm

end Theory.AlgebraicGroup
