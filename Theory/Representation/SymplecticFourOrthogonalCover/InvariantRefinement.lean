module

public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.OrthogonalActors
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Quadratic refinements from escaping central kernels

Pull a binary central cover back to the universal orthogonal five-space.
Its displacement span is linear over the coefficient field, even after
restricting scalars. If the central kernel escapes this span, a field-linear
functional separates the radical from the span. Its normalized restriction
to the natural four-space makes the quadratic correction a coboundary and
therefore produces an invariant quadratic refinement of either type.

The ambient application keeps the original elementary subgroup, conjugation
map and central-cover kernel. Source: MS93 (3.3), printed p.867, using (1.5)(ii).
-/

public section
noncomputable section
namespace Representation.SymplecticFourOrthogonalCover
open Matrix ClassicalOrthogonal Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
variable {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]

private theorem exists_correction_functional
    (A : Subgroup (L (K := K)))
    (h : ¬ radical (K := K) ≤ Coinvariants.ker (action.comp A.subtype)) :
    ∃ l : Natural (K := K) →ₗ[K] K, ∀ g : A, ∀ v,
      l (binaryNatural g.val v) + correction g.val.val v = l v := by
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp h
  obtain ⟨f,hfx,hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxn inferInstance
  have hz : f ((0,1) : Space (K := K)) ≠ 0 := by
    intro he
    apply hfx
    have hx' : x = x.2 • ((0,1) : Space (K := K)) := by
      apply Prod.ext
      · simpa only [Prod.smul_fst,smul_zero] using (mem_radical x).mp hx
      · simp
    rw [hx',map_smul,he,smul_zero]
  let l : Natural (K := K) →ₗ[K] K :=
    (f ((0,1) : Space (K := K)))⁻¹ • (f.comp (LinearMap.inl K _ _))
  refine ⟨l,fun g v => ?_⟩
  have hi : f (action g.val (v,0)) = f (v,0) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    have hh : f (action g.val (v,0)-(v,0)) ∈ (⊥ : Submodule K K) := by
      rw [←hf]
      exact Submodule.mem_map_of_mem (Coinvariants.sub_mem_ker
        (ρ := action.comp A.subtype) g (v,0))
    exact hh
  have he : f (action g.val (v,0)) =
      f (binaryNatural g.val v,0)+ correction g.val.val v*f ((0,1) : Space (K := K)) := by
    rw [action_apply]
    have hh : (g.val.val.val *ᵥ v, (0:K)+correction g.val.val v) =
        (binaryNatural g.val v,0)+correction g.val.val v • ((0,1) : Space (K := K)) := by
      apply Prod.ext <;> simp
      rfl
    rw [hh,map_add,map_smul]
    rfl
  rw [he] at hi
  change (f ((0,1) : Space (K := K)))⁻¹*f (binaryNatural g.val v,0)+
    correction g.val.val v = (f ((0,1) : Space (K := K)))⁻¹*f (v,0)
  calc
    _ = (f ((0,1) : Space (K := K)))⁻¹ *
        (f (binaryNatural g.val v,0)+correction g.val.val v*f ((0,1) : Space (K := K))) := by
      rw [mul_add]
      congr 1
      rw [mul_left_comm,inv_mul_cancel₀ hz,mul_one]
    _ = _ := congrArg ((f ((0,1) : Space (K := K)))⁻¹ * ·) hi

private theorem refinement_of_correction_functional
    (A : Subgroup (L (K := K))) (l : Natural (K := K) →ₗ[K] K)
    (hl : ∀ g : A, ∀ v, l (binaryNatural g.val v)+correction g.val.val v=l v) :
    ∃ c : Natural (K := K), ∀ g : A, ∀ v,
      refinement c (binaryNatural g.val v)=refinement c v := by
  let c : Natural (K := K) := fun i => (l (Pi.single i 1))^2
  have he (v : Natural (K := K)) : refinement c v =
      Representation.OneCohomology.SymplecticFour.rowQuadratic v + (l v)^2 := by
    have hv : v = ∑ i, v i • Pi.single i 1 := by
      ext i
      rcases i with i | i <;> fin_cases i <;> simp
    have hlv : l v = ∑ i, v i*l (Pi.single i 1) := by
      conv_lhs => rw [hv]
      simp only [map_sum,map_smul,smul_eq_mul]
    rw [hlv,CharTwo.sum_sq]
    rw [refinement_apply]
    simp only [Representation.OneCohomology.SymplecticFour.rowQuadratic]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [c,mul_pow,mul_comm]
  refine ⟨c,fun g v => ?_⟩
  rw [he,he]
  have hs := congrArg (fun x : K => x^2) (hl g v)
  rw [CharTwo.add_sq] at hs
  change Representation.OneCohomology.SymplecticFour.rowQuadratic
      (g.val.val.val *ᵥ v) + (l (binaryNatural g.val v))^2 = _
  rw [correction_square]
  rw [add_assoc,add_comm (correction g.val.val v^2),hs]

/-- Kernel escape in any binary central quotient forces an invariant field-valued refinement. -/
theorem cover_preserves_refinement_of_kernel_escape
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := K)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (A : Subgroup (L (K := K)))
    (h : ¬ p.toLinearMap.ker ≤ Coinvariants.ker (σ.comp A.subtype)) :
    ∃ c : Natural (K := K), ∀ g : A, ∀ v,
      refinement c (binaryNatural g.val v)=refinement c v := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  have hrad : ¬ radical (K := K) ≤ Coinvariants.ker (action.comp A.subtype) := by
    intro hr
    apply h
    intro w hw
    obtain ⟨v,rfl⟩ := hf w
    have hv : v ∈ radical (K := K) := by
      change p (f v)=0 at hw
      rw [hpf] at hw
      exact hw
    have hv' : v ∈ Coinvariants.ker (binaryAction.comp A.subtype) := by
      change v ∈ Coinvariants.ker (restrictScalars (k := ZMod 2) (action.comp A.subtype))
      rw [coinvariants_restrictScalars]
      exact hr hv
    let fA : Representation.IntertwiningMap (binaryAction.comp A.subtype) (σ.comp A.subtype) :=
      f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => LinearMap.congr_fun (f.isIntertwining' g.val) v)
    rw [←map_coinvariants_of_surjective fA hf]
    exact Submodule.mem_map_of_mem hv'
  obtain ⟨l,hl⟩ := exists_correction_functional A hrad
  exact refinement_of_correction_functional A l hl


open scoped IsMulCommutative commutatorElement

/-- Ambient conjugation turns an escaping literal cover kernel into a
quadratic refinement invariant under the original actor image. -/
theorem ambient_cover_preserves_refinement_of_kernel_escape
    {G : Type*} [Group G] (U D A : Subgroup G)
    [Finite U] [IsElementaryAbelian 2 U]
    (σ : Representation (ZMod 2) (L (K := K)) (Additive U))
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (α : A →* L (K := K))
    (hact : ∀ a : A, ∀ u : U,
      ((σ (α a) (Additive.ofMul u)).toMul : G) = (a:G)*u*(a:G)⁻¹)
    (hcomm : ⁅A,U⁆ ≤ D)
    (hescape : ¬ (p.toLinearMap.ker.toAddSubgroup.toSubgroup').map U.subtype ≤ D) :
    ∃ c : Natural (K := K), ∀ a : A, ∀ v,
      refinement c (binaryNatural (α a) v)=refinement c v := by
  let T : Submodule (ZMod 2) (Additive U) :=
    AddSubgroup.toZModSubmodule 2 (D.subgroupOf U).toAddSubgroup
  have hT : Coinvariants.ker (σ.comp α.range.subtype) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    obtain ⟨a,ha⟩ := g.property
    change ((σ g.val w-w).toMul:G) ∈ D
    rw [←ha,toMul_sub,div_eq_mul_inv]
    have hh := hact a w.toMul
    simp only [ofMul_toMul] at hh
    change ((σ (α a) w).toMul:G) * (w.toMul:G)⁻¹ ∈ D
    rw [hh]
    exact hcomm (Subgroup.commutator_mem_commutator a.property w.toMul.property)
  have he : ¬ p.toLinearMap.ker ≤ Coinvariants.ker (σ.comp α.range.subtype) := by
    intro hle
    apply hescape
    rintro x ⟨u,hu,rfl⟩
    exact hT (hle hu)
  obtain ⟨c,hc⟩ := cover_preserves_refinement_of_kernel_escape p hp α.range he
  exact ⟨c,fun a => hc ⟨α a,⟨a,rfl⟩⟩⟩

/-- The same kernel-escape argument for an embedded binary cover. This keeps
the canonical moved-space carrier and the producer's literal ambient map. -/
theorem embedded_cover_preserves_refinement_of_kernel_escape
    {G : Type*} [Group G] (D A : Subgroup G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (L (K := K)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (j : Multiplicative W →* G) (α : A →* L (K := K))
    (hact : ∀ a : A, ∀ w : W,
      j (Multiplicative.ofAdd (σ (α a) w)) = (a:G)*j (Multiplicative.ofAdd w)*(a:G)⁻¹)
    (hcomm : ⁅A,j.range⁆ ≤ D)
    (hescape : ¬ (p.toLinearMap.ker.toAddSubgroup.toSubgroup).map j ≤ D) :
    ∃ c : Natural (K := K), ∀ a : A, ∀ v,
      refinement c (binaryNatural (α a) v)=refinement c v := by
  let T : Submodule (ZMod 2) W :=
    AddSubgroup.toZModSubmodule 2 (D.comap j).toAddSubgroup'
  have hT : Coinvariants.ker (σ.comp α.range.subtype) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    obtain ⟨a,ha⟩ := g.property
    change j (Multiplicative.ofAdd (σ g.val w-w)) ∈ D
    rw [←ha,ofAdd_sub,map_div,div_eq_mul_inv,hact]
    exact hcomm (Subgroup.commutator_mem_commutator a.property ⟨Multiplicative.ofAdd w,rfl⟩)
  have he : ¬ p.toLinearMap.ker ≤ Coinvariants.ker (σ.comp α.range.subtype) := by
    intro hle
    apply hescape
    rintro x ⟨u,hu,rfl⟩
    exact hT (hle hu)
  obtain ⟨c,hc⟩ := cover_preserves_refinement_of_kernel_escape p hp α.range he
  exact ⟨c,fun a => hc ⟨α a,⟨a,rfl⟩⟩⟩

end Representation.SymplecticFourOrthogonalCover
