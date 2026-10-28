module
public import Theory.Representation.Suzuki.BorelFixedSemisimple
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry

/-!
# Constituents of Suzuki Borel-fixed cyclic modules

The explicit ovoid decomposition expresses each Borel-fixed vector as a sum
of images of the trivial line and the full Steinberg tensor. Automorphisms
carry Sylow normalizers to conjugate Sylow normalizers; applying the same
augmentation map proves that every automorphic twist of Steinberg is
isomorphic to Steinberg over any extension of the defining field.

These are the constituent inputs to the normal ambient span of the original
A₅ source seeds. Source: Aschbacher–Smith, §13.6, printed p.918, together
with the rank-one permutation action of the Suzuki group.
-/

@[expose] public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural Subgroup

/-- A Borel-fixed vector is a sum of images of the trivial and full tensors. -/
theorem borel_fixed_range_sum {m : ℕ} (hm : 1 ≤ m)
    {K W : Type*} [Field K] [Algebra (F m) K] [AddCommGroup W] [Module K W]
    (ρ : Representation K (SuzukiMatrixGroup m) W) (v : W)
    (hfix : ∀ g ∈ SuzukiBorelSubgroup m, ρ g v = v) :
    ∃ f₀ : (trivial K (SuzukiMatrixGroup m) K).IntertwiningMap ρ,
    ∃ f₁ : (tensorRep m K Finset.univ).IntertwiningMap ρ,
      v ∈ f₀.range ⊔ f₁.range := by
  classical
  let : Fintype (SuzukiOvoid m) := Fintype.ofFinite _
  have hx : ∀ g : SuzukiMatrixGroup m,
      g • suzukiOvoidInfinity m = suzukiOvoidInfinity m → ρ g v = v := by
    intro g hg
    apply hfix g
    rwa [suzukiBorelSubgroup_eq_stabilizer m (by omega), MulAction.mem_stabilizer_iff]
  let o := FixedPointPermutation.orbitMap (suzukiOvoidInfinity m) ρ v hx
  obtain ⟨e⟩ := ovoid_permutation_equiv_trivial_prod_full hm K
  let t := o.comp e.toIntertwiningMap
  let f₀ := t.comp (IntertwiningMap.inl K _ _)
  let f₁ := t.comp (IntertwiningMap.inr K _ _)
  refine ⟨f₀,f₁,?_⟩
  let w := e.symm (Pi.single (suzukiOvoidInfinity m) 1)
  have he : t w = v := by
    change o (e (e.symm _)) = v
    rw [e.apply_symm_apply]
    exact (FixedPointPermutation.orbitMap_single _ ρ v hx _).trans
      (FixedPointPermutation.value_base _ ρ v hx)
  rw [← he]
  change t w ∈ f₀.range.toSubmodule ⊔ f₁.range.toSubmodule
  have hw : w = (w.1,0) + (0,w.2) := by ext <;> simp
  rw [hw,map_add]
  exact Submodule.mem_sup.mpr ⟨t (w.1,0),⟨w.1,rfl⟩,t (0,w.2),⟨w.2,rfl⟩,rfl⟩

/-- Every automorphism carries the full Borel to an inner conjugate. -/
theorem borel_map_automorphism {m : ℕ} (hm : 1 ≤ m)
    (α : SuzukiMatrixGroup m ≃* SuzukiMatrixGroup m) :
    ∃ g : SuzukiMatrixGroup m, (SuzukiBorelSubgroup m).map α.toMonoidHom =
      (SuzukiBorelSubgroup m).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨S,hS⟩ := suzukiRootSubgroup_isSylow m (by omega)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) S
    (S.mapSurjective (f := α.toMonoidHom) α.surjective)
  refine ⟨g,?_⟩
  rw [← suzukiRootSubgroup_normalizer m (by omega),
    map_equiv_normalizer_eq, map_equiv_normalizer_eq]
  congr 1
  have hh := congrArg Sylow.toSubgroup hg
  change (S : Subgroup (SuzukiMatrixGroup m)).map (MulAut.conj g).toMonoidHom =
    (S : Subgroup (SuzukiMatrixGroup m)).map α.toMonoidHom at hh
  exact congrArg (fun Q : Subgroup (SuzukiMatrixGroup m) => (Q : Set (SuzukiMatrixGroup m)))
    (by simpa only [hS] using hh.symm)

/-- The full Steinberg tensor is unchanged by any Suzuki automorphism. -/
theorem full_tensor_comp_equiv {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (F m) K]
    (α : SuzukiMatrixGroup m ≃* SuzukiMatrixGroup m) :
    Nonempty (Representation.Equiv ((tensorRep m K Finset.univ).comp α.toMonoidHom)
      (tensorRep m K Finset.univ)) := by
  classical
  let : Fintype (SuzukiOvoid m) := Fintype.ofFinite _
  let R := tensorRep m K Finset.univ
  let σ : Representation K (SuzukiMatrixGroup m) (TensorSpace m K Finset.univ) :=
    R.comp α.toMonoidHom
  obtain ⟨g,hg⟩ := borel_map_automorphism hm α
  let v := R g (tensorHighestVector m K Finset.univ)
  have hf : ∀ b ∈ SuzukiBorelSubgroup m, σ b v = v := by
    intro b hb
    have hab : α b ∈ (SuzukiBorelSubgroup m).map (MulAut.conj g).toMonoidHom :=
      hg ▸ mem_map_of_mem α.toMonoidHom hb
    obtain ⟨c,hc,he⟩ := hab
    change R (α b) (R g _) = R g _
    rw [← he]
    change R (g*c*g⁻¹) (R g _) = R g _
    rw [← Module.End.mul_apply, ← map_mul, show g*c*g⁻¹*g = g*c by group,
      map_mul, Module.End.mul_apply]
    rw [show R c (tensorHighestVector m K Finset.univ) = tensorHighestVector m K Finset.univ
      from tensorHighestVector_full_fixed_borel m K c hc]
  have hmove : ∃ b, σ b v ≠ v := by
    obtain ⟨b,hb⟩ := highest_full_moved hm K
    refine ⟨α.symm (g*b*g⁻¹),?_⟩
    intro he
    have he' := congrArg (R g⁻¹) he
    apply hb
    change R g⁻¹ (R (α (α.symm (g*b*g⁻¹))) (R g _)) = R g⁻¹ (R g _) at he'
    simpa only [α.apply_symm_apply, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_left, inv_mul_cancel, mul_assoc, mul_inv_cancel_left,
      mul_one, map_one, Module.End.one_apply] using he'
  have hx : ∀ b : SuzukiMatrixGroup m,
      b • suzukiOvoidInfinity m = suzukiOvoidInfinity m → σ b v = v := by
    intro b hb
    apply hf b
    rwa [suzukiBorelSubgroup_eq_stabilizer m (by omega), MulAction.mem_stabilizer_iff]
  let f := FixedPointPermutation.coreOrbitMap (suzukiOvoidInfinity m) σ v hx
  have hn : f ≠ 0 := FixedPointPermutation.coreOrbitMap_ne_zero _ σ v hx hmove
  let : R.IsIrreducible := tensorRep_irreducible hm Finset.univ
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff α.toMonoidHom α.surjective R).mpr
    inferInstance
  let : (FixedPointPermutation.core (K := K) (G := SuzukiMatrixGroup m)
    (Ω := SuzukiOvoid m)).toRepresentation.IsIrreducible := ovoid_augmentation_irreducible hm K
  let ef := f.ofBijective ⟨(IsIrreducible.injective_or_eq_zero f).resolve_right hn,
    (IsIrreducible.surjective_or_eq_zero f).resolve_right hn⟩
  obtain ⟨e⟩ := ovoid_augmentation_equiv_full hm K
  exact ⟨ef.symm.trans e⟩

end Representation.SuzukiSmallDegree
