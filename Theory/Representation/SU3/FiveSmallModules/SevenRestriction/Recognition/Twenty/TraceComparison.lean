module
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.RepresentationTheory.Character

/-!
# Trace comparison over the original coefficient field

An absolutely irreducible representation and an irreducible representation
with equal trace characters are equivalent over their original field, in
arbitrary characteristic. Only the first representation needs to be absolute.

For inequivalent simple modules, Jacobson density separates a trace-one map
on the absolute module from zero on the other module. Off-diagonal module
endomorphisms vanish by simplicity, and the absolute module's endomorphisms
are scalars, so the chosen map lies in the bicommutant. Equality of traces
on group elements extends linearly to the group algebra and contradicts
this separator.

The degree-twenty recognition assembly applies this to an actual simple
factor of trivial Borel induction. It does not assume a splitting field or
extract integer spectral multiplicities from a characteristic-two trace.
Source: Jacobson density, as formalized by Mathlib's `jacobson_density`;
application to Guralnick–Malle, *Classification of 2F-modules I*, Prop. 4.3.
-/

open scoped MonoidAlgebra
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty

private theorem separate_simple_modules
    {F A ι : Type*} [Field F] [Ring A] [Algebra F A] [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
    [∀ i, Module A (M i)] [∀ i, IsScalarTower F A (M i)]
    [∀ i, FiniteDimensional F (M i)] [∀ i, IsSimpleModule A (M i)]
    (hne : Pairwise fun i j => IsEmpty (M i ≃ₗ[A] M j)) (k : ι)
    (hs : Function.Surjective (algebraMap F (Module.End A (M k))))
    (f : Module.End F (M k)) :
    ∃ a : A, (∀ v : M k, a • v = f v) ∧
      ∀ i, i ≠ k → ∀ v : M i, a • v = 0 := by
  classical
  let component (T : Module.End A (Π i, M i)) (i j : ι) : M j →ₗ[A] M i :=
    (LinearMap.proj i).comp (T.comp (LinearMap.single A M j))
  have diagonal (T : Module.End A (Π i, M i)) (v : Π i, M i) (i : ι) :
      (T v) i = component T i i (v i) := by
    calc
      (T v) i = ∑ j, component T i j (v j) := by
        conv_lhs => rw [← Finset.univ_sum_single v]
        simp only [map_sum, Finset.sum_apply]
        rfl
      _ = component T i i (v i) := by
        apply Finset.sum_eq_single i
        · intro j _ hj
          have hz : component T i j = 0 := by
            by_contra h
            exact (hne hj).false
              (LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero h))
          rw [hz, LinearMap.zero_apply]
        · simp
  let fs : ∀ i, Module.End F (M i) := fun i => if h : i = k then h ▸ f else 0
  let P := Π i, M i
  let fp : Module.End F P := LinearMap.pi fun i => (fs i).comp (LinearMap.proj i)
  have hcomm (T : Module.End A P) (v : P) : fp (T v) = T (fp v) := by
    funext i
    change fs i ((T v) i) = (T (fp v)) i
    rw [diagonal, diagonal]
    change fs i (component T i i (v i)) = component T i i (fs i (v i))
    by_cases hi : i = k
    · subst i
      obtain ⟨c, hc⟩ := hs (component T k k)
      simp only [fs, dif_pos rfl]
      rw [← hc]
      exact f.map_smul c (v k)
    · simp [fs, hi]
  let fp' : Module.End (Module.End A P) P :=
    { fp.toAddHom with map_smul' T v := hcomm T v }
  let b := Module.finBasis F P
  obtain ⟨a, ha⟩ := jacobson_density fp' (Finset.univ.image b)
  have heq : fp = (Module.toModuleEnd F (S := A) P) a := by
    apply b.ext
    intro j
    exact ha (b j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have he (i : ι) (v : M i) : a • v = fs i v := by
    have h := congrArg (fun T : Module.End F P => T (Pi.single i v) i) heq
    change fs i (Pi.single i v i) = a • Pi.single i v i at h
    simpa only [Pi.single_eq_same] using h.symm
  exact ⟨a, by simpa [fs] using he k,
    fun i hi v => by simpa [fs, hi] using he i v⟩

private theorem trace_one {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Nontrivial V] :
    ∃ t : Module.End F V, LinearMap.trace F V t = 1 := by
  classical
  let b := Module.finBasis F V
  let k : Fin (Module.finrank F V) := ⟨0, Module.finrank_pos⟩
  let u := LinearMap.toSpanSingleton F V (b k)
  have hu : (b.coord k).comp u = LinearMap.id := by
    apply LinearMap.ext
    intro c
    simp [u]
  refine ⟨u.comp (b.coord k), ?_⟩
  rw [LinearMap.trace_comp_comm', hu, LinearMap.trace_id]
  simp

universe u
/-- Equal trace characters identify an absolute simple module with a simple
module over the same field; no group-order invertibility is needed. -/
public theorem equiv_of_equal_trace
    {F G : Type*} [Field F] [Monoid G]
    {V W : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G V) (σ : Representation F G W)
    [ρ.IsAbsolutelyIrreducible] [σ.IsIrreducible]
    (hchar : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  classical
  let : ρ.IsIrreducible := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  by_contra hne
  let M : Bool → Type _ := fun b => if b then σ.asModule else ρ.asModule
  let addM : ∀ b, AddCommGroup (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let modM : ∀ b, Module F (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let modA : ∀ b, Module F[G] (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let tower : ∀ b, IsScalarTower F F[G] (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let fd : ∀ b, FiniteDimensional F (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let si : ∀ b, IsSimpleModule F[G] (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  have hn : IsEmpty (ρ.asModule ≃ₗ[F[G]] σ.asModule) := by
    refine ⟨fun e => hne ?_⟩
    let e' := (IntertwiningMap.equivLinearMapAsModule ρ σ).symm e.toLinearMap
    exact ⟨e'.ofBijective e.bijective⟩
  have hp : Pairwise fun i j => IsEmpty (M i ≃ₗ[F[G]] M j) := by
    intro i j hij
    constructor
    intro e
    cases i <;> cases j
    · exact hij rfl
    · exact hn.false e
    · exact hn.false e.symm
    · exact hij rfl
  have hs : Function.Surjective (algebraMap F (Module.End F[G] ρ.asModule)) :=
    (algebraMap_surj_iff_surj ρ).mpr ((isAbsolutelyIrreducible_iff_surjective ρ).mp inferInstance)
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨t, ht⟩ := trace_one (F := F) (V := V)
  obtain ⟨a, ha, hb⟩ := separate_simple_modules M hp false hs (ρ.asModuleEquiv.symm.conj t)
  have hρ : ρ.asAlgebraHom a = t := by
    ext v
    have h := congrArg ρ.asModuleEquiv (ha (ρ.asModuleEquiv.symm v))
    change (ρ.asAlgebraHom a) v = t v at h
    exact h
  have hσ : σ.asAlgebraHom a = 0 := by
    ext v
    have h := congrArg σ.asModuleEquiv (hb true (by decide) (σ.asModuleEquiv.symm v))
    change (σ.asAlgebraHom a) v = 0 at h
    exact h
  have hlin : (LinearMap.trace F V).comp ρ.asAlgebraHom.toLinearMap =
      (LinearMap.trace F W).comp σ.asAlgebraHom.toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext
    intro r
    have h := congrFun hchar g
    simpa [character] using congrArg (r • ·) h
  have h := congrArg (fun f : F[G] →ₗ[F] F => f a) hlin
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hρ, hσ, map_zero, ht] at h
  exact one_ne_zero h
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
