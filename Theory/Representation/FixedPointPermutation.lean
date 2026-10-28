module
public import Theory.Representation.NormalInvariants
public import Theory.Representation.RepEquiv
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Permutation maps from a fixed vector

A vector fixed by a point stabilizer defines an equivariant map from the
transitive permutation module. Its augmentation restriction is nonzero
whenever the vector is moved. When the number of points is nonzero in the
coefficient field, constants split off augmentation; irreducible augmentation
then makes the permutation module semisimple.

The concrete consumer is the Suzuki ovoid module and its Borel-fixed source
seeds. These constructions retain the literal action on every coordinate.
-/

@[expose] public noncomputable section
namespace Representation.FixedPointPermutation
variable {K G Ω W : Type*} [Field K] [Group G] [MulAction G Ω]
  [Fintype Ω] [AddCommGroup W] [Module K W]

def action : Representation K G (Ω → K) where
  toFun g := { toFun v := fun x => v (g⁻¹ • x)
               map_add' := by intros; rfl
               map_smul' := by intros; rfl }
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [mul_smul]

def augmentation : (Ω → K) →ₗ[K] K where
  toFun v := ∑ x, v x
  map_add' := by intros; exact Finset.sum_add_distrib
  map_smul' := by intros; simp [Finset.mul_sum]

def core : Subrepresentation (action (K := K) (G := G) (Ω := Ω)) where
  toSubmodule := (augmentation (K := K) (Ω := Ω)).ker
  apply_mem_toSubmodule g v hv := by
    change (∑ x, v (g⁻¹ • x)) = 0
    exact (Equiv.sum_comp (MulAction.toPerm g⁻¹) v).trans hv

variable [MulAction.IsPretransitive G Ω]
  (x : Ω) (ρ : Representation K G W) (v : W)
  (hv : ∀ g : G, g • x = x → ρ g v = v)

def mover (y : Ω) : G := (MulAction.exists_smul_eq G x y).choose

omit [Fintype Ω] in
theorem mover_apply (y : Ω) : mover (G := G) x y • x = y :=
  (MulAction.exists_smul_eq G x y).choose_spec

def value (y : Ω) : W := ρ (mover x y) v

omit [Fintype Ω] in
include hv in
theorem value_equivariant (g : G) (y : Ω) :
    value x ρ v (g • y) = ρ g (value x ρ v y) := by
  let b := (mover x (g • y))⁻¹ * g * mover x y
  have hb : b • x = x := by
    dsimp only [b]
    rw [mul_smul, mul_smul, mover_apply]
    exact inv_smul_eq_iff.mpr (mover_apply x (g • y)).symm
  have hh := congrArg (ρ (mover x (g • y))) (hv b hb)
  simp only [b, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] at hh
  simpa only [value, map_mul, Module.End.mul_apply] using hh.symm

omit [Fintype Ω] in
include hv in
theorem value_base : value x ρ v x = v := hv _ (mover_apply x x)

def orbitMap : (action (K := K) (G := G) (Ω := Ω)).IntertwiningMap ρ where
  toLinearMap := {
    toFun a := ∑ y, a y • value x ρ v y
    map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    change (∑ y, a (g⁻¹ • y) • value x ρ v y) = ρ g (∑ y, a y • value x ρ v y)
    rw [map_sum]
    simp only [map_smul, ← value_equivariant x ρ v hv]
    exact (Equiv.sum_comp (MulAction.toPerm g)
      (fun y => a (g⁻¹ • y) • value x ρ v y)).symm.trans (by simp)

theorem orbitMap_single [DecidableEq Ω] (y : Ω) : orbitMap x ρ v hv (Pi.single y 1) = value x ρ v y := by
  classical
  simp [orbitMap]

def coreOrbitMap : (core (K := K) (G := G) (Ω := Ω)).toRepresentation.IntertwiningMap ρ where
  toLinearMap := (orbitMap x ρ v hv).toLinearMap.comp (core.toSubmodule.subtype)
  isIntertwining' g := by
    ext a
    exact LinearMap.congr_fun ((orbitMap x ρ v hv).isIntertwining' g) a.val

theorem coreOrbitMap_ne_zero (hmove : ∃ g, ρ g v ≠ v) : coreOrbitMap x ρ v hv ≠ 0 := by
  classical
  intro hz
  obtain ⟨g,hg⟩ := hmove
  let a : (core (K := K) (G := G) (Ω := Ω)).toSubmodule :=
    ⟨Pi.single (g • x) 1 - Pi.single x 1, by
      change (∑ y, ((Pi.single (g • x) 1 - Pi.single x 1) : Ω → K) y) = 0
      simp [Finset.sum_sub_distrib]⟩
  have hh := congrArg (fun f : core.toRepresentation.IntertwiningMap ρ => f a) hz
  change orbitMap x ρ v hv (Pi.single (g • x) 1 - Pi.single x 1) = 0 at hh
  rw [map_sub, orbitMap_single, orbitMap_single,
    value_equivariant x ρ v hv, value_base x ρ v hv] at hh
  exact hg (sub_eq_zero.mp hh)

omit [MulAction.IsPretransitive G Ω] in
include x in
theorem finrank_core : Module.finrank K (core (K := K) (G := G) (Ω := Ω)).toSubmodule + 1 =
    Fintype.card Ω := by
  have hs : Function.Surjective (augmentation (K := K) (Ω := Ω)) := by
    classical
    intro c
    exact ⟨Pi.single x c, by simp [augmentation]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (augmentation (K := K) (Ω := Ω))
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    Module.finrank_pi] at h
  change Module.finrank K (augmentation (K := K) (Ω := Ω)).ker + 1 = _
  omega

section Splitting
omit [MulAction.IsPretransitive G Ω]

def constantsMap : (trivial K G K).IntertwiningMap (action (K := K) (G := G) (Ω := Ω)) where
  toLinearMap := { toFun c := fun _ => c
                   map_add' := by intros; rfl
                   map_smul' := by intros; rfl }
  isIntertwining' _ := rfl

def coreMap : (core (K := K) (G := G) (Ω := Ω)).toRepresentation.IntertwiningMap (action (K := K) (G := G) (Ω := Ω)) where
  toLinearMap := core.toSubmodule.subtype
  isIntertwining' _ := rfl

def splittingMap : ((trivial K G K).prod (core (K := K) (G := G) (Ω := Ω)).toRepresentation).IntertwiningMap
    (action (K := K) (G := G) (Ω := Ω)) where
  toLinearMap := (constantsMap (K := K) (G := G) (Ω := Ω)).toLinearMap.coprod
    (coreMap (K := K) (G := G) (Ω := Ω)).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    rintro ⟨c,a⟩
    ext y
    rfl

theorem splittingMap_surjective (hc : (Fintype.card Ω : K) ≠ 0) :
    Function.Surjective (splittingMap (K := K) (G := G) (Ω := Ω)) := by
  intro a
  let c := (∑ y, a y) / (Fintype.card Ω : K)
  let b : (core (K := K) (G := G) (Ω := Ω)).toSubmodule := ⟨a - (fun _ => c), by
    change (∑ y, (a y - c)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [c, mul_div_cancel₀ _ hc]⟩
  refine ⟨(c,b), ?_⟩
  change (fun y => c + (a y - c)) = a
  ext y
  ring

theorem splittingMap_injective [Nonempty Ω] (hc : (Fintype.card Ω : K) ≠ 0) :
    Function.Injective (splittingMap (K := K) (G := G) (Ω := Ω)) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  rintro ⟨c,b⟩ hb
  have he : (fun y => c + b.val y) = 0 := hb
  have hh := congrArg (fun a : Ω → K => ∑ y, a y) he
  have hsum : (∑ y, b.val y) = 0 := b.property
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hsum, add_zero, Pi.zero_apply, mul_zero] at hh
  have hc0 : c = 0 := (mul_eq_zero.mp hh).resolve_left hc
  have hb0 : b = 0 := Subtype.ext (by simpa [hc0] using he)
  simp [hc0,hb0]

private theorem semisimple_prod {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by
  let l := LinearMap.inl R M N
  let r := LinearMap.inr R M N
  have ht : l.range ⊔ r.range = ⊤ := by
    apply top_unique
    rintro ⟨a,b⟩ _
    exact Submodule.mem_sup.mpr ⟨(a,0),⟨a,rfl⟩,(0,b),⟨b,rfl⟩,by simp⟩
  have hs := IsSemisimpleModule.sup (R := R) (M := M × N)
    (p := l.range) (q := r.range) (IsSemisimpleModule.range l) (IsSemisimpleModule.range r)
  rw [ht] at hs
  let := hs
  exact IsSemisimpleModule.congr (R := R) (M := (⊤ : Submodule R (M × N)))
    (N := M × N) (Submodule.topEquiv (R := R) (M := M × N)).symm

set_option backward.isDefEq.respectTransparency false in
theorem semisimple_of_core_irreducible
    (hc : (Fintype.card Ω : K) ≠ 0)
    (hcore : (core (K := K) (G := G) (Ω := Ω)).toRepresentation.IsIrreducible) :
    IsSemisimpleModule (MonoidAlgebra K G) (action (K := K) (G := G) (Ω := Ω)).asModule := by
  let C := core (K := K) (G := G) (Ω := Ω)
  let t := trivial K G K
  have ht : t.IsIrreducible := by
    let : IsSimpleModule K K := isSimpleModule_iff_finrank_eq_one.mpr (Module.finrank_self K)
    rw [IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, fun S => ?_⟩
    rcases eq_bot_or_eq_top S.toSubmodule with hs | hs
    · exact Or.inl (Subrepresentation.toSubmodule_injective hs)
    · exact Or.inr (Subrepresentation.toSubmodule_injective hs)
  let := ht
  let := hcore
  let : IsSemisimpleModule (MonoidAlgebra K G) (t.asModule × C.toRepresentation.asModule) :=
    semisimple_prod
  let f := IntertwiningMap.equivLinearMapAsModule t
    (action (K := K) (G := G) (Ω := Ω)) (constantsMap (K := K) (G := G) (Ω := Ω))
  let g := IntertwiningMap.equivLinearMapAsModule C.toRepresentation
    (action (K := K) (G := G) (Ω := Ω)) (coreMap (K := K) (G := G) (Ω := Ω))
  apply IsSemisimpleModule.of_surjective
    (M := t.asModule × C.toRepresentation.asModule)
    { toFun := fun a => f a.1 + g a.2
      map_add' := by intro a b; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
      map_smul' := by intro c a; simpa only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
        smul_add] using congrArg₂ (· + ·) (f.map_smul c a.1) (g.map_smul c a.2) }
  exact splittingMap_surjective (K := K) (G := G) (Ω := Ω) hc
end Splitting
end Representation.FixedPointPermutation

