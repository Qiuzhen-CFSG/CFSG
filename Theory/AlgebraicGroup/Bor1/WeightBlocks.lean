module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Center

universe u v

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k]
variable {ι : Type v} {V : Type*} [AddCommGroup V] [Module k V]

/-! Linear-algebra infrastructure for the block representation in Bor1 §5.6.

If a decomposition of `V` is indexed by `ι`, the endomorphisms preserving every
block form a submodule.  A linear automorphism which permutes the blocks by an
equivalence normalizes this submodule under conjugation.
-/

@[expose]
public def blockDiagonalEnd (E : ι → Submodule k V) :
    Submodule k (Module.End k V) where
  carrier := {u | ∀ i, ∀ x, x ∈ E i → u x ∈ E i}
  zero_mem' := by
    intro i x hx
    exact (E i).zero_mem
  add_mem' := by
    intro u v hu hv i x hx
    exact (E i).add_mem (hu i x hx) (hv i x hx)
  smul_mem' := by
    intro c u hu i x hx
    exact (E i).smul_mem c (hu i x hx)

public theorem mem_blockDiagonalEnd_iff
    (E : ι → Submodule k V) (u : Module.End k V) :
  u ∈ blockDiagonalEnd E ↔ ∀ i, ∀ x, x ∈ E i → u x ∈ E i :=
  Iff.rfl

/-! The local centralizer calculation used in Bor1 §5.6.  On any free
    finite-dimensional block, an endomorphism commuting with the whole
    endomorphism algebra is scalar.  The blockwise version is obtained by
    applying this lemma to each restriction. -/

public theorem eq_smul_id_of_commute_all
    [Module.Free k V] (A : Module.End k V)
    (hA : ∀ u : Module.End k V, Commute A u) :
    ∃ c : k, A = c • LinearMap.id := by
  have hcenter : A ∈ Set.center (Module.End k V) := by
    rw [Set.mem_center_iff, isMulCentral_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro u
      exact (hA u).eq
    · intro b c
      simp [mul_assoc]
    · intro b c
      simp [mul_assoc]
  obtain ⟨c, hc, hAc⟩ := (Module.End.mem_center_iff.mp hcenter)
  refine ⟨c, ?_⟩
  simpa [Module.End.smulLeft_apply] using hAc

public theorem blockDiagonalEnd_conj_mem
    (E : ι → Submodule k V) (σ : Equiv ι ι)
    (A : LinearMap.GeneralLinearGroup k V)
    (hA : ∀ i, Submodule.map (A : Module.End k V) (E i) = E (σ i))
    (u : Module.End k V) (hu : u ∈ blockDiagonalEnd E) :
    (A : Module.End k V) ∘ₗ u ∘ₗ (↑(A⁻¹) : Module.End k V) ∈
      blockDiagonalEnd E := by
  intro i x hxi
  have hpre : (↑(A⁻¹) : Module.End k V) x ∈ E (σ.symm i) := by
    have hxmap : x ∈ Submodule.map (A : Module.End k V) (E (σ.symm i)) := by
      rw [hA]
      simpa using hxi
    rcases hxmap with ⟨y, hy, hAy⟩
    have hAy' : (A : Module.End k V) y = x := hAy
    have hInv : (↑(A⁻¹) : Module.End k V) x = y := by
      calc
        (↑(A⁻¹) : Module.End k V) x =
            (↑(A⁻¹) : Module.End k V) ((A : Module.End k V) y) := by
              rw [hAy']
        _ = y := by
          change A.toLinearEquiv.symm (A.toLinearEquiv y) = y
          exact A.toLinearEquiv.symm_apply_apply y
    rw [hInv]
    exact hy
  have hmid : u ((↑(A⁻¹) : Module.End k V) x) ∈ E (σ.symm i) :=
    hu (σ.symm i) _ hpre
  have hmap : (A : Module.End k V) (u ((↑(A⁻¹) : Module.End k V) x)) ∈
      Submodule.map (A : Module.End k V) (E (σ.symm i)) :=
    ⟨_, hmid, rfl⟩
  rw [hA] at hmap
  change (A : Module.End k V) (u ((↑(A⁻¹) : Module.End k V) x)) ∈ E i
  simpa only [Equiv.apply_symm_apply] using hmap

/-! The conjugation map can be restricted to the block-diagonal submodule. -/

@[expose]
public def conjEndLinearMap (A : LinearMap.GeneralLinearGroup k V) :
    Module.End k V →ₗ[k] Module.End k V where
  toFun u := (A : Module.End k V) ∘ₗ u ∘ₗ (↑(A⁻¹) : Module.End k V)
  map_add' u v := by
    ext x
    change (A : Module.End k V) ((u + v) ((↑(A⁻¹) : Module.End k V) x)) =
      (A : Module.End k V) (u ((↑(A⁻¹) : Module.End k V) x)) +
        (A : Module.End k V) (v ((↑(A⁻¹) : Module.End k V) x))
    simp

  map_smul' c u := by
    ext x
    change (A : Module.End k V) ((c • u) ((↑(A⁻¹) : Module.End k V) x)) =
      c • (A : Module.End k V) (u ((↑(A⁻¹) : Module.End k V) x))
    simp

public theorem conjEndLinearMap_eq_self_iff
    (A : LinearMap.GeneralLinearGroup k V) (u : Module.End k V) :
    conjEndLinearMap A u = u ↔ Commute (A : Module.End k V) u := by
  constructor
  · intro h
    rw [commute_iff_eq]
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun h ((A : Module.End k V) x)
    change (A : Module.End k V)
        (u ((↑(A⁻¹) : Module.End k V) ((A : Module.End k V) x))) =
      u ((A : Module.End k V) x) at hx
    have hinv : (↑(A⁻¹) : Module.End k V) ((A : Module.End k V) x) = x := by
      change A.toLinearEquiv.symm (A.toLinearEquiv x) = x
      exact A.toLinearEquiv.symm_apply_apply x
    rw [hinv] at hx
    exact hx
  · intro h
    ext x
    change (A : Module.End k V) (u ((↑(A⁻¹) : Module.End k V) x)) = u x
    have hcomm := (commute_iff_eq _ _).mp h
    have hcomm' := LinearMap.congr_fun hcomm ((↑(A⁻¹) : Module.End k V) x)
    change (A : Module.End k V) (u ((↑(A⁻¹) : Module.End k V) x)) =
      u ((A : Module.End k V) ((↑(A⁻¹) : Module.End k V) x)) at hcomm'
    rw [show (A : Module.End k V) ((↑(A⁻¹) : Module.End k V) x) = x by
      change A.toLinearEquiv (A.toLinearEquiv.symm x) = x
      exact A.toLinearEquiv.apply_symm_apply x] at hcomm'
    exact hcomm'

@[expose]
public def blockDiagonalEnd_conjLinearMap
    (E : ι → Submodule k V) (σ : Equiv ι ι)
    (A : LinearMap.GeneralLinearGroup k V)
    (hA : ∀ i, Submodule.map (A : Module.End k V) (E i) = E (σ i)) :
    blockDiagonalEnd E →ₗ[k] blockDiagonalEnd E :=
  LinearMap.codRestrict (blockDiagonalEnd E)
    ((conjEndLinearMap A).domRestrict (blockDiagonalEnd E))
    (fun u => blockDiagonalEnd_conj_mem E σ A hA u.1 u.2)

public theorem blockDiagonalEnd_map_inv
    (E : ι → Submodule k V) (σ : Equiv ι ι)
    (A : LinearMap.GeneralLinearGroup k V)
    (hA : ∀ i, Submodule.map (A : Module.End k V) (E i) = E (σ i)) :
    ∀ i, Submodule.map (↑(A⁻¹) : Module.End k V) (E i) = E (σ.symm i) := by
  intro i
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.map (A : Module.End k V) (E (σ.symm i)) := by
      rw [hA]
      change y ∈ E i at hy
      rw [Equiv.apply_symm_apply]
      exact hy
    rcases hy' with ⟨z, hz, hAz⟩
    have hInv : (↑(A⁻¹) : Module.End k V) y = z := by
      calc
        (↑(A⁻¹) : Module.End k V) y =
            (↑(A⁻¹) : Module.End k V) ((A : Module.End k V) z) := by rw [hAz]
        _ = z := by
          change A.toLinearEquiv.symm (A.toLinearEquiv z) = z
          exact A.toLinearEquiv.symm_apply_apply z
    rw [hInv]
    exact hz
  · rintro x hx
    refine ⟨(A : Module.End k V) x, ?_, ?_⟩
    · have hxi : (A : Module.End k V) x ∈ E i := by
        have hm : (A : Module.End k V) x ∈
            Submodule.map (A : Module.End k V) (E (σ.symm i)) :=
          ⟨x, hx, rfl⟩
        rw [hA (σ.symm i)] at hm
        simpa only [Equiv.apply_symm_apply] using hm
      exact hxi
    · change A.toLinearEquiv.symm (A.toLinearEquiv x) = x
      exact A.toLinearEquiv.symm_apply_apply x

public theorem blockDiagonalEnd_conjLinearMap_apply
    (E : ι → Submodule k V) (σ : Equiv ι ι)
    (A : LinearMap.GeneralLinearGroup k V)
    (hA : ∀ i, Submodule.map (A : Module.End k V) (E i) = E (σ i))
    (u : blockDiagonalEnd E) :
    (blockDiagonalEnd_conjLinearMap E σ A hA u).1 =
      (A : Module.End k V) ∘ₗ u.1 ∘ₗ (↑(A⁻¹) : Module.End k V) := by
  simp [blockDiagonalEnd_conjLinearMap, LinearMap.codRestrict,
    LinearMap.domRestrict, conjEndLinearMap]

public theorem conjEndLinearMap_one :
    conjEndLinearMap (1 : LinearMap.GeneralLinearGroup k V) = LinearMap.id := by
  ext u x
  change ((1 : Module.End k V) ∘ₗ u ∘ₗ
    (↑((1 : LinearMap.GeneralLinearGroup k V)⁻¹) : Module.End k V)) x = u x
  simp

public theorem conjEndLinearMap_mul
    (A B : LinearMap.GeneralLinearGroup k V) :
    conjEndLinearMap (A * B) =
      (conjEndLinearMap A).comp (conjEndLinearMap B) := by
  ext u x
  change ((A * B : LinearMap.GeneralLinearGroup k V) : Module.End k V)
      (u ((↑((A * B)⁻¹) : Module.End k V) x)) =
    (A : Module.End k V)
      ((B : Module.End k V)
        (u ((↑(B⁻¹) : Module.End k V)
          ((↑(A⁻¹) : Module.End k V) x))))
  rw [show ((A * B : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
      (A : Module.End k V) * (B : Module.End k V) by
    exact Units.val_mul A B]
  rw [show ((↑((A * B)⁻¹) : Module.End k V) x) =
      (↑(B⁻¹) : Module.End k V) ((↑(A⁻¹) : Module.End k V) x) by
    rw [show (A * B)⁻¹ = B⁻¹ * A⁻¹ by simp]
    exact congrArg (fun z : Module.End k V => z x) (Units.val_mul B⁻¹ A⁻¹)]
  simp only [Module.End.mul_apply]

@[expose]
public noncomputable def conjEndGeneralLinear
    (A : LinearMap.GeneralLinearGroup k V) :
    LinearMap.GeneralLinearGroup k (Module.End k V) where
  val := conjEndLinearMap A
  inv := conjEndLinearMap A⁻¹
  val_inv := by
    ext u x
    change (conjEndLinearMap A) ((conjEndLinearMap A⁻¹) u) x = u x
    rw [← LinearMap.comp_apply]
    rw [← conjEndLinearMap_mul, mul_inv_cancel, conjEndLinearMap_one]
    rfl
  inv_val := by
    ext u x
    change (conjEndLinearMap A⁻¹) ((conjEndLinearMap A) u) x = u x
    rw [← LinearMap.comp_apply]
    rw [← conjEndLinearMap_mul, inv_mul_cancel, conjEndLinearMap_one]
    rfl

@[expose]
public noncomputable def conjEndRepresentation :
    LinearMap.GeneralLinearGroup k V →*
      LinearMap.GeneralLinearGroup k (Module.End k V) where
  toFun := conjEndGeneralLinear
  map_one' := Units.ext conjEndLinearMap_one
  map_mul' := by
    intro A B
    apply Units.ext
    exact conjEndLinearMap_mul A B

/-! A block-permuting representation induces a representation on the
    block-diagonal endomorphisms.  Notice that the permutation data are only
    needed to prove preservation of the submodule; the multiplicativity proof
    is the ordinary multiplicativity of conjugation. -/

@[expose]
public noncomputable def blockDiagonalEnd_conjGeneralLinear
    (E : ι → Submodule k V) (σ : Equiv ι ι)
    (A : LinearMap.GeneralLinearGroup k V)
    (hA : ∀ i, Submodule.map (A : Module.End k V) (E i) = E (σ i)) :
    LinearMap.GeneralLinearGroup k (blockDiagonalEnd E) where
  val := blockDiagonalEnd_conjLinearMap E σ A hA
  inv := blockDiagonalEnd_conjLinearMap E σ.symm A⁻¹
    (blockDiagonalEnd_map_inv E σ A hA)
  val_inv := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (blockDiagonalEnd_conjLinearMap E σ A hA
      (blockDiagonalEnd_conjLinearMap E σ.symm A⁻¹
        (blockDiagonalEnd_map_inv E σ A hA) u)).1 = u.1
    rw [blockDiagonalEnd_conjLinearMap_apply, blockDiagonalEnd_conjLinearMap_apply]
    change ((conjEndLinearMap A).comp (conjEndLinearMap A⁻¹)) u.1 = u.1
    rw [← conjEndLinearMap_mul, mul_inv_cancel, conjEndLinearMap_one]
    rfl
  inv_val := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (blockDiagonalEnd_conjLinearMap E σ.symm A⁻¹
      (blockDiagonalEnd_map_inv E σ A hA)
      (blockDiagonalEnd_conjLinearMap E σ A hA u)).1 = u.1
    rw [blockDiagonalEnd_conjLinearMap_apply, blockDiagonalEnd_conjLinearMap_apply]
    change ((conjEndLinearMap A⁻¹).comp (conjEndLinearMap A)) u.1 = u.1
    rw [← conjEndLinearMap_mul, inv_mul_cancel, conjEndLinearMap_one]
    rfl

public theorem blockDiagonalEnd_conjGeneralLinear_apply_eq_self_iff
    (E : ι → Submodule k V) (σ : Equiv ι ι)
    (A : LinearMap.GeneralLinearGroup k V)
    (hA : ∀ i, Submodule.map (A : Module.End k V) (E i) = E (σ i))
    (u : blockDiagonalEnd E) :
    (blockDiagonalEnd_conjGeneralLinear E σ A hA :
      Module.End k (blockDiagonalEnd E)) u = u ↔
      Commute (A : Module.End k V) u.1 := by
  constructor
  · intro h
    apply (conjEndLinearMap_eq_self_iff A u.1).mp
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    apply (conjEndLinearMap_eq_self_iff A u.1).mpr h

/-! The preceding pointwise calculation packages the exact kernel test for
    the block-conjugation representation.  This is the form used in Bor1
    §5.6: the conjugation action is trivial precisely when the original
    operator centralizes the whole block-diagonal endomorphism algebra. -/

public theorem blockDiagonalEnd_conjGeneralLinear_eq_one_iff
    (E : ι → Submodule k V) (σ : Equiv ι ι)
    (A : LinearMap.GeneralLinearGroup k V)
    (hA : ∀ i, Submodule.map (A : Module.End k V) (E i) = E (σ i)) :
    blockDiagonalEnd_conjGeneralLinear E σ A hA = 1 ↔
      ∀ u : blockDiagonalEnd E, Commute (A : Module.End k V) u.1 := by
  constructor
  · intro h u
    apply (blockDiagonalEnd_conjGeneralLinear_apply_eq_self_iff E σ A hA u).mp
    have hval :
        (blockDiagonalEnd_conjGeneralLinear E σ A hA :
          LinearMap.GeneralLinearGroup k (blockDiagonalEnd E)) =
          (1 : LinearMap.GeneralLinearGroup k (blockDiagonalEnd E)) := h
    have hu := congrArg
      (fun L : Module.End k (blockDiagonalEnd E) => L u)
      (congrArg Units.val hval)
    simpa using hu
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    have hu := (blockDiagonalEnd_conjGeneralLinear_apply_eq_self_iff E σ A hA u).mpr
      (h u)
    exact congrArg Subtype.val hu

/-! For the full endomorphism algebra, the same kernel calculation reduces to
the scalar operators.  This is the elementary centralizer step used in
Bor1 §5.6 before restricting to block-diagonal endomorphisms. -/

public theorem conjEndGeneralLinear_eq_one_iff_eq_scalar
    [Module.Free k V] (A : LinearMap.GeneralLinearGroup k V) :
    conjEndGeneralLinear A = 1 ↔
      ∃ c : k, (A : Module.End k V) = c • LinearMap.id := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := eq_smul_id_of_commute_all (A : Module.End k V) (by
      intro u
      apply (conjEndLinearMap_eq_self_iff A u).mp
      have hu := congrArg
        (fun L : LinearMap.GeneralLinearGroup k (Module.End k V) =>
          (L : Module.End k (Module.End k V)) u) h
      exact hu)
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply (conjEndLinearMap_eq_self_iff A u).mpr
    rw [hc]
    show (c • LinearMap.id) * u = u * (c • LinearMap.id)
    ext x
    simp [Module.End.mul_apply]

/-! A representation has exactly a prescribed kernel after passing to the
full End-space conjugation representation as soon as its scalar elements are
exactly the prescribed subgroup. -/

public theorem conjEndRepresentation_comp_ker_eq_of_scalar_iff
    [Module.Free k V] {Γ : Type*} [Group Γ]
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (N : Subgroup Γ)
    (hN : ∀ g : Γ,
      (∃ c : k, (ρ g : Module.End k V) = c • LinearMap.id) ↔ g ∈ N) :
    (conjEndRepresentation.comp ρ).ker = N := by
  ext g
  change conjEndGeneralLinear (ρ g) = 1 ↔ g ∈ N
  rw [conjEndGeneralLinear_eq_one_iff_eq_scalar]
  exact hN g

@[expose]
public noncomputable def blockDiagonalEnd_conjRepresentation
    {Γ : Type*} [Monoid Γ]
    (E : ι → Submodule k V)
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (σ : Γ →* Equiv.Perm ι)
    (hA : ∀ g i, Submodule.map
      ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i)) :
    Γ →* LinearMap.GeneralLinearGroup k (blockDiagonalEnd E) where
  toFun g := blockDiagonalEnd_conjGeneralLinear E (σ g) (ρ g) (hA g)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (blockDiagonalEnd_conjLinearMap E (σ 1) (ρ 1) (hA 1) u).1 = u.1
    simp only [map_one]
    rw [blockDiagonalEnd_conjLinearMap_apply]
    change (conjEndLinearMap (1 : LinearMap.GeneralLinearGroup k V)) u.1 = u.1
    rw [conjEndLinearMap_one]
    rfl
  map_mul' := by
    intro g h
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (blockDiagonalEnd_conjLinearMap E (σ (g * h)) (ρ (g * h))
      (hA (g * h)) u).1 =
      ((blockDiagonalEnd_conjGeneralLinear E (σ g) (ρ g) (hA g)) *
        (blockDiagonalEnd_conjGeneralLinear E (σ h) (ρ h) (hA h))).val u
    change (blockDiagonalEnd_conjLinearMap E (σ (g * h)) (ρ (g * h))
      (hA (g * h)) u).1 =
      ((blockDiagonalEnd_conjLinearMap E (σ g) (ρ g) (hA g))
        ((blockDiagonalEnd_conjLinearMap E (σ h) (ρ h) (hA h)) u)).1
    rw [blockDiagonalEnd_conjLinearMap_apply,
      blockDiagonalEnd_conjLinearMap_apply,
      blockDiagonalEnd_conjLinearMap_apply]
    rw [map_mul ρ]
    change (conjEndLinearMap (ρ g * ρ h)) u.1 =
      (conjEndLinearMap (ρ g)) ((conjEndLinearMap (ρ h)) u.1)
    exact congrArg (fun L : Module.End k V →ₗ[k] Module.End k V => L u.1)
      (conjEndLinearMap_mul (ρ g) (ρ h))

public theorem blockDiagonalEnd_conjRepresentation_eq_one_iff
    {Γ : Type*} [Monoid Γ]
    (E : ι → Submodule k V)
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (σ : Γ →* Equiv.Perm ι)
    (hA : ∀ g i, Submodule.map
      ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i))
    (g : Γ) :
    (blockDiagonalEnd_conjRepresentation E ρ σ hA g) = 1 ↔
      ∀ u : blockDiagonalEnd E,
        Commute ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) u.1 := by
  exact blockDiagonalEnd_conjGeneralLinear_eq_one_iff E (σ g) (ρ g) (hA g)

public theorem blockDiagonalEnd_conjRepresentation_ker_eq
    {Γ : Type*} [Group Γ]
    (E : ι → Submodule k V)
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (σ : Γ →* Equiv.Perm ι)
    (hA : ∀ g i, Submodule.map
      ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i))
    (N : Subgroup Γ)
    (hN : ∀ g : Γ,
      (∀ u : blockDiagonalEnd E,
        Commute ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) u.1) ↔
        g ∈ N) :
    (blockDiagonalEnd_conjRepresentation E ρ σ hA).ker = N := by
  ext g
  rw [MonoidHom.mem_ker, blockDiagonalEnd_conjRepresentation_eq_one_iff]
  exact hN g

end Theory.AlgebraicGroup.Bor1
