module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.LocalRing.Basic

universe u v w

/-! The top wedge of a basis indexed by `Fin n` is nonzero. -/

namespace Theory.AlgebraicGroup

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k]
variable {M : Type v} [AddCommGroup M] [Module k M]

public lemma exteriorPower_ιMulti_finBasis_ne_zero
    (n : ℕ) (b : Module.Basis (Fin n) k M) :
    exteriorPower.ιMulti k n b ≠ 0 := by
  let e : Fin n ↪o Fin n := OrderEmbedding.id (Fin n)
  let s : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv e
  have hli := exteriorPower.ιMulti_family_linearIndependent_field
    (n := n) b.linearIndependent
  have hs := hli.ne_zero s
  simpa [s, e, exteriorPower.ιMulti_family] using hs

end

section

open scoped ExteriorAlgebra

variable (k : Type u) [Field k]
variable (M : Type v) [AddCommGroup M] [Module k M]

/-- A finite basis packaged with an abstract exterior degree, avoiding repeated
reduction of concrete `finrank` expressions in downstream dependent types. -/
public structure FiniteSubspaceTopWedgeData where
  degree : ℕ
  basis : Module.Basis (Fin degree) k M

/-- The top wedge selected by finite-subspace data. -/
@[expose]
public noncomputable def FiniteSubspaceTopWedgeData.vector
    (D : FiniteSubspaceTopWedgeData k M) : ⋀[k]^D.degree M :=
  exteriorPower.ιMulti k D.degree D.basis

/-- The selected top wedge is nonzero. -/
public lemma FiniteSubspaceTopWedgeData.vector_ne_zero
    (D : FiniteSubspaceTopWedgeData k M) : D.vector ≠ 0 :=
  exteriorPower_ιMulti_finBasis_ne_zero D.degree D.basis

end

/-! Vanishing of a finite exterior product detects linear dependence over a field. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k]
variable {M : Type v} [AddCommGroup M] [Module k M]

public lemma exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent
    (n : ℕ) (v : Fin n → M) :
    exteriorPower.ιMulti k n v = 0 ↔ ¬ LinearIndependent k v := by
  constructor
  · intro h hli
    let e : Fin n ↪o Fin n := OrderEmbedding.id (Fin n)
    let s : Set.powersetCard (Fin n) n := Set.powersetCard.ofFinEmbEquiv e
    have hfamily := exteriorPower.ιMulti_family_linearIndependent_field
      (n := n) hli
    have hs := hfamily.ne_zero s
    exact hs (by simpa [s, e, exteriorPower.ιMulti_family] using h)
  · intro h
    exact (exteriorPower.ιMulti k n).map_linearDependent v h

end

/-! Adjoining a vector to an independent family gives zero exterior product exactly on its span. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k]
variable {M : Type v} [AddCommGroup M] [Module k M]

public lemma exteriorPower_ιMulti_cons_eq_zero_iff_mem_span
    (n : ℕ) (v : Fin n → M) (hv : LinearIndependent k v) (x : M) :
    exteriorPower.ιMulti k (n + 1) (Fin.cons x v) = 0 ↔
      x ∈ Submodule.span k (Set.range v) := by
  rw [exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent,
    linearIndependent_finCons, not_and_or]
  simp [hv]

end

/-! Exterior multiplication by a top wedge detects membership in its span. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k]
variable {M : Type v} [AddCommGroup M] [Module k M]

public lemma exteriorAlgebra_ι_mul_ιMulti_eq_zero_iff_mem_span
    (n : ℕ) (v : Fin n → M) (hv : LinearIndependent k v) (x : M) :
    ExteriorAlgebra.ι k x *
        (exteriorPower.ιMulti k n v : ExteriorAlgebra k M) = 0 ↔
      x ∈ Submodule.span k (Set.range v) := by
  rw [← exteriorPower_ιMulti_cons_eq_zero_iff_mem_span n v hv x]
  rw [← Submodule.coe_eq_zero]
  simp only [exteriorPower.ιMulti_apply_coe]
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  have htail : Matrix.vecTail (Fin.cons x v) = v := by
    ext i
    exact Fin.cons_succ (α := fun _ => M) x v i
  rw [htail]
  simp

end

/-! A mapped top wedge recovers the range of the underlying injection. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k]
variable {U : Type v} [AddCommGroup U] [Module k U]
variable {M : Type w} [AddCommGroup M] [Module k M]

public lemma FiniteSubspaceTopWedgeData.range_iff_ι_mul_vector_eq_zero
    (D : FiniteSubspaceTopWedgeData k U) (f : U →ₗ[k] M)
    (hf : Function.Injective f) (x : M) :
    ExteriorAlgebra.ι k x *
        ((exteriorPower.map D.degree f D.vector :
          ⋀[k]^D.degree M) : ExteriorAlgebra k M) = 0 ↔
      x ∈ LinearMap.range f := by
  rw [show D.vector = exteriorPower.ιMulti k D.degree D.basis from rfl]
  rw [exteriorPower.map_apply_ιMulti]
  rw [exteriorAlgebra_ι_mul_ιMulti_eq_zero_iff_mem_span D.degree
    (f ∘ D.basis) (D.basis.linearIndependent.map' f
      (LinearMap.ker_eq_bot.mpr hf)) x]
  have hspan :
      Submodule.span k (Set.range (f ∘ D.basis)) = LinearMap.range f := by
    calc
      Submodule.span k (Set.range (f ∘ D.basis)) =
          Submodule.span k (f '' Set.range D.basis) := by
        rw [Set.range_comp]
      _ = Submodule.map f (Submodule.span k (Set.range D.basis)) :=
        (Submodule.map_span f (Set.range D.basis)).symm
      _ = Submodule.map f ⊤ := by rw [D.basis.span_eq]
      _ = LinearMap.range f := (LinearMap.range_eq_map f).symm
  rw [hspan]

end

/-! Stabilizing a mapped top-wedge line is equivalent to stabilizing the original range. -/

open scoped ExteriorAlgebra
section
variable {k : Type u} [Field k]
variable {U : Type v} [AddCommGroup U] [Module k U]
variable {M : Type w} [AddCommGroup M] [Module k M]

public lemma FiniteSubspaceTopWedgeData.map_mem_span_iff_range_stable
    (D : FiniteSubspaceTopWedgeData k U) (f : U →ₗ[k] M)
    (hf : Function.Injective f) (T : M ≃ₗ[k] M) :
    exteriorPower.map D.degree T.toLinearMap
        (exteriorPower.map D.degree f D.vector) ∈
          k ∙ exteriorPower.map D.degree f D.vector ↔
      ∀ u : U, T (f u) ∈ LinearMap.range f := by
  let p : ⋀[k]^D.degree M := exteriorPower.map D.degree f D.vector
  have hpne : p ≠ 0 := by
    exact (map_ne_zero_iff (exteriorPower.map D.degree f)
      (exteriorPower.map_injective_field (n := D.degree) hf)).mpr D.vector_ne_zero
  constructor
  · intro hline u
    rw [← D.range_iff_ι_mul_vector_eq_zero f hf]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hline
    have hmapne : exteriorPower.map D.degree T.toLinearMap p ≠ 0 := by
      exact (map_ne_zero_iff (exteriorPower.map D.degree T.toLinearMap)
        (exteriorPower.map_injective_field (n := D.degree) T.injective)).mpr hpne
    have hcne : c ≠ 0 := by
      intro hczero
      apply hmapne
      rw [← hc]
      simp [hczero]
    have hmapcomp :
        exteriorPower.map D.degree T.toLinearMap p =
          exteriorPower.map D.degree (T.toLinearMap.comp f) D.vector := by
      dsimp [p]
      rw [exteriorPower.map_comp, LinearMap.comp_apply]
    have hz :
        ExteriorAlgebra.ι k (T (f u)) *
          ((exteriorPower.map D.degree T.toLinearMap p :
            ⋀[k]^D.degree M) : ExteriorAlgebra k M) = 0 := by
      rw [hmapcomp]
      rw [D.range_iff_ι_mul_vector_eq_zero
        (T.toLinearMap.comp f) (T.injective.comp hf)]
      exact ⟨u, rfl⟩
    have hcoe :
        ((exteriorPower.map D.degree T.toLinearMap p :
          ⋀[k]^D.degree M) : ExteriorAlgebra k M) =
            c • (p : ExteriorAlgebra k M) := by
      exact congrArg Subtype.val hc.symm
    rw [hcoe, Algebra.mul_smul_comm] at hz
    exact (smul_eq_zero.mp hz).resolve_left hcne
  · intro hstable
    let ef : U ≃ₗ[k] LinearMap.range f := LinearEquiv.ofInjective f hf
    let tf : U →ₗ[k] LinearMap.range f :=
      (T.toLinearMap.comp f).codRestrict (LinearMap.range f) hstable
    let S : U →ₗ[k] U := ef.symm.toLinearMap.comp tf
    have hSf (u : U) : f (S u) = T (f u) := by
      change f (ef.symm (tf u)) = T (f u)
      rw [LinearEquiv.ofInjective_symm_apply]
      rfl
    let : Module.Free k U := Module.Free.of_basis D.basis
    let : Module.Finite k U := Module.Finite.of_basis D.basis
    have hfinU : Module.finrank k U = D.degree := by
      rw [Module.finrank_eq_card_basis D.basis, Fintype.card_fin]
    have hfinext : Module.finrank k (⋀[k]^D.degree U) = 1 := by
      rw [exteriorPower.finrank_eq, hfinU, Nat.choose_self]
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hfinext
      D.vector_ne_zero (exteriorPower.map D.degree S D.vector)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    calc
      c • exteriorPower.map D.degree f D.vector =
          exteriorPower.map D.degree f (c • D.vector) := by
            rw [LinearMap.map_smul]
      _ = exteriorPower.map D.degree f
          (exteriorPower.map D.degree S D.vector) := by rw [hc]
      _ = exteriorPower.map D.degree (f.comp S) D.vector := by
        rw [exteriorPower.map_comp S f, LinearMap.comp_apply]
      _ = exteriorPower.map D.degree (T.toLinearMap.comp f) D.vector := by
        congr 2
        ext u
        exact hSf u
      _ = exteriorPower.map D.degree T.toLinearMap
          (exteriorPower.map D.degree f D.vector) := by
        rw [exteriorPower.map_comp f T.toLinearMap, LinearMap.comp_apply]

end
/-! Functorial action of the general linear group on an exterior power. -/

section

open scoped ExteriorAlgebra

variable (k : Type u) [Field k]
variable (M : Type v) [AddCommGroup M] [Module k M]

/-- The linear equivalence induced on an exterior power. -/
@[expose]
public noncomputable def exteriorPowerLinearEquiv (n : ℕ) (f : M ≃ₗ[k] M) :
    (⋀[k]^n M) ≃ₗ[k] (⋀[k]^n M) where
  toLinearMap := exteriorPower.map n f.toLinearMap
  invFun := exteriorPower.map n f.symm.toLinearMap
  left_inv x := by
    change exteriorPower.map n f.symm.toLinearMap
      (exteriorPower.map n f.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    have hcomp : f.symm.toLinearMap.comp f.toLinearMap = LinearMap.id := by
      ext y
      simp
    rw [hcomp, exteriorPower.map_id]
    rfl
  right_inv x := by
    change exteriorPower.map n f.toLinearMap
      (exteriorPower.map n f.symm.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    have hcomp : f.toLinearMap.comp f.symm.toLinearMap = LinearMap.id := by
      ext y
      simp
    rw [hcomp, exteriorPower.map_id]
    rfl

/-- The general-linear representation on an exterior power. -/
@[expose]
public noncomputable def exteriorPowerGeneralLinear (n : ℕ) :
    LinearMap.GeneralLinearGroup k M →*
      LinearMap.GeneralLinearGroup k (⋀[k]^n M) where
  toFun f := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (exteriorPowerLinearEquiv k M n f.toLinearEquiv)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    change exteriorPower.map n LinearMap.id x = x
    rw [exteriorPower.map_id]
    rfl
  map_mul' f g := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    change exteriorPower.map n
      (f.toLinearEquiv * g.toLinearEquiv).toLinearMap x =
        exteriorPower.map n f.toLinearEquiv.toLinearMap
          (exteriorPower.map n g.toLinearEquiv.toLinearMap x)
    rw [show (f.toLinearEquiv * g.toLinearEquiv).toLinearMap =
      f.toLinearEquiv.toLinearMap.comp g.toLinearEquiv.toLinearMap from rfl]
    rw [exteriorPower.map_comp, LinearMap.comp_apply]

end

end Theory.AlgebraicGroup

