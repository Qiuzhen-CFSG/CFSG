module

public import Theory.Representation.FirstCohomology
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# First cohomology under scalar restriction and isomorphism

Scalar restriction leaves both crossed homomorphisms and principal crossed
homomorphisms unchanged. Their quotient therefore commutes with scalar
restriction, and its dimension satisfies the usual tower law. An intertwining
pair of group and vector-space isomorphisms likewise transports the quotient.

These elementary identifications allow calculations in matrix coordinates over
an extension field to apply to identified modules over the prime field. In
particular they preserve the field convention in Aschbacher--Smith, *The
Classification of Quasithin Groups*, Lemma I.1.6, printed p.408.
-/

@[expose] public section

namespace Representation
variable {k K G V : Type*} [CommRing k] [CommRing K] [Algebra k K]
  [Group G] [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]

/-- Restrict the coefficient ring without changing the group action. -/
def restrictScalars (ρ : Representation K G V) : Representation k G V where
  toFun g := (ρ g).restrictScalars k
  map_one' := by ext v; exact congrArg (fun f : Module.End K V => f v) ρ.map_one
  map_mul' g h := by ext v; exact congrArg (fun f : Module.End K V => f v) (ρ.map_mul g h)

namespace OneCohomology

/-- Scalar restriction leaves the crossed homomorphisms unchanged. -/
def cocyclesRestrictEquiv (ρ : Representation K G V) :
    cocycles (restrictScalars (k := k) ρ) ≃ₗ[k] cocycles ρ where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- First cohomology commutes with restriction of the coefficient ring. -/
def H1RestrictEquiv (ρ : Representation K G V) :
    H1 (restrictScalars (k := k) ρ) ≃ₗ[k] H1 ρ :=
  (Submodule.Quotient.equiv (principal (restrictScalars (k := k) ρ)).range
    ((principal ρ).range.restrictScalars k) (cocyclesRestrictEquiv ρ) (by
      ext f
      constructor
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        exact ⟨v, rfl⟩
      · rintro ⟨v, rfl⟩
        exact ⟨principal (restrictScalars (k := k) ρ) v, ⟨v, rfl⟩, rfl⟩)).trans
    (Submodule.Quotient.restrictScalarsEquiv k (principal ρ).range)

end OneCohomology
end Representation


namespace Representation.OneCohomology
section Congr
variable {k G H V W : Type*} [CommRing k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k H W)
  (eG : G ≃* H) (eV : V ≃ₗ[k] W)
  (he : ∀ g v, eV (ρ g v) = σ (eG g) (eV v))

/-- Transport crossed homomorphisms along intertwining group and module isomorphisms. -/
def cocyclesCongr : cocycles ρ ≃ₗ[k] cocycles σ where
  toFun f := ⟨fun h => eV (f.val (eG.symm h)), by
    intro g h
    dsimp only
    rw [map_mul, f.property (eG.symm g) (eG.symm h), map_add, he, eG.apply_symm_apply]⟩
  invFun f := ⟨fun g => eV.symm (f.val (eG g)), by
    intro g h
    apply eV.injective
    simp only [map_add, eV.apply_symm_apply, he]
    rw [map_mul]
    exact f.property (eG g) (eG h)⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' f t := by ext g; exact eV.map_add _ _
  map_smul' r f := by ext g; exact eV.map_smul r _

/-- The transport sends a principal cocycle to the principal cocycle of the image vector. -/
lemma cocyclesCongr_principal (v : V) :
    cocyclesCongr ρ σ eG eV he (principal ρ v) = principal σ (eV v) := by
  ext h
  change eV (ρ (eG.symm h) v - v) = σ h (eV v) - eV v
  rw [map_sub, he, eG.apply_symm_apply]

/-- Intertwining group and module isomorphisms induce an isomorphism on first cohomology. -/
def H1Congr : H1 ρ ≃ₗ[k] H1 σ :=
  Submodule.Quotient.equiv (principal ρ).range (principal σ).range
    (cocyclesCongr ρ σ eG eV he) (by
      ext f
      constructor
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        exact ⟨eV v, (cocyclesCongr_principal ρ σ eG eV he v).symm⟩
      · rintro ⟨w, rfl⟩
        refine ⟨principal ρ (eV.symm w), ⟨eV.symm w, rfl⟩, ?_⟩
        exact (cocyclesCongr_principal ρ σ eG eV he (eV.symm w)).trans
          (congrArg (principal σ) (eV.apply_symm_apply w)))
end Congr

section Dimension
variable {k K G V : Type*} [Field k] [Field K] [Algebra k K]
  [Group G] [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]

/-- The dimension over the smaller field is multiplied by the extension degree. -/
lemma finrank_restrictScalars (ρ : Representation K G V) :
    Module.finrank k (H1 (restrictScalars (k := k) ρ)) =
      Module.finrank k K * Module.finrank K (H1 ρ) := by
  rw [(H1RestrictEquiv ρ).finrank_eq, Module.finrank_mul_finrank]
end Dimension
end Representation.OneCohomology
