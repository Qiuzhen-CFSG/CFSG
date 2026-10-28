module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Interface
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.SquareZero

/-!
# Assembly of the cubic image/kernel flag from concrete coordinates

The fixed matrix identities and an actual equivariant coordinate comparison
produce a rank-21 square-zero intertwiner on the original induced module.
Its image and kernel give the literal quotient dimensions 21, 84, 21.
Commutation with the two specified generating actors is extended to the
whole group by a subgroup argument.

The two independent contracts in `ModelFlag.Interface` remain explicit here.
`ModelFlag.Realization` discharges them and exports the unconditional
`model_flags`; `ModelFlag.Quotients` supplies equivariant coordinates for its
literal quotients. Simplicity is reserved for the separate consumer.
Source: Guralnick–Malle, Proposition 4.3, p.10; Aschbacher–Smith K.2, p.453.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag

theorem intertwines_of_generators {K G V I : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (a : I → G) (ha : Subgroup.closure (Set.range a) = ⊤)
    (f : Module.End K V) (hf : ∀ i v, f (ρ (a i) v) = ρ (a i) (f v)) :
    ∀ g v, f (ρ g v) = ρ g (f v) := by
  let S : Subgroup G := {
    carrier := {g | ∀ v, f (ρ g v) = ρ g (f v)}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro g h hg hh v
      simp only [map_mul, Module.End.mul_apply]
      rw [hg, hh]
    inv_mem' := by
      intro g hg v
      apply (ρ.apply_bijective g).injective
      rw [ρ.self_inv_apply, ← hg, ρ.self_inv_apply] }
  have hS : Subgroup.closure (Set.range a) ≤ S := by
    apply (Subgroup.closure_le (k := Set.range a) (K := S)).mpr
    rintro g ⟨i, rfl⟩
    exact hf i
  rw [ha] at hS
  intro g
  exact hS (Subgroup.mem_top g)

universe v
noncomputable def Coordinates.intertwiner {K : Type v} [Field K] [CharP K 2]
    {χ : standardBorel modelForm →* Kˣ} (c : Coordinates χ) (h : MatrixRelations.{v}) :
    (ind (standardBorel modelForm).subtype (scalarCharacter χ)).IntertwiningMap
      (ind (standardBorel modelForm).subtype (scalarCharacter χ)) := by
  let f := c.equiv.symm.conj (nilpotentMatrix c.z c.quadratic).toLin'
  have hf : ∀ g v, f (ind (standardBorel modelForm).subtype (scalarCharacter χ) g v) =
      ind (standardBorel modelForm).subtype (scalarCharacter χ) g (f v) := by
    apply intertwines_of_generators _ c.actor c.generates f
    intro i v
    apply c.equiv.injective
    change c.equiv (c.equiv.symm ((nilpotentMatrix c.z c.quadratic).mulVec
      (c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ) (c.actor i) v)))) =
      c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ) (c.actor i)
        (c.equiv.symm ((nilpotentMatrix c.z c.quadratic).mulVec (c.equiv v))))
    rw [c.equiv.apply_symm_apply, c.action, c.action, c.equiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, h.commutes K, Matrix.mulVec_mulVec]
  exact ⟨f, fun g => LinearMap.ext (hf g)⟩

@[simp] theorem Coordinates.intertwiner_equiv {K : Type v} [Field K] [CharP K 2]
    {χ : standardBorel modelForm →* Kˣ} (c : Coordinates χ) (h : MatrixRelations.{v})
    (v : IndV (standardBorel modelForm).subtype (scalarCharacter χ)) :
    c.equiv (c.intertwiner h v) = (nilpotentMatrix c.z c.quadratic).mulVec (c.equiv v) :=
  c.equiv.apply_symm_apply _

noncomputable def Coordinates.flag {K : Type v} [Field K] [CharP K 2]
    {χ : standardBorel modelForm →* Kˣ} (c : Coordinates χ) (h : MatrixRelations.{v}) :
    ThreeStepFlag (ind (standardBorel modelForm).subtype (scalarCharacter χ)) := by
  letI : FiniteDimensional K (IndV (standardBorel modelForm).subtype (scalarCharacter χ)) :=
    c.equiv.symm.finiteDimensional
  apply imageKernelFlag (c.intertwiner h)
  · intro v
    apply c.equiv.injective
    rw [c.intertwiner_equiv, c.intertwiner_equiv, Matrix.mulVec_mulVec,
      h.square_zero K, Matrix.zero_mulVec, map_zero]
  · rw [c.equiv.finrank_eq]
    simp
  · exact (conjugateRangeEquiv c.equiv (nilpotentMatrix c.z c.quadratic).toLin').finrank_eq.trans
      (h.rank K c.z c.quadratic)

noncomputable def model_flags_of_coordinates_and_relations
    (hc : ModelCoordinates.{v}) (h : MatrixRelations.{v}) : ModelFlags.{v} := by
  intro K _ _ _ χ hn hcub
  exact (Classical.choice (hc K χ hn hcub)).flag h

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
