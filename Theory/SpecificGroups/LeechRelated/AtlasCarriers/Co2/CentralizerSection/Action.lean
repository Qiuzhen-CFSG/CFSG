module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection.Generation

/-!
# The surjective symplectic block action of a Co2 centralizing subgroup

Compatibility with the surjective vector coloring is closed under products
and inverses and determines a unique symplectic matrix. The generator
identities therefore give a homomorphism on their actual closure. The two
matrix images generate Sp6(2), so this homomorphism is onto.

Source: GLS3 Table 5.3k and ATLAS Co2G1-p2300B0. This construction supplies
the simple centralizer section used in Aschbacher--Smith A.2.19.
-/

public section
namespace Sporadic.LeechRelated.Co2.CentralizerSection
open Matrix.PSp4Three

/-- Equivariance of a carrier permutation through a symplectic matrix. -/
@[expose] def Compatible (g : Carrier) (s : S) : Prop :=
  ∀ x, color (inclusion g x) = s • color x

private theorem compatible_one : Compatible 1 1 := by
  intro x
  simp

private theorem compatible_mul {g h : Carrier} {s t : S}
    (hg : Compatible g s) (hh : Compatible h t) : Compatible (g * h) (s * t) := by
  intro x
  rw [map_mul, Equiv.Perm.mul_apply, hg, hh, mul_smul]

private theorem compatible_inv {g : Carrier} {s : S}
    (h : Compatible g s) : Compatible g⁻¹ s⁻¹ := by
  intro x
  have hh := h (inclusion g⁻¹ x)
  have hc : inclusion g (inclusion g⁻¹ x) = x := by
    rw [map_inv]
    exact (inclusion g).apply_symm_apply x
  rw [hc] at hh
  exact eq_inv_smul_iff.mpr hh.symm

private theorem compatible_unique {g : Carrier} {s t : S}
    (hs : Compatible g s) (ht : Compatible g t) : s = t := by
  apply ext_action
  intro v
  obtain ⟨x, rfl⟩ := color_surjective v
  exact (hs x).symm.trans (ht x)

private def liftGroup : Subgroup Carrier where
  carrier := {g | ∃ s : S, Compatible g s}
  one_mem' := ⟨1, compatible_one⟩
  mul_mem' := by
    rintro g h ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s * t, compatible_mul hs ht⟩
  inv_mem' := by
    rintro g ⟨s, hs⟩
    exact ⟨s⁻¹, compatible_inv hs⟩

private theorem numerator_le_lift : numerator ≤ liftGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨matrixGenerator i, color_localGenerator i⟩

private theorem exists_matrix (g : numerator) : ∃ s : S, Compatible g.val s :=
  numerator_le_lift g.property

/-- The actual quotient action on the six-dimensional binary symplectic space. -/
noncomputable def symplecticMap : numerator →* S where
  toFun g := Classical.choose (exists_matrix g)
  map_one' := compatible_unique (Classical.choose_spec (exists_matrix 1)) compatible_one
  map_mul' g h := compatible_unique (Classical.choose_spec (exists_matrix (g * h)))
    (compatible_mul (Classical.choose_spec (exists_matrix g))
      (Classical.choose_spec (exists_matrix h)))

theorem symplecticMap_spec (g : numerator) : Compatible g.val (symplecticMap g) :=
  Classical.choose_spec (exists_matrix g)

/-- The literal generators map to the two certified matrices. -/
theorem symplecticMap_generator (i : Fin 2) :
    symplecticMap (numeratorGenerator i) = matrixGenerator i :=
  compatible_unique (symplecticMap_spec _) (color_localGenerator i)

theorem symplecticMap_surjective : Function.Surjective symplecticMap := by
  apply MonoidHom.range_eq_top.mp
  apply matrix_generators_generate
  intro i
  exact ⟨numeratorGenerator i, symplecticMap_generator i⟩

end Sporadic.LeechRelated.Co2.CentralizerSection
