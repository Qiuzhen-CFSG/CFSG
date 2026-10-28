module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.CentralEmbedding.PermutationCertificates

/-!
# Three central elements in the literal generated subgroup

The matrix and permutation certificates identify the three signed words with
explicit triples. Commutation with the two generators extends to their subgroup
closure. The scalar third coordinate is killed by the actual projective quotient.
Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.CentralWords

theorem fourA_ambient : fourA x y = ((1, permB), 1) :=
  Prod.ext (Prod.ext fourA_perm1 fourA_perm2) fourA_matrix

theorem fourB_ambient : fourB x y = ((permA, permB), 1) :=
  Prod.ext (Prod.ext fourB_perm1 fourB_perm2) fourB_matrix

theorem three_ambient : three x y = ((1, 1), scalarZ) :=
  Prod.ext (Prod.ext three_perm1 three_perm2) three_matrix

/-- The first order-four word from the source data. -/
def elementA : Group := ⟨((1, permB), 1), by
  rw [← fourA_ambient]
  exact (fourA generatorX generatorY).property⟩

/-- The second order-four word from the source data. -/
def elementB : Group := ⟨((permA, permB), 1), by
  rw [← fourB_ambient]
  exact (fourB generatorX generatorY).property⟩

/-- The order-three word from the source data. -/
def elementC : Group := ⟨((1, 1), scalarZ), by
  rw [← three_ambient]
  exact (three generatorX generatorY).property⟩

theorem elementA_word : elementA = fourA generatorX generatorY :=
  Subtype.ext fourA_ambient.symm

theorem elementB_word : elementB = fourB generatorX generatorY :=
  Subtype.ext fourB_ambient.symm

theorem elementC_word : elementC = three generatorX generatorY :=
  Subtype.ext three_ambient.symm

theorem elementA_fourth : elementA ^ 4 = 1 := by
  apply Subtype.ext
  exact Prod.ext (Prod.ext (one_pow 4) permB_fourth) (one_pow 4)

theorem elementB_fourth : elementB ^ 4 = 1 := by
  apply Subtype.ext
  exact Prod.ext (Prod.ext permA_fourth permB_fourth) (one_pow 4)

theorem scalarZ_cube : scalarZ ^ 3 = 1 := by
  apply Subtype.ext
  decide +kernel

theorem elementC_cube : elementC ^ 3 = 1 := by
  apply Subtype.ext
  exact Prod.ext (Prod.ext (one_pow 3) (one_pow 3)) scalarZ_cube

theorem scalarZ_central : scalarZ ∈ Subgroup.center SL := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  exact ⟨z, by decide +kernel, by decide +kernel⟩

private theorem central_of_generators (g : Group)
    (hx : Commute (g : Ambient) x) (hy : Commute (g : Ambient) y) :
    g ∈ Subgroup.center Group := by
  have h : (g : Ambient) ∈ Subgroup.centralizer (subgroup : Set Ambient) := by
    rw [subgroup, Subgroup.centralizer_closure]
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact hx.eq.symm
    · have he : t = y := Set.mem_singleton_iff.mp ht
      subst t
      exact hy.eq.symm
  apply Subgroup.mem_center_iff.mpr
  intro t
  exact Subtype.ext (h t t.property)

theorem elementA_central : elementA ∈ Subgroup.center Group := by
  apply central_of_generators
  · exact Prod.ext (Prod.ext (one_mul _ |>.trans (mul_one _).symm) permB_x.eq)
      (one_mul _ |>.trans (mul_one _).symm)
  · exact Prod.ext (Prod.ext (one_mul _ |>.trans (mul_one _).symm) permB_y.eq)
      (one_mul _ |>.trans (mul_one _).symm)

theorem elementB_central : elementB ∈ Subgroup.center Group := by
  apply central_of_generators
  · exact Prod.ext (Prod.ext permA_x.eq permB_x.eq)
      (one_mul _ |>.trans (mul_one _).symm)
  · exact Prod.ext (Prod.ext permA_y.eq permB_y.eq)
      (one_mul _ |>.trans (mul_one _).symm)

theorem elementC_central : elementC ∈ Subgroup.center Group := by
  apply central_of_generators
  · exact Prod.ext (Prod.ext (one_mul _ |>.trans (mul_one _).symm)
      (one_mul _ |>.trans (mul_one _).symm))
      (Subgroup.mem_center_iff.mp scalarZ_central matrixX).symm
  · exact Prod.ext (Prod.ext (one_mul _ |>.trans (mul_one _).symm)
      (one_mul _ |>.trans (mul_one _).symm))
      (Subgroup.mem_center_iff.mp scalarZ_central matrixY).symm

theorem projection_elementA : projection elementA = 1 := by
  change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
    ((QuotientGroup.mk' (Subgroup.center SL)) 1) = 1
  simp only [map_one]

theorem projection_elementB : projection elementB = 1 := by
  change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
    ((QuotientGroup.mk' (Subgroup.center SL)) 1) = 1
  simp only [map_one]

theorem projection_elementC : projection elementC = 1 := by
  have hs : (QuotientGroup.mk' (Subgroup.center SL)) scalarZ = 1 :=
    (QuotientGroup.eq_one_iff scalarZ).mpr scalarZ_central
  change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
    ((QuotientGroup.mk' (Subgroup.center SL)) scalarZ) = 1
  rw [hs, map_one]

end Matrix.PSL3.ExceptionalFourCover.KernelModel.CentralWords
