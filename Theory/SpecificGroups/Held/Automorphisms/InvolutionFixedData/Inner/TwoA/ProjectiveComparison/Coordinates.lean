module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Explicit projective coordinates for the Held 2A comparison

The 21 normalized vectors enumerate the projective plane over the computable
quadratic field F₂[z], z² = z + 1. The existing finite-field equivalence and
coefficientwise projective transport identify its matrix PSL with PSL₃(4) over
`GaloisField 2 2`. Two determinant-one matrices act by the permutations below;
all vector comparisons are checked by the Lean kernel.

The point labels and matrices come from the retained Held degree-2058 ATLAS
representation and the discovery in `Scratch/HeldTwoACover/discovery.json` of
the parent cover task. The matrices here are the inverse transposes of the
right-row lifts, in the left-column convention. No Held membership or orbit
exhaustion is asserted in this module. Source: GLS3 Table 5.3p and pp.260–261;
original ATLAS data and attribution: `Held/Model/Source/README.md`.
-/

@[expose] public section

namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison
open Matrix
abbrev F := Representation.SL2FourNatural.F
abbrev PG := Projectivization F (Fin 3 → F)
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) F
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F
noncomputable def modelEquiv : PSL ≃* Matrix.PSL3Four.PSL :=
  Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv

def z : F := ⟨0, 1⟩
theorem z_sq : z ^ 2 = z + 1 := by decide +kernel

def vector : Fin 21 → Fin 3 → F :=
  ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, z], ![0, 1, z + 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, z], ![1, 0, z + 1], ![1, 1, 0], ![1, 1, 1], ![1, 1, z], ![1, 1, z + 1], ![1, z, 0], ![1, z, 1], ![1, z, z], ![1, z, z + 1], ![1, z + 1, 0], ![1, z + 1, 1], ![1, z + 1, z], ![1, z + 1, z + 1]]

theorem vector_ne_zero : ∀ i, vector i ≠ 0 := by decide +kernel

set_option maxRecDepth 2048 in
theorem vector_separates : ∀ (i j : Fin 21) (c : F),
    c • vector j = vector i → i = j := by decide +kernel

noncomputable def point (i : Fin 21) : PG :=
  Projectivization.mk F (vector i) (vector_ne_zero i)

theorem point_injective : Function.Injective point := by
  intro i j h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp h
  exact vector_separates i j c hc

theorem card_PG : Nat.card PG = 21 := by
  rw [Atlas.card_projectiveSpace]
  norm_num [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]

noncomputable def pointEquiv : Fin 21 ≃ PG :=
  Equiv.ofBijective point ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨point_injective, by simp [card_PG]⟩)

def matrixA : SL := ⟨![![z, 0, z + 1], ![z, 0, 1], ![z, z, z]], by decide +kernel⟩

def permA : Equiv.Perm (Fin 21) where
  toFun := ![16, 0, 13, 14, 15, 10, 17, 7, 4, 9, 19, 6, 2, 12, 20, 8, 1, 11, 18, 5, 3]
  invFun := ![1, 16, 12, 20, 8, 19, 11, 7, 15, 9, 5, 17, 13, 2, 3, 4, 0, 6, 18, 10, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem matrixA_vector : ∀ i : Fin 21, ∃ c : F,
    c • vector (permA i) = matrixA.val *ᵥ vector i := by decide +kernel

noncomputable def projectiveA : PSL := QuotientGroup.mk' _ matrixA

theorem projectiveA_point (i : Fin 21) :
    projectiveA • pointEquiv i = pointEquiv (permA i) := by
  change matrixA • point i = point (permA i)
  rw [point, Projectivization.smul_mk]
  exact (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr (matrixA_vector i)

def matrixB : SL := ⟨![![z + 1, 0, 1], ![1, z + 1, z + 1], ![1, 0, 1]], by decide +kernel⟩

def permB : Equiv.Perm (Fin 21) where
  toFun := ![18, 1, 6, 10, 14, 15, 9, 8, 4, 19, 17, 20, 0, 7, 13, 12, 2, 11, 5, 16, 3]
  invFun := ![12, 1, 16, 20, 8, 18, 2, 13, 7, 6, 3, 17, 15, 14, 4, 5, 19, 10, 0, 9, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem matrixB_vector : ∀ i : Fin 21, ∃ c : F,
    c • vector (permB i) = matrixB.val *ᵥ vector i := by decide +kernel

noncomputable def projectiveB : PSL := QuotientGroup.mk' _ matrixB

theorem projectiveB_point (i : Fin 21) :
    projectiveB • pointEquiv i = pointEquiv (permB i) := by
  change matrixB • point i = point (permB i)
  rw [point, Projectivization.smul_mk]
  exact (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr (matrixB_vector i)

def pointLabel : Fin 21 → Fin 2058 :=
  ![25, 230, 365, 1605, 521, 827, 476, 1490, 1334, 1826, 414, 261, 1855, 1003, 811, 275, 1259, 993, 1917, 30, 1441]

theorem pointLabel_injective : Function.Injective pointLabel := by decide +kernel

theorem pointLabel_zero : pointLabel 0 = 25 := rfl

noncomputable def label (p : PG) : Fin 2058 := pointLabel (pointEquiv.symm p)

theorem label_pointEquiv (i : Fin 21) : label (pointEquiv i) = pointLabel i := by
  simp [label]

theorem label_injective : Function.Injective label :=
  pointLabel_injective.comp pointEquiv.symm.injective

end Held.InvolutionFixedData.TwoA.ProjectiveComparison
