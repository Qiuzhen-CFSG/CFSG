module

public import Theory.SpecificGroups.SymplecticFour.LocalFactors
public import Theory.GroupTheory.Amalgam.RankTwo
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.Binary
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.Blocks

/-!
# The concrete symplectic four-space flag amalgam

The two vertices are the stabilizers of the incident isotropic line and plane
in the actual symplectic matrix group. The overlap retains the whole flag
stabilizer. Both inclusion maps land in the same ambient matrix group.
The local factors are determinant kernels, defined separately from the vertices.
Their joins with the Borel give the source amalgam `(L₁B, B, L₂B)`, compatibly
isomorphic to the flag amalgam. Their intersection is an actual Sylow subgroup
over a field of order `2ⁿ`. For `n > 1` both factors are genuine natural L₂-blocks;
for `n = 1` the proved join equalities give the actual `LᵢS ≃ C₂ × S₄` models.

The public imports also supply the relative solvable-residual and embedded
two-core identities, the local SL₂ automorphism actions with faithful field
contribution, and binary diagram-preserving extension rigidity. These use
normality inside the local overgroups and compare cores in a common ambient
group. No extension-elimination conclusion is assumed in the local alternative.

Source: Aschbacher--Smith F.1.12(I)(2) and the local facts in its proof, printed
pp.262--264. Recognition of an arbitrary source amalgam and elimination of its
outer extension remain with the parent F.1.12 assembly.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour

open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour

variable (F : Type*) [Field F]

/-- The actual point/plane inclusion amalgam, with the whole flag overlap. -/
def amalgam : RankTwoAmalgam (pointParabolic (F := F)) (borel (F := F))
    (planeParabolic (F := F)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

variable {F}

theorem overlap_eq :
    pointParabolic (F := F) ⊓ planeParabolic = borel := rfl

theorem left_injective : Function.Injective (amalgam F).left :=
  RankTwoAmalgam.ofSubgroups_left_injective _ _ _ _ _

theorem right_injective : Function.Injective (amalgam F).right :=
  RankTwoAmalgam.ofSubgroups_right_injective _ _ _ _ _

/-- The two overlap maps are compatible with the ambient matrix embeddings. -/
theorem overlap_compatible (b : borel (F := F)) :
    (pointParabolic (F := F)).subtype ((amalgam F).left b) =
      (planeParabolic (F := F)).subtype ((amalgam F).right b) := rfl

/-- This equality justifies replacing L₁S by P₁ in the binary calculation. -/
theorem pointLocal_sup_of_card_two [Finite F] (hF : Nat.card F = 2)
    (S : Subgroup (Sp F)) (hS : S ≤ borel) :
    pointLocal ⊔ S = pointParabolic := by
  rw [pointLocal_eq_of_card_two hF]
  exact sup_eq_left.mpr (hS.trans inf_le_left)

/-- The analogous binary equality for the plane local factor. -/
theorem planeLocal_sup_of_card_two [Finite F] (hF : Nat.card F = 2)
    (S : Subgroup (Sp F)) (hS : S ≤ borel) :
    planeLocal ⊔ S = planeParabolic := by
  rw [planeLocal_eq_of_card_two hF]
  exact sup_eq_left.mpr (hS.trans inf_le_right)

/-- The source triple, retaining the joins with the whole Borel. -/
def localAmalgam : RankTwoAmalgam
    (pointLocal (F := F) ⊔ borel : Subgroup (Sp F)) (borel (F := F))
    (planeLocal (F := F) ⊔ borel : Subgroup (Sp F)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ le_sup_right le_sup_right

/-- Both vertex identifications are subgroup equalities in the same matrix
group, so they commute with the overlap maps. -/
def localAmalgamIso : RankTwoAmalgam.Iso (localAmalgam (F := F)) (amalgam F) where
  left := MulEquiv.subgroupCongr pointParabolic_eq_pointLocal_sup_borel.symm
  middle := MulEquiv.refl _
  right := MulEquiv.subgroupCongr planeParabolic_eq_planeLocal_sup_borel.symm
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- Binary models for the literal joins, using the previously proved equalities
with the actual parabolics before applying their matrix product models. -/
def pointLocalSupEquivProd [Finite F] (hF : Nat.card F = 2)
    (S : Subgroup (Sp F)) (hS : S ≤ borel) :
    (pointLocal ⊔ S : Subgroup (Sp F)) ≃* Binary.LocalProduct :=
  (MulEquiv.subgroupCongr (pointLocal_sup_of_card_two hF S hS)).trans
    (Binary.pointParabolicEquivProd hF)

/-- The corresponding binary model for the plane-local join. -/
def planeLocalSupEquivProd [Finite F] (hF : Nat.card F = 2)
    (S : Subgroup (Sp F)) (hS : S ≤ borel) :
    (planeLocal ⊔ S : Subgroup (Sp F)) ≃* Binary.LocalProduct :=
  (MulEquiv.subgroupCongr (planeLocal_sup_of_card_two hF S hS)).trans
    (Binary.planeParabolicEquivProd hF)

section Sylow
variable [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)

/-- The concrete Sylow subgroup is precisely the intersection of the separate
local factors, rather than the whole flag overlap. -/
theorem localFactors_inf_eq_sylow :
    pointLocal ⊓ planeLocal = (unipotentSylow hF hn : Subgroup (Sp F)) := rfl

theorem sylow_le_pointLocal :
    (unipotentSylow hF hn : Subgroup (Sp F)) ≤ pointLocal := inf_le_left

theorem sylow_le_planeLocal :
    (unipotentSylow hF hn : Subgroup (Sp F)) ≤ planeLocal := inf_le_right

/-- The whole overlap is the Sylow normalizer. -/
theorem overlap_eq_normalizer_sylow :
    borel (F := F) = Subgroup.normalizer
      ((unipotentSylow hF hn : Subgroup (Sp F)) : Set (Sp F)) :=
  borel_eq_normalizer_unipotent

/-- Geometry and generation of the concrete source triple, with its chosen
Sylow subgroup and its two proper, distinct vertices. -/
theorem flag_structure :
    pointLocal ⊓ planeLocal = (unipotentSylow hF hn : Subgroup (Sp F)) ∧
    pointParabolic ⊓ planeParabolic = borel (F := F) ∧
    borel (F := F) = Subgroup.normalizer
      ((unipotentSylow hF hn : Subgroup (Sp F)) : Set (Sp F)) ∧
    pointParabolic = pointLocal ⊔ borel (F := F) ∧
    planeParabolic = planeLocal ⊔ borel (F := F) ∧
    pointParabolic (F := F) ≠ planeParabolic ∧
    pointParabolic (F := F) ≠ ⊤ ∧ planeParabolic (F := F) ≠ ⊤ ∧
    pointParabolic (F := F) ⊔ planeParabolic = ⊤ :=
  ⟨localFactors_inf_eq_sylow hF hn, overlap_eq, overlap_eq_normalizer_sylow hF hn,
    pointParabolic_eq_pointLocal_sup_borel, planeParabolic_eq_planeLocal_sup_borel,
    pointParabolic_ne_planeParabolic, pointParabolic_ne_top, planeParabolic_ne_top,
    parabolics_sup_eq_top⟩

end Sylow

section LocalStructure
variable {F : Type} [Field F] [Finite F] {n : ℕ}

/-- The concrete local alternative of F.1.12(I)(2), with no assumed block,
product model, characteristic, or Sylow witness. The binary isomorphisms have
domain `LᵢS` for the actual Sylow subgroup. -/
theorem local_alternative (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    (ChapterC.IsL2EvenBlock (pointLocal (F := F)) n ∧
      ChapterC.IsL2EvenBlock (planeLocal (F := F)) n) ∨
    (Nat.card F = 2 ∧
      Nonempty ((pointLocal ⊔ (unipotentSylow hF hn : Subgroup (Sp F)) :
        Subgroup (Sp F)) ≃* Binary.LocalProduct) ∧
      Nonempty ((planeLocal ⊔ (unipotentSylow hF hn : Subgroup (Sp F)) :
        Subgroup (Sp F)) ≃* Binary.LocalProduct)) := by
  by_cases h : n = 1
  · have htwo : Nat.card F = 2 := by simpa only [h, pow_one] using hF
    exact Or.inr ⟨htwo,
      ⟨pointLocalSupEquivProd htwo _ unipotent_le_borel⟩,
      ⟨planeLocalSupEquivProd htwo _ unipotent_le_borel⟩⟩
  · have hgt : 1 < n := by omega
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact Or.inl ⟨pointLocal_isL2EvenBlock hF hgt, planeLocal_isL2EvenBlock hF hgt⟩

/-- The nonbinary residual assertions used on p.264, together with containment
of the standard Sylow subgroup in both factors. The residuals of the vertices
are compared inside the respective parabolics. -/
theorem nonbinary_residuals (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    Subgroup.solvableResidual (pointLocal (F := F)) = ⊤ ∧
    Subgroup.solvableResidual (planeLocal (F := F)) = ⊤ ∧
    Subgroup.solvableResidual (pointParabolic (F := F)) =
      (pointLocal (F := F)).subgroupOf pointParabolic ∧
    Subgroup.solvableResidual (planeParabolic (F := F)) =
      (planeLocal (F := F)).subgroupOf planeParabolic ∧
    (unipotentSylow hF hn.le : Subgroup (Sp F)) ≤ pointLocal ∧
    (unipotentSylow hF hn.le : Subgroup (Sp F)) ≤ planeLocal := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨pointLocal_solvableResidual_eq_top hF hn, planeLocal_solvableResidual_eq_top hF hn,
    pointParabolic_solvableResidual_relative hF hn, planeParabolic_solvableResidual_relative hF hn,
    sylow_le_pointLocal hF hn.le, sylow_le_planeLocal hF hn.le⟩

end LocalStructure

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour
