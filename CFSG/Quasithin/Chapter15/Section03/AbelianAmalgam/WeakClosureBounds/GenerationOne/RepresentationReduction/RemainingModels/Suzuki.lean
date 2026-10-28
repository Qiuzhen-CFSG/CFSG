module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Matrix
public import Theory.SpecificGroups.Suzuki.StandardSubgroups

/-!
# The Suzuki Borel on its natural module

The root element with coordinates (1,0) forces a fixed vector onto the first
coordinate. A torus parameter whose outer weight is nontrivial then kills that
coordinate. The exponent is strictly below the order of the multiplicative
field group for m>0. All elements belong to the concrete Suzuki matrix carrier
and its standard Borel; the section transport uses the literal central quotient.

Source: Aschbacher–Smith, 15.3.65(i), printed p.1152; the root and torus
coordinates are those of Huppert–Blackburn XI.3.1 in StandardSubgroups.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Matrix
open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped Matrix
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels

abbrev suzukiNatural (m : ℕ) := matrixNatural (SuzukiMatrixSubgroup m)

private theorem suzuki_outer_exponent_lt (m : ℕ) (hm : 0 < m) :
    1 + 2 ^ m < Nat.card (BinaryGaloisField (2 * m + 1))ˣ := by
  rw [Nat.card_units, GaloisField.card 2 (2 * m + 1) (by omega)]
  have htwo : 2 ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hbound := Nat.pow_le_pow_right (by decide : 0 < 2) (show m + 2 ≤ 2*m+1 by omega)
  rw [pow_add] at hbound
  norm_num at hbound
  omega

theorem suzuki_borel_fixedSpace_eq_bot (m : ℕ) (hm : 0 < m) :
    fixedSpace (suzukiNatural m) (SuzukiBorelSubgroup m) = ⊥ := by
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic
    (G := (BinaryGaloisField (2 * m + 1))ˣ) (k := 1 + 2 ^ m) (by positivity)
    (suzuki_outer_exponent_lt m hm)
  have ha' : (a : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m) ≠ 1 :=
    fun h => ha (Units.ext (by simpa using h))
  let u : SuzukiMatrixGroup m := ⟨SuzukiRootGL m 1 0,
    suzukiRootClosure_le m (Subgroup.subset_closure ⟨1, 0, rfl⟩)⟩
  have hu : u ∈ SuzukiBorelSubgroup m :=
    (show SuzukiRootClosure m ≤ SuzukiRootClosure m ⊔ SuzukiSplitTorusClosure m
      from le_sup_left) (Subgroup.subset_closure ⟨1, 0, rfl⟩)
  let t : SuzukiMatrixGroup m := ⟨SuzukiTorusGL m a,
    suzukiSplitTorusClosure_le m (Subgroup.subset_closure ⟨a, rfl⟩)⟩
  have ht : t ∈ SuzukiBorelSubgroup m :=
    (show SuzukiSplitTorusClosure m ≤ SuzukiRootClosure m ⊔ SuzukiSplitTorusClosure m
      from le_sup_right) (Subgroup.subset_closure ⟨a, rfl⟩)
  apply bot_unique
  intro v hv
  have he := hv ⟨u, hu⟩
  change (SuzukiRootMatrix m 1 0).mulVec v = v at he
  have h3 : v 3 = 0 := by
    have h := congrFun he 2
    simpa [SuzukiRootMatrix, mulVec, dotProduct, Fin.sum_univ_four] using h
  have h2 : v 2 = 0 := by
    have h := congrFun he 1
    simpa [SuzukiRootMatrix, mulVec, dotProduct, Fin.sum_univ_four, h3] using h
  have h1 : v 1 = 0 := by
    have h := congrFun he 0
    simpa [SuzukiRootMatrix, mulVec, dotProduct, Fin.sum_univ_four, h3, h2] using h
  have htfix := hv ⟨t, ht⟩
  change (SuzukiTorusMatrix m a).mulVec v = v at htfix
  have h0 : v 0 = 0 := zero_of_scalar_fixed ha' (by
    simpa [SuzukiTorusMatrix, mulVec, dotProduct, Fin.sum_univ_four] using congrFun htfix 0)
  ext i
  fin_cases i <;> assumption

/-- Transport to I/C_I(K) using the displayed group map, Borel image and
actual equivariant linear identification. The extension I need not split. -/
theorem suzuki_centralQuotient_fixed (m : ℕ) (hm : 0 < m)
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (φ : K →* SuzukiMatrixGroup m)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      (suzukiNatural m) (φ g) (e v))
    (hB : (B.subgroupOf K).map φ = SuzukiBorelSubgroup m) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K := by
  apply inf_fixedSpace_le_of_centralQuotient ρ K B I hI
  exact fixedSpace_eq_bot_of_equivariant _ (suzukiNatural m) φ e he _ _ hB
    (suzuki_borel_fixedSpace_eq_bot m hm)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels
