module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Matrix
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Basic

/-!
# The full SU₃ torus on the natural module

The matrix field has q² elements and conjugation is the q-power map. A unit
whose (q−1)-st power is not one gives three diagonal weights different from one.
In particular the middle weight uses the full extension-field torus. The action
and Borel live on the actual special unitary cover. The root–torus join is the
standard Borel identified by Chapter F's standard_su_borel_data.

No natural action of PSU₃ is asserted. Any local identification must intertwine
an actual homomorphism to SU₃ with the literal quotient representation.
Source: Aschbacher–Smith, 15.3.65(i), printed p.1152; Huppert II.10.12.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Matrix
open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped Matrix
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
theorem unitary_torus_parameters (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ a : Fˣ, (a : F) ≠ 1 ∧ J.conj (a : F) ≠ 1 ∧
      J.conj (a : F) * (a : F)⁻¹ ≠ 1 := by
  have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have hexp : 2 ^ n - 1 < Nat.card Fˣ := by
    rw [Nat.card_units, hcard]
    have hs : 2 ^ n < (2 ^ n) ^ 2 := by nlinarith
    omega
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (by omega : (2 ^ n - 1 : ℕ) ≠ 0) hexp
  have ha' : (a : F) ^ (2 ^ n - 1) ≠ 1 :=
    fun h => ha (Units.ext (by simpa using h))
  have ha1 : (a : F) ≠ 1 := by intro h; exact ha' (by rw [h, one_pow])
  refine ⟨a, ha1, fun h => ha1 (J.conj.injective (h.trans (map_one J.conj).symm)), ?_⟩
  rw [hconj, show 2 ^ n = (2 ^ n - 1) + 1 by omega, pow_succ]
  simpa [mul_assoc, a.ne_zero] using ha'

/-- The binary natural action of the actual special unitary matrices. -/
def unitaryNatural (J : HermitianForm 3 F) := matrixNatural J.specialSubgroup

/-- The standard root–torus Borel, on SU₃ before taking a scalar quotient. -/
def unitaryBorel (J : HermitianForm 3 F)
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :=
  suRoot J hstandard ⊔ suTorus J hstandard

/-- The full extension-field torus eliminates the middle coordinate as well. -/
theorem unitary_borel_fixedSpace_eq_bot (J : HermitianForm 3 F)
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    fixedSpace (unitaryNatural J) (unitaryBorel J hstandard) = ⊥ := by
  obtain ⟨a, ha, hca, hmid⟩ := unitary_torus_parameters J n hn hcard hconj
  apply bot_unique
  intro v hv
  have ht : hermitianTorusSU J hstandard a ∈ unitaryBorel J hstandard :=
    (show suTorus J hstandard ≤ unitaryBorel J hstandard from le_sup_right) ⟨a, rfl⟩
  have he := hv ⟨hermitianTorusSU J hstandard a, ht⟩
  change (hermitianTorusMatrix J a).mulVec v = v at he
  have h0 : v 0 = 0 := zero_of_scalar_fixed (inv_ne_one.mpr hca) (by
    simpa [hermitianTorusMatrix, mulVec, dotProduct, Fin.sum_univ_three] using congrFun he 0)
  have h1 : v 1 = 0 := zero_of_scalar_fixed hmid (by
    simpa [hermitianTorusMatrix, mulVec, dotProduct, Fin.sum_univ_three] using congrFun he 1)
  have h2 : v 2 = 0 := zero_of_scalar_fixed ha (by
    simpa [hermitianTorusMatrix, mulVec, dotProduct, Fin.sum_univ_three] using congrFun he 2)
  ext i
  fin_cases i <;> assumption

/-- Transport to I/C_I(K) using the displayed group map, Borel image and
actual equivariant linear identification. The extension I need not split. -/
theorem unitary_centralQuotient_fixed (J : HermitianForm 3 F)
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (φ : K →* J.specialSubgroup)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] (Fin 3 → F))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      (unitaryNatural J) (φ g) (e v))
    (hB : (B.subgroupOf K).map φ = unitaryBorel J hstandard) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K := by
  apply inf_fixedSpace_le_of_centralQuotient ρ K B I hI
  exact fixedSpace_eq_bot_of_equivariant _ (unitaryNatural J) φ e he _ _ hB
    (unitary_borel_fixedSpace_eq_bot J hstandard n hn hcard hconj)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels
