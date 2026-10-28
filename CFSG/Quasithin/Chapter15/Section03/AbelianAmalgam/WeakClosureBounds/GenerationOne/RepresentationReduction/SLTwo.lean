module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.FixedSpace
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# The SL₂ Borel calculation, including central extensions

A nonidentity split diagonal element has no fixed vector on the natural
SL₂-module over a field with more than two elements. This proves the claim for
the actual upper-triangular Borel and transports it to an identified local
section. The central-extension lemma then applies to I/C_I(K), without assuming
that I splits. This is the SL₂ calculation in Aschbacher--Smith, 15.3.65,
printed p.1152; the occurrence of the module remains a classification obligation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open Representation Representation.BinaryOffender Matrix Matrix.SpecialLinearGroup
open scoped Matrix

section Matrix
variable {F : Type*} [Field F]

/-- A nonidentity split diagonal has no eigenvalue one on the natural module. -/
theorem slTwo_diagonal_fixed_eq_zero (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (v : Fin 2 → F) (hv : specialLinearNatural 2 (diag2 x hx) v = v) : v = 0 := by
  have he (i : Fin 2) := congrFun hv i
  have h0 : x * v 0 = v 0 := by
    simpa [specialLinearNatural_apply, diag2_coe', mulVec, dotProduct,
      Fin.sum_univ_two] using he 0
  have h1 : x⁻¹ * v 1 = v 1 := by
    simpa [specialLinearNatural_apply, diag2_coe', mulVec, dotProduct,
      Fin.sum_univ_two] using he 1
  have hz0 : v 0 = 0 := by
    have h : (x - 1) * v 0 = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h0
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hx1)
  have hz1 : v 1 = 0 := by
    have h : (x⁻¹ - 1) * v 1 = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h1
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (inv_ne_one.mpr hx1))
  ext i
  fin_cases i <;> assumption

variable [Finite F] [Algebra (ZMod 2) F]

/-- The literal Borel has no nonzero fixed vector on the binary natural module. -/
theorem slTwo_borel_fixedSpace_eq_bot (hF : 2 < Nat.card F) :
    fixedSpace (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2))
      (rankOneBorel F) = ⊥ := by
  classical
  let := Fintype.ofFinite F
  have hcard : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hF
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hx0 : x ≠ 0 := by simpa using fun h => hx (by simp [h])
  have hx1 : x ≠ 1 := by simpa using fun h => hx (by simp [h])
  apply bot_unique
  intro v hv
  exact slTwo_diagonal_fixed_eq_zero x hx0 hx1 v
    (hv ⟨diag2 x hx0, diag_mem_rankOneBorel x hx0⟩)

/-- Transport to an actual local section by an equivariant linear equivalence.
The Borel image equality, as well as the group map, is retained. -/
theorem slTwo_section_fixedSpace_eq_bot
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (φ : D →* SpecialLinearGroup (Fin 2) F)
    (e : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, e (ρ g v) = specialLinearNatural 2 (φ g) (e v))
    (B : Subgroup D) (hB : B.map φ = rankOneBorel F) (hF : 2 < Nat.card F) :
    fixedSpace ρ B = ⊥ :=
  fixedSpace_eq_bot_of_equivariant ρ
    (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)) φ e he
    B (rankOneBorel F) hB (slTwo_borel_fixedSpace_eq_bot hF)

/-- Borel fixation in an actual central extension of the natural SL₂ module.
The field size hypothesis includes every f>1 case, whether or not the extension splits. -/
theorem slTwo_centralQuotient_fixed
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (φ : K →* SpecialLinearGroup (Fin 2) F)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      specialLinearNatural 2 (φ g) (e v))
    (hB : (B.subgroupOf K).map φ = rankOneBorel F) (hF : 2 < Nat.card F) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K :=
  inf_fixedSpace_le_of_centralQuotient ρ K B I hI
    (slTwo_section_fixedSpace_eq_bot _ φ e he _ hB hF)

end Matrix
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
