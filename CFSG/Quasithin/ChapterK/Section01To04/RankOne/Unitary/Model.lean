module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The actual natural SU₃ identification for K.3.3

The entire marked layer is identified with the special unitary matrix group,
including its possible cubic center. Binary coordinates intertwine the column
action. The field degree determines the module dimension, and Sylow restriction
transports the known Hermitian omega calculation through the literal inclusion
of the layer. No recognition or ratio conclusion is included in the model.

Source: Aschbacher–Smith, K.3.3, printed p.456 (1 March 2004 manuscript).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki.MatrixGroups Subgroup Representation.BinaryOffender

variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]

/-- An actual SU₃ natural module, with its full special-unitary actor. -/
structure UnitaryModel (J : HermitianForm 3 F)
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) where
  groupEquiv : L ≃* J.specialSubgroup
  coordinates : V ≃ₗ[ZMod 2] (Fin 3 → F)
  intertwines : ∀ (g : L) (v : V),
    coordinates (ρ (g : G) v) = Matrix.mulVec (groupEquiv g).val.val (coordinates v)

namespace UnitaryModel
variable {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (M : UnitaryModel J ρ L)

/-- Coordinates preserve the original ambient actor. -/
def coordinateAction : Representation (ZMod 2) G (Fin 3 → F) :=
  M.coordinates.conjRingEquiv.toMonoidHom.comp ρ

@[simp] theorem coordinateAction_apply (g : G) (v : V) :
    M.coordinateAction g (M.coordinates v) = M.coordinates (ρ g v) := by
  change M.coordinates (ρ g (M.coordinates.symm (M.coordinates v))) = _
  rw [M.coordinates.symm_apply_apply]

theorem coordinateAction_natural (g : L) (v : Fin 3 → F) :
    M.coordinateAction (g : G) v = Matrix.mulVec (M.groupEquiv g).val.val v := by
  change M.coordinates (ρ (g : G) (M.coordinates.symm v)) = _
  rw [M.intertwines, M.coordinates.apply_symm_apply]

theorem coordinateAction_injective (hfaith : Function.Injective ρ) :
    Function.Injective M.coordinateAction :=
  M.coordinates.conjRingEquiv.injective.comp hfaith

theorem fixedCodim_eq (A : Subgroup G) :
    fixedCodim ρ A = fixedCodim M.coordinateAction A := by
  simpa using fixedCodim_map_equivariant ρ M.coordinateAction (MonoidHom.id G)
    M.coordinates (fun g v => (M.coordinateAction_apply g v).symm) A

variable [Finite F]

/-- The binary degree of the actual coefficient field. -/
theorem field_finrank {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2) :
    Module.finrank (ZMod 2) F = 2 * s := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_zmod, hcard, ← pow_mul] at hc
  exact ((Nat.pow_right_injective (by decide : 2 ≤ 2)) hc).symm.trans (Nat.mul_comm _ _)

include M in
/-- The source dimension 6s follows from the given column-action identification. -/
theorem finrank_eq {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2) :
    Module.finrank (ZMod 2) V = 6 * s := by
  rw [M.coordinates.finrank_eq, Module.finrank_pi_fintype, field_finrank hcard]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

variable [Finite G]

include M in
/-- The source's literal Ω₁(T ∩ L), without replacing SU₃ by its projective quotient. -/
theorem omega_calculation [L.Normal]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) (T : Sylow 2 G) :
    IsElementaryTwo (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
      rank (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = s := by
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ s :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  have ho := HermitianForm.SylowOmega.omega_of_special_equiv J hs hcard hfixed hJ M.groupEquiv P
  have hc : Nat.card (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = 2 ^ s := by
    rw [← hP, ← map_omegaOneAmbient_injective L.subtype L.subtype_injective,
      card_map_of_injective L.subtype_injective]
    exact ho.2.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hb
    rw [hb, card_bot] at hc
    have hp := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : s ≠ 0)
    omega
  · rw [← hP, ← map_omegaOneAmbient_injective L.subtype L.subtype_injective]
    let := ho.2.1
    exact IsElementaryAbelian.map _
  · rw [rank, hc, Nat.log_pow (by decide : 1 < 2)]

end UnitaryModel
end CFSG.Quasithin.ChapterK.RankOne
