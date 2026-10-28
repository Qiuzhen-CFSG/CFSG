module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Torus
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration

/-!
# Opposite unitary flags and their diagonal stabilizer

A matrix fixing the standard and opposite flags is both upper and lower
triangular. On this intersection the actual Borel torus character is
injective, since an upper-unitriangular diagonal matrix is the identity.
This bounds the literal opposite-flag fixer by `(q²-1)(q-1)`, hence by three
in SU₄(2), without enumerating matrices.

Source: the apartment-stabilizer calculation underlying Aschbacher–Smith
F.4.5–6, printed pp.275–277.
-/
@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourApartment
noncomputable section
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "G" => SU F (form F σ hσ)
local notation "B" => borelSU F (form F σ hσ)
local notation "w" => reverse F σ hσ

theorem reverse_inv : w⁻¹ = w := by
  apply (inv_eq_iff_mul_eq_one).mpr
  apply Subtype.ext
  apply Units.ext
  change (w).val.val * (w).val.val = 1
  rw [reverse_val, gram_sq]

theorem diagonal_of_opposite_flags (a : G) (ha : a ∈ B) (hb : w * a * w ∈ B) :
    a.val.val = Matrix.diagonal (fun i => a.val.val i i) := by
  have ht := (mem_borel_iff_triangular F σ hσ a).mp ha
  have ht' := (mem_borel_iff_triangular F σ hσ (w*a*w)).mp hb
  have h23 := ht' (by decide : (0 : Fin 4) < 1)
  have h13 := ht' (by decide : (0 : Fin 4) < 2)
  have h03 := ht' (by decide : (0 : Fin 4) < 3)
  have h12 := ht' (by decide : (1 : Fin 4) < 2)
  have h02 := ht' (by decide : (1 : Fin 4) < 3)
  have h01 := ht' (by decide : (2 : Fin 4) < 3)
  change ((w).val.val * a.val.val * (w).val.val) 1 0 = 0 at h23
  change ((w).val.val * a.val.val * (w).val.val) 2 0 = 0 at h13
  change ((w).val.val * a.val.val * (w).val.val) 3 0 = 0 at h03
  change ((w).val.val * a.val.val * (w).val.val) 2 1 = 0 at h12
  change ((w).val.val * a.val.val * (w).val.val) 3 1 = 0 at h02
  change ((w).val.val * a.val.val * (w).val.val) 3 2 = 0 at h01
  simp [reverse_val, gram, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    at h23 h13 h03 h12 h02 h01
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_or_gt_of_ne hij with h | h
    · fin_cases i <;> fin_cases j <;> simp_all
    · exact ht h

def oppositeFlagFixer : Subgroup G := B ⊓ (B).comap (MulAut.conj w).toMonoidHom

def oppositeCharacter : oppositeFlagFixer F σ hσ →* Fˣ × (FixedField F σ)ˣ :=
  (torusCharacter F σ hσ).comp (Subgroup.inclusion inf_le_left)

theorem oppositeCharacter_injective : Function.Injective (oppositeCharacter F σ hσ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have ha' : (⟨a.val, a.property.1⟩ : B) ∈ (torusCharacter F σ hσ).ker := ha
  rw [torusCharacter_ker] at ha'
  have hu : a.val ∈ upper F σ hσ := ha'
  have hd := (mem_upper_iff_entries F σ hσ a.val).mp hu
  have ho : w * a.val * w ∈ B := by
    have hm := a.property.2
    change w * a.val * w⁻¹ ∈ B at hm
    simpa only [reverse_inv] using hm
  have hm := diagonal_of_opposite_flags F σ hσ a.val a.property.1 ho
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change a.val.val.val = 1
  rw [hm]
  ext i j
  simp [hd.2]

theorem oppositeFlagFixer_card_le : Nat.card (oppositeFlagFixer F σ hσ) ≤
    (Nat.card F - 1) * (Nat.card (FixedField F σ) - 1) := by
  have h := Nat.card_le_card_of_injective (oppositeCharacter F σ hσ)
    (oppositeCharacter_injective F σ hσ)
  simpa only [Nat.card_prod, Nat.card_units] using h
end
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourApartment
