module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Reduction
public import Theory.Mathieu.M12.Properties.Transitivity
-- Internal access is confined to certifying the fixed Atlas embedding table:
-- its public `m11M12PointEmbedding_eq_value` has an unexposed right-hand side.
-- This proof extension preserves the foundational module's public boundary.
import all Theory.Mathieu.M12.Properties.PointStabilizer

/-!
# The marked point stabilizer and three intersection words

The embedded words aba, bab³ and b³ab fix both 0 and 6. Their conjugates
by the first M₁₂ generator consequently fix 0. The first generator and
the point stabilizer generate M₁₂, since that stabilizer is maximal.
The relation (ta)⁵ = 1 will distinguish the two possible extending matrices.

These are literal permutations in the existing Atlas marking, used for the
James recognition argument cited in Aschbacher--Smith G.7.3(2), p.348.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12Recognition.PointExtension
open Sporadic.Mathieu

def aPerm : Equiv.Perm (Fin 12) :=
  Equiv.swap 7 10 * Equiv.swap 6 5 * Equiv.swap 4 3 * Equiv.swap 11 9

def bPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 6, 8, 11] * List.formPerm [7, 4, 2, 9]

noncomputable def a : M12 := pointEmbedding m11GeneratorAInM11
noncomputable def b : M12 := pointEmbedding m11GeneratorBInM11
def t : M12 := ⟨m12GeneratorA, m12GeneratorA_mem⟩

theorem a_perm : (a : Equiv.Perm (Fin 12)) = aPerm := by
  apply _root_.Equiv.ext
  intro x
  fin_cases x
  · exact m11ToM12ExtendHom_apply_12 m11GeneratorAInM11
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 1) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 6) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 7) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 5) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 0) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 4) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 2) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 3) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 9) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 10) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorAInM11 (m11M12PointEmbedding 8) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl

theorem b_perm : (b : Equiv.Perm (Fin 12)) = bPerm := by
  apply _root_.Equiv.ext
  intro x
  fin_cases x
  · exact m11ToM12ExtendHom_apply_12 m11GeneratorBInM11
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 1) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 6) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 7) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 5) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 0) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 4) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 2) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 3) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 9) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 10) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl
  · change m11ToM12ExtendHom m11GeneratorBInM11 (m11M12PointEmbedding 8) = _
    rw [m11ToM12ExtendHom_apply_embedded]
    rfl

noncomputable def intersectionWord (k : Fin 3) : M12 :=
  ![a * b * a, b * a * b ^ 3, b ^ 3 * a * b] k

def wordPerm (k : Fin 3) : Equiv.Perm (Fin 12) :=
  ![aPerm * bPerm * aPerm, bPerm * aPerm * bPerm ^ 3,
    bPerm ^ 3 * aPerm * bPerm] k

theorem intersectionWord_perm (k : Fin 3) :
    (intersectionWord k : Equiv.Perm (Fin 12)) = wordPerm k := by
  fin_cases k <;> simp [intersectionWord, wordPerm, a_perm, b_perm]

theorem intersectionWord_fixes (k : Fin 3) :
    wordPerm k 0 = 0 ∧ wordPerm k 6 = 6 := by
  revert k
  decide +kernel

theorem intersectionWord_mem (k : Fin 3) :
    intersectionWord k ∈ MulAction.stabilizer M12 (12 : Fin 12) := by
  change (intersectionWord k : Equiv.Perm (Fin 12)) 0 = 0
  rw [intersectionWord_perm]
  exact (intersectionWord_fixes k).1

theorem conjugateWord_mem (k : Fin 3) :
    t * intersectionWord k * t⁻¹ ∈ MulAction.stabilizer M12 (12 : Fin 12) := by
  change (m12GeneratorA * (intersectionWord k : Equiv.Perm (Fin 12)) *
    m12GeneratorA⁻¹) 0 = 0
  rw [intersectionWord_perm]
  have : m12GeneratorA⁻¹ 0 = 6 := by decide +kernel
  change m12GeneratorA (wordPerm k (m12GeneratorA⁻¹ 0)) = 0
  rw [this, (intersectionWord_fixes k).2]
  decide +kernel

theorem t_not_mem : t ∉ MulAction.stabilizer M12 (12 : Fin 12) := by
  change ¬ m12GeneratorA 0 = 0
  decide +kernel

theorem ta_fifth : (t * a) ^ 5 = 1 := by
  apply Subtype.ext
  change (m12GeneratorA * (a : Equiv.Perm (Fin 12))) ^ 5 = 1
  rw [a_perm]
  decide +kernel

theorem agree_on_stabilizer
    (τ : Representation (ZMod 2) M12 M12Heart)
    (hpoint : ∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g))
    (g : M12) (hg : g ∈ MulAction.stabilizer M12 (12 : Fin 12)) :
    τ g = m12HeartRepresentation g := by
  have hs : Function.Surjective m11ToM12PointStabilizer :=
    (m11ToM12PointStabilizer_injective.bijective_of_nat_card_le
      (by exact (Nat.card_congr m11EquivM12PointStabilizer.toEquiv).ge)).surjective
  obtain ⟨x, hx⟩ := hs ⟨g, hg⟩
  have he : pointEmbedding x = g := congrArg Subtype.val hx
  rw [← he]
  exact hpoint x

theorem eq_of_agree_on_t
    (τ : Representation (ZMod 2) M12 M12Heart)
    (hpoint : ∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g))
    (ht : τ t = m12HeartRepresentation t) : τ = m12HeartRepresentation := by
  let E := τ.eqLocus m12HeartRepresentation
  have hle : MulAction.stabilizer M12 (12 : Fin 12) ≤ E :=
    fun g hg => agree_on_stabilizer τ hpoint g hg
  have htop : E = ⊤ := m12PointStabilizerTwelve_isCoatom.lt_iff.mp
    (lt_of_le_of_ne hle (by
      intro he
      apply t_not_mem
      rw [he]
      exact ht))
  apply MonoidHom.ext
  intro g
  exact (show g ∈ E by rw [htop]; trivial)

end Representation.MathieuSmall.M12Recognition.PointExtension
