module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.HallSource
/-!
# Commutativity of the paired odd Hall torus

For each even block, apply the proved natural quotient-action theorem to
Dᵢ E. The normalizer hypotheses descend from the ambient Hall group, so
E centralizes each Dᵢ. Their join D is therefore centralized by E, and
B = D E is abelian. The final consumer uses the literal conjugation map
and derives factor normalizations from the source intersections R ∩ Lᵢ
and D ∩ Lᵢ.

Source: Aschbacher–Smith, the two-block shadow argument, printed p.540,
using the original quotient-action argument of 2.4.8(5), printed p.530.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]

/-- A full odd torus in an even block is centralized by the abelian normal actor. -/
theorem natural_torus_centralized
    (L B D E : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (P : Sylow 2 L) (hBL : B ≤ normalizer (L : Set G))
    (hBP : B ≤ normalizer ((P : Subgroup L).map L.subtype : Set G))
    (hDL : D ≤ L) (hDB : D ≤ B) (hEB : E ≤ B)
    (hBD : B ≤ normalizer (D : Set G)) (hBE : B ≤ normalizer (E : Set G))
    [IsMulCommutative D] [IsMulCommutative E]
    (hodd : Odd (Nat.card D)) (hcard : Nat.card D = 2^n-1) :
    D ≤ centralizer (E : Set G) := by
  have hsub : D ⊔ E ≤ B := sup_le hDB hEB
  let : IsMulCommutative (D ⊔ E : Subgroup G) :=
    LinearShadows.Single.natural_joint_torus_abelian L (D ⊔ E) D E hL P
      (hsub.trans hBL) (hsub.trans hBP) hDL le_sup_left le_sup_right rfl
      (hsub.trans hBD) (hsub.trans hBE) hodd hcard
  intro d hd e he
  exact congrArg Subtype.val (mul_comm' (⟨e, mem_sup_right he⟩ : (D ⊔ E : Subgroup G))
    ⟨d, mem_sup_left hd⟩)

/-- The two natural torus factors make the entire normal abelian-factor join abelian. -/
theorem double_joint_torus_abelian
    (L₁ L₂ B D D₁ D₂ E : Subgroup G) {n : ℕ}
    (hL₁ : ChapterC.IsL2EvenBlock L₁ n) (hL₂ : ChapterC.IsL2EvenBlock L₂ n)
    (P₁ : Sylow 2 L₁) (P₂ : Sylow 2 L₂)
    (hBL₁ : B ≤ normalizer (L₁ : Set G)) (hBL₂ : B ≤ normalizer (L₂ : Set G))
    (hBP₁ : B ≤ normalizer ((P₁ : Subgroup L₁).map L₁.subtype : Set G))
    (hBP₂ : B ≤ normalizer ((P₂ : Subgroup L₂).map L₂.subtype : Set G))
    (hD₁L : D₁ ≤ L₁) (hD₂L : D₂ ≤ L₂) (hD : D₁ ⊔ D₂ = D)
    (hB : D ⊔ E = B)
    (hBD₁ : B ≤ normalizer (D₁ : Set G)) (hBD₂ : B ≤ normalizer (D₂ : Set G))
    (hBE : B ≤ normalizer (E : Set G))
    [IsMulCommutative D] [IsMulCommutative E]
    (hodd₁ : Odd (Nat.card D₁)) (hodd₂ : Odd (Nat.card D₂))
    (hcard₁ : Nat.card D₁ = 2^n-1) (hcard₂ : Nat.card D₂ = 2^n-1) :
    IsMulCommutative B := by
  have hDB : D ≤ B := le_sup_left.trans_eq hB
  have hEB : E ≤ B := le_sup_right.trans_eq hB
  have hD₁D : D₁ ≤ D := le_sup_left.trans_eq hD
  have hD₂D : D₂ ≤ D := le_sup_right.trans_eq hD
  let : IsMulCommutative D₁ := .of_setLike_mul_comm fun _ ha _ hb =>
    setLike_mul_comm (hD₁D ha) (hD₁D hb)
  let : IsMulCommutative D₂ := .of_setLike_mul_comm fun _ ha _ hb =>
    setLike_mul_comm (hD₂D ha) (hD₂D hb)
  have hc₁ := natural_torus_centralized L₁ B D₁ E hL₁ P₁ hBL₁ hBP₁ hD₁L
    (hD₁D.trans hDB) hEB hBD₁ hBE hodd₁ hcard₁
  have hc₂ := natural_torus_centralized L₂ B D₂ E hL₂ P₂ hBL₂ hBP₂ hD₂L
    (hD₂D.trans hDB) hEB hBD₂ hBE hodd₂ hcard₂
  have hDE : D ≤ centralizer (E : Set G) := hD ▸ sup_le hc₁ hc₂
  have hED : E ≤ centralizer (D : Set G) := le_centralizer_iff.mp hDE
  rw [← hB]
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) hED
  · apply le_centralizer_iff.mpr
    exact sup_le hDE (le_centralizer_iff_isMulCommutative.mpr inferInstance)

/-- Literal conjugate-torus specialization of the paired-block argument. -/
theorem double_conjugate_torus_abelian
    (L₁ L₂ B D D₁ D₂ : Subgroup G) (x : G) {n : ℕ}
    (hL₁ : ChapterC.IsL2EvenBlock L₁ n) (hL₂ : ChapterC.IsL2EvenBlock L₂ n)
    (P₁ : Sylow 2 L₁) (P₂ : Sylow 2 L₂)
    (hBL₁ : B ≤ normalizer (L₁ : Set G)) (hBL₂ : B ≤ normalizer (L₂ : Set G))
    (hBP₁ : B ≤ normalizer ((P₁ : Subgroup L₁).map L₁.subtype : Set G))
    (hBP₂ : B ≤ normalizer ((P₂ : Subgroup L₂).map L₂.subtype : Set G))
    (hD₁L : D₁ ≤ L₁) (hD₂L : D₂ ≤ L₂) (hD : D₁ ⊔ D₂ = D)
    (hB : D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom = B)
    (hBD₁ : B ≤ normalizer (D₁ : Set G)) (hBD₂ : B ≤ normalizer (D₂ : Set G))
    (hBE : B ≤ normalizer (D.map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    [IsMulCommutative D]
    (hodd₁ : Odd (Nat.card D₁)) (hodd₂ : Odd (Nat.card D₂))
    (hcard₁ : Nat.card D₁ = 2^n-1) (hcard₂ : Nat.card D₂ = 2^n-1) :
    IsMulCommutative B := by
  exact double_joint_torus_abelian L₁ L₂ B D D₁ D₂
    (D.map (MulAut.conj x⁻¹).toMonoidHom) hL₁ hL₂ P₁ P₂ hBL₁ hBL₂ hBP₁ hBP₂
    hD₁L hD₂L hD hB hBD₁ hBD₂ hBE hodd₁ hodd₂ hcard₁ hcard₂

/-- The actual paired Sylow intersections and torus intersections supply all
normalizations needed for the literal conjugate product. -/
theorem double_conjugate_torus_abelian_of_intersections
    (L₁ L₂ R B D : Subgroup G) (x : G) {n : ℕ}
    (hL₁ : ChapterC.IsL2EvenBlock L₁ n) (hL₂ : ChapterC.IsL2EvenBlock L₂ n)
    (P₁ : Sylow 2 L₁) (P₂ : Sylow 2 L₂)
    (hP₁ : (P₁ : Subgroup L₁).map L₁.subtype = R ⊓ L₁)
    (hP₂ : (P₂ : Subgroup L₂).map L₂.subtype = R ⊓ L₂)
    (hBL₁ : B ≤ normalizer (L₁ : Set G)) (hBL₂ : B ≤ normalizer (L₂ : Set G))
    (hBR : B ≤ normalizer (R : Set G)) (hBD : B ≤ normalizer (D : Set G))
    (hD : (D ⊓ L₁) ⊔ (D ⊓ L₂) = D)
    (hB : D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom = B)
    (hBE : B ≤ normalizer (D.map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    [IsMulCommutative D]
    (hodd₁ : Odd (Nat.card (D ⊓ L₁ : Subgroup G)))
    (hodd₂ : Odd (Nat.card (D ⊓ L₂ : Subgroup G)))
    (hcard₁ : Nat.card (D ⊓ L₁ : Subgroup G) = 2^n-1)
    (hcard₂ : Nat.card (D ⊓ L₂ : Subgroup G) = 2^n-1) :
    IsMulCommutative B := by
  have hBP₁ : B ≤ normalizer ((P₁ : Subgroup L₁).map L₁.subtype : Set G) := by
    rw [hP₁]
    exact (le_inf hBR hBL₁).trans inf_normalizer_le_normalizer_inf
  have hBP₂ : B ≤ normalizer ((P₂ : Subgroup L₂).map L₂.subtype : Set G) := by
    rw [hP₂]
    exact (le_inf hBR hBL₂).trans inf_normalizer_le_normalizer_inf
  exact double_conjugate_torus_abelian L₁ L₂ B D (D ⊓ L₁) (D ⊓ L₂) x
    hL₁ hL₂ P₁ P₂ hBL₁ hBL₂ hBP₁ hBP₂ inf_le_right inf_le_right hD hB
    ((le_inf hBD hBL₁).trans inf_normalizer_le_normalizer_inf)
    ((le_inf hBD hBL₂).trans inf_normalizer_le_normalizer_inf)
    hBE hodd₁ hodd₂ hcard₁ hcard₂

end CFSG.Quasithin.Chapter2.LinearDouble
