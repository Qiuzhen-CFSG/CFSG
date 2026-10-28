module

public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Cardinalities of the concrete symplectic flag subgroups

Over any field, the Borel matrices have unique coordinates consisting of two
units `a,d` and four arbitrary scalars `b,u,w,v`. In the order e₀,e₁,f₀,f₁,
their matrices are

    [a b u (a*w+b*v)/d]
    [0 d w v          ]
    [0 0 1/a 0        ]
    [0 0 -b/(a*d) 1/d ].

The equation `gᵀ J g = J`, together with flag preservation, forces all displayed
entries. Conversely these matrices preserve the form and flag. The unipotent
subgroup is the specialization `a = d = 1`, by the determinant-character
calculation. The resulting equivalences give orders q⁴ and q⁴(q−1)² over a
finite field, with no restriction on the characteristic.

Source: the concrete flag realization underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(I)(2), printed pp.262–264.
These are counting lemmas for that realization, not the classification assertion
of F.1.12 itself.
-/

public section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]
noncomputable section
private def flagMatrix (a d : Fˣ) (b u w v : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![(a : F), b; 0, (d : F)]
    !![u, ((a : F)*w+b*v)/(d : F); w, v]
    0 !![(a : F)⁻¹, 0; -b/((a : F)*(d : F)), (d : F)⁻¹]
private lemma flagMatrix_mem (a d : Fˣ) (b u w v : F) :
    flagMatrix a d b u w v ∈ Matrix.symplecticGroup (Fin 2) F := by
  rw [flagMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
private def flagElement (a d : Fˣ) (b u w v : F) : borel (F := F) :=
  ⟨⟨flagMatrix a d b u w v, flagMatrix_mem a d b u w v⟩, by
    rw [mem_borel_iff]
    constructor
    · rfl
    · intro i j; rfl⟩
end

private lemma flagElement_surjective (g : borel (F := F)) :
    ∃ (a d : Fˣ) (b u w v : F), flagElement a d b u w v = g := by
  let m := g.val.val
  have hz := (mem_borel_iff g.val).mp g.property
  have h (i j : Fin 2 ⊕ Fin 2) := congrArg (fun M => M i j)
    (SymplecticGroup.mem_iff'.mp g.val.property)
  have h00 := h (.inl 0) (.inr 0)
  have h01 := h (.inl 0) (.inr 1)
  have h10 := h (.inl 1) (.inr 0)
  have h11 := h (.inl 1) (.inr 1)
  have h23 := h (.inr 0) (.inr 1)
  simp [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two, hz.1, hz.2, Matrix.transpose_apply] at h00 h01 h10 h11 h23
  have ha := left_ne_zero_of_mul_eq_one h00
  have h21 := h01.resolve_left ha
  simp only [h21, mul_zero, neg_zero, zero_add, neg_inj] at h11
  have hd := left_ne_zero_of_mul_eq_one h11
  change m (.inl 0) (.inl 0) ≠ 0 at ha
  change m (.inl 1) (.inl 1) ≠ 0 at hd
  change m (.inr 0) (.inr 1) = 0 at h21
  have h20 : m (.inr 0) (.inr 0) = (m (.inl 0) (.inl 0))⁻¹ := by
    apply mul_left_cancel₀ ha
    rw [h00, mul_inv_cancel₀ ha]
  have h31 : m (.inr 1) (.inr 1) = (m (.inl 1) (.inl 1))⁻¹ := by
    apply mul_left_cancel₀ hd
    rw [h11, mul_inv_cancel₀ hd]
  have h30 : m (.inr 1) (.inr 0) =
      -m (.inl 0) (.inl 1) / (m (.inl 0) (.inl 0) * m (.inl 1) (.inl 1)) := by
    apply (eq_div_iff (mul_ne_zero ha hd)).2
    linear_combination -m (.inl 0) (.inl 0) * h10 - m (.inl 0) (.inl 1) * h00
  have h03 : m (.inl 0) (.inr 1) =
      (m (.inl 0) (.inl 0) * m (.inl 1) (.inr 0) +
        m (.inl 0) (.inl 1) * m (.inl 1) (.inr 1)) / m (.inl 1) (.inl 1) := by
    change m (.inr 0) (.inr 0) * m (.inl 0) (.inr 1) +
      m (.inr 1) (.inr 0) * m (.inl 1) (.inr 1) +
      (-(m (.inl 0) (.inr 0) * m (.inr 0) (.inr 1)) +
      -(m (.inl 1) (.inr 0) * m (.inr 1) (.inr 1))) = 0 at h23
    rw [h21, h20, h30, h31] at h23
    field_simp [ha, hd] at h23
    apply (eq_div_iff hd).2
    linear_combination h23
  refine ⟨Units.mk0 _ ha, Units.mk0 _ hd, m (.inl 0) (.inl 1),
    m (.inl 0) (.inr 0), m (.inl 1) (.inr 0), m (.inl 1) (.inr 1), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  dsimp [m] at h20 h21 h30 h31 h03 ⊢
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [flagElement, flagMatrix, Matrix.fromBlocks, hz.1, hz.2, m,
      h20, h21, h30, h31, h03]

private def flagParam (x : Fˣ × Fˣ × F × F × F × F) : borel (F := F) :=
  flagElement x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

private lemma flagParam_injective : Function.Injective (flagParam (F := F)) := by
  rintro ⟨a, d, b, u, w, v⟩ ⟨a', d', b', u', w', v'⟩ h
  have he (i j : Fin 2 ⊕ Fin 2) := congrArg (fun g : borel (F := F) => g.val.val i j) h
  have h00 := he (.inl 0) (.inl 0)
  have h11 := he (.inl 1) (.inl 1)
  have h01 := he (.inl 0) (.inl 1)
  have h02 := he (.inl 0) (.inr 0)
  have h12 := he (.inl 1) (.inr 0)
  have h13 := he (.inl 1) (.inr 1)
  simp only [flagParam, flagElement, flagMatrix, Matrix.fromBlocks] at h00 h11 h01 h02 h12 h13
  exact Prod.ext (Units.ext h00) (Prod.ext (Units.ext h11)
    (Prod.ext h01 (Prod.ext h02 (Prod.ext h12 h13))))

/-- Unique coordinates for matrices preserving the standard isotropic flag. -/
noncomputable def borelCoordinates : (Fˣ × Fˣ × F × F × F × F) ≃ borel (F := F) :=
  Equiv.ofBijective flagParam ⟨flagParam_injective, by
    intro g
    obtain ⟨a, d, b, u, w, v, h⟩ := flagElement_surjective g
    exact ⟨⟨a, d, b, u, w, v⟩, h⟩⟩

private def unipotentParam (x : F × F × F × F) : unipotent (F := F) :=
  ⟨(flagElement 1 1 x.1 x.2.1 x.2.2.1 x.2.2.2).val, by
    rw [mem_unipotent_iff]
    exact ⟨(flagElement 1 1 x.1 x.2.1 x.2.2.1 x.2.2.2).property, rfl, rfl⟩⟩

private lemma unipotentParam_bijective : Function.Bijective (unipotentParam (F := F)) := by
  constructor
  · intro x y h
    have he : flagParam (1, 1, x) = flagParam (1, 1, y) :=
      Subtype.ext (congrArg (fun z : unipotent (F := F) => z.val) h)
    have ht := flagParam_injective he
    exact congrArg (fun p => p.2.2) ht
  · intro g
    have hg := (mem_unipotent_iff g.val).mp g.property
    obtain ⟨a, d, b, u, w, v, h⟩ := flagElement_surjective ⟨g.val, hg.1⟩
    have hm := congrArg (fun g : borel (F := F) => g.val.val) h
    have ha : a = 1 := by
      apply Units.ext
      have he := congrArg (fun m => m (.inl 0) (.inl 0)) hm
      exact he.trans hg.2.1
    have hd : d = 1 := by
      apply Units.ext
      have he := congrArg (fun m => m (.inl 1) (.inl 1)) hm
      exact he.trans hg.2.2
    subst a d
    exact ⟨(b, u, w, v), Subtype.ext (congrArg (fun z : borel (F := F) => z.val) h)⟩

/-- Four freely chosen field entries parametrize the determinant-one flag kernel. -/
noncomputable def unipotentCoordinates : (F × F × F × F) ≃ unipotent (F := F) :=
  Equiv.ofBijective unipotentParam unipotentParam_bijective

/-- The concrete unipotent flag subgroup has order q⁴. -/
theorem card_unipotent [Finite F] : Nat.card (unipotent (F := F)) = (Nat.card F)^4 := by
  rw [← Nat.card_congr (unipotentCoordinates (F := F))]
  simp only [Nat.card_prod]
  ring

/-- The whole Borel has order q⁴(q−1)², including its diagonal torus. -/
theorem card_borel [Finite F] :
    Nat.card (borel (F := F)) = (Nat.card F)^4 * (Nat.card F - 1)^2 := by
  rw [← Nat.card_congr (borelCoordinates (F := F))]
  simp only [Nat.card_prod, Nat.card_units]
  ring
end Theory.SpecificGroups.SymplecticFour
