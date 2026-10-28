module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure.Kernel
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure.Semilinear

/-!
# Unique shift–semilinear coordinates for root automorphisms

We define the proposed normal form as a central additive shift followed by a
pair of diagonal scalars, an optional graph involution, and optional Frobenius.
The two simple-root coordinates recover the scalars and both involution flags;
then cancellation recovers the shift. Thus the parameter map is injective.
Coverage of all root automorphisms is a separate obligation. No enumeration
of automorphisms or subgroups is used here.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.3, 46.14.
The cardinality and normalizer consumers are in `AutomizerConjugacy.FullStructure`.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
noncomputable section

def fieldChoice (f : Bool) : F ≃+* F := if f then fieldFrobenius else RingEquiv.refl F

def standardPart (a : Fˣ × Fˣ) (g f : Bool) : MulAut Root :=
  diagonalHom a * (if g then graph else 1) * (if f then SylowModel.frob else 1)

theorem standardPart_x (a : Fˣ × Fˣ) (g f : Bool) (q : Root) :
    (standardPart a g f q).x = (a.1 : F) * fieldChoice f (if g then q.y else q.x) := by
  cases g <;> cases f <;>
    simp [standardPart, fieldChoice, diagonalHom, diagonal, graph, SylowModel.frob]

theorem standardPart_y (a : Fˣ × Fˣ) (g f : Bool) (q : Root) :
    (standardPart a g f q).y = (a.2 : F) * fieldChoice f (if g then q.x else q.y) := by
  cases g <;> cases f <;>
    simp [standardPart, fieldChoice, diagonalHom, diagonal, graph, SylowModel.frob]

theorem standardPart_mem (a : Fˣ × Fˣ) (g f : Bool) : standardPart a g f ∈ semilinear := by
  have hd : diagonalHom a ∈ semilinear :=
    (le_sup_left : torus ⊔ zpowers graph ≤ semilinear)
      ((le_sup_left : torus ≤ torus ⊔ zpowers graph) ⟨a, rfl⟩)
  have hg : (if g then graph else 1) ∈ semilinear := by
    cases g
    · exact semilinear.one_mem
    · exact (le_sup_left : torus ⊔ zpowers graph ≤ semilinear)
        ((le_sup_right : zpowers graph ≤ torus ⊔ zpowers graph) (mem_zpowers graph))
  have hf : (if f then SylowModel.frob else 1) ∈ semilinear := by
    cases f
    · exact semilinear.one_mem
    · exact (le_sup_right : zpowers SylowModel.frob ≤ semilinear) (mem_zpowers SylowModel.frob)
  exact semilinear.mul_mem (semilinear.mul_mem hd hg) hf

abbrev Parameters := Shift × (Fˣ × Fˣ) × Bool × Bool

def normalForm (p : Parameters) : MulAut Root :=
  shift p.1 * standardPart p.2.1 p.2.2.1 p.2.2.2

/-- Classifying only the two root coordinates suffices for full coverage. -/
theorem normalForm_surjective_of_coordinate_action
    (h : ∀ a : MulAut Root, ∃ (d : Fˣ × Fˣ) (g f : Bool),
      ∀ q : Root, (a q).x = (standardPart d g f q).x ∧
        (a q).y = (standardPart d g f q).y) :
    Function.Surjective normalForm := by
  intro a
  obtain ⟨d, g, f, hd⟩ := h a
  let t := standardPart d g f
  have hx (q : Root) : ((a * t⁻¹) q).x = q.x := by
    change (a (t.symm q)).x = q.x
    rw [(hd (t.symm q)).1]
    exact congrArg SylowModel.U.x (t.apply_symm_apply q)
  have hy (q : Root) : ((a * t⁻¹) q).y = q.y := by
    change (a (t.symm q)).y = q.y
    rw [(hd (t.symm q)).2]
    exact congrArg SylowModel.U.y (t.apply_symm_apply q)
  obtain ⟨l, hl⟩ := exists_shift_of_fix_coordinates (a * t⁻¹) hx hy
  refine ⟨(l, d, g, f), ?_⟩
  change shift l * t = a
  rw [← hl, inv_mul_cancel_right]

theorem normalForm_injective : Function.Injective normalForm := by
  rintro ⟨l, a, g, f⟩ ⟨m, b, h, k⟩ he
  have hx (q : Root) :
      (a.1 : F) * fieldChoice f (if g then q.y else q.x) =
        (b.1 : F) * fieldChoice k (if h then q.y else q.x) := by
    have hh := congrArg (fun s : MulAut Root => (s q).x) he
    simpa only [normalForm, MulAut.mul_apply, shift_x, standardPart_x] using hh
  have hy (q : Root) :
      (a.2 : F) * fieldChoice f (if g then q.x else q.y) =
        (b.2 : F) * fieldChoice k (if h then q.x else q.y) := by
    have hh := congrArg (fun s : MulAut Root => (s q).y) he
    simpa only [normalForm, MulAut.mul_apply, shift_y, standardPart_y] using hh
  have hgh : g = h := by
    have hh := hx ⟨1, 0, 0⟩
    cases g <;> cases h
    · rfl
    · simp at hh
    · exact ((Units.ne_zero b.1) (by simpa using hh.symm)).elim
    · rfl
  subst h
  have hab : a = b := by
    apply Prod.ext <;> apply Units.ext
    · cases g
      · simpa using hx ⟨1, 0, 0⟩
      · simpa using hx ⟨0, 1, 0⟩
    · cases g
      · simpa using hy ⟨0, 1, 0⟩
      · simpa using hy ⟨1, 0, 0⟩
  subst b
  have hfield (x : F) : fieldChoice f x = fieldChoice k x := by
    apply mul_left_cancel₀ (Units.ne_zero a.1)
    cases g
    · simpa using hx ⟨x, 0, 0⟩
    · simpa using hx ⟨0, x, 0⟩
  have hfk : f = k := by
    obtain ⟨x, hxnontriv⟩ := exists_fieldFrobenius_ne
    have hh := hfield x
    cases f <;> cases k
    · rfl
    · exact (hxnontriv (by simpa [fieldChoice] using hh.symm)).elim
    · exact (hxnontriv (by simpa [fieldChoice] using hh)).elim
    · rfl
  subst k
  have hlm : l = m := shift_injective (mul_right_cancel he)
  subst m
  rfl

theorem parameters_card : Nat.card Parameters = Nat.card Shift * 36 := by
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  norm_num only [Parameters, Nat.card_prod, Nat.card_units, card_F, hb]

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
