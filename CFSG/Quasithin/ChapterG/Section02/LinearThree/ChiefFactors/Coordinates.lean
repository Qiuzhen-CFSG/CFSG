module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.QuotientImages
public import Mathlib.FieldTheory.Finiteness

/-!
# Marked coordinates used by the G.2.5 order calculation

The inputs are the portions of clauses (6–7) needed for counting: genuine
equivariant coordinates on the two literal quotients, and the images of the
marked subgroups as copies of one-dimensional F-subspaces. The lower action
is contragredient; the upper action is natural. The recognition argument must
construct these markings (its lower lines are annihilators of the marked
planes). No order or chief-factor count is included in this interface.

Counting a marked image uses an equivalence with a power of its actual line.
In particular, the upper marking is an image in S/S₃, not a quotient of W by
S₃. Zero multiplicities are permitted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.2.5(6–8), printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors

variable {F : Type*} [Field F]

/-- The copies of an actual F-subspace inside the coordinate direct sum. -/
def lineCopies (P : Submodule F (Fin 3 → F)) (k : ℕ) :
    Subgroup (Multiplicative (Fin k → Fin 3 → F)) where
  carrier := {v | ∀ i, v.toAdd i ∈ P}
  one_mem' := fun _ => P.zero_mem
  mul_mem' hv hw i := P.add_mem (hv i) (hw i)
  inv_mem' hv i := P.neg_mem (hv i)

/-- Counting uses the line itself, rather than a prescribed numerical order. -/
def lineCopiesEquiv (P : Submodule F (Fin 3 → F)) (k : ℕ) :
    lineCopies P k ≃ (Fin k → P) where
  toFun v i := ⟨v.val.toAdd i, v.property i⟩
  invFun v := ⟨Multiplicative.ofAdd (fun i => (v i).val), fun i => (v i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_lineCopies [Finite F] (P : Submodule F (Fin 3 → F)) (k : ℕ)
    (hP : Module.finrank F P = 1) :
    Nat.card (lineCopies P k) = Nat.card F ^ k := by
  rw [Nat.card_congr (lineCopiesEquiv P k), Nat.card_fun,
    Module.natCard_eq_pow_finrank (K := F), hP, pow_one, Nat.card_fin]

variable {G : Type*} [Group G] [Finite G] [Finite F]
  {D : Setup G} {n : ℕ} {g h : G}

/-- The marked part of the earlier layer identifications. All action equations
refer to ambient conjugation and the original star projection. -/
structure MarkedLayers (d : Hypothesis D F n g h) (hLI : D.L ≤ I D g h)
    (r s : ℕ)
    [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
    [((S₃ D g h).subgroupOf (S D g h)).Normal] where
  lower : LowerQuotient D g h ≃* Multiplicative (Fin s → Fin 3 → F)
  upper : UpperQuotient D g h ≃* Multiplicative (Fin r → Fin 3 → F)
  lower_normalizes : D.L ≤ normalizer (S₃ D g h : Set G)
  lower_equivariant (l : D.L) (a : S₃ D g h) (i : Fin s) :
    (lower (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))
      ⟨(l : G) * a * (l : G)⁻¹,
        (mem_normalizer_iff.mp (lower_normalizes l.property) a).mp a.property⟩)).toAdd i =
      (d.model (starProjection D l)⁻¹).val.transpose *ᵥ
        (lower (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a)).toAdd i
  upper_equivariant (l : D.L) (a : S D g h) (i : Fin r) :
    (upper (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * a * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h (hLI l.property)) a).mp
          a.property⟩)).toAdd i =
      (d.model (starProjection D l)).val *ᵥ
        (upper (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a)).toAdd i
  lowerLineG : Submodule F (Fin 3 → F)
  lowerLineH : Submodule F (Fin 3 → F)
  lowerLineG_dimension : Module.finrank F lowerLineG = 1
  lowerLineH_dimension : Module.finrank F lowerLineH = 1
  lower_mark_g :
    (lowerImage D g h (W D g h ⊓ Setup.conjugate (W D g h) g)).map lower.toMonoidHom =
      lineCopies lowerLineG s
  lower_mark_h :
    (lowerImage D g h (W D g h ⊓ Setup.conjugate (W D g h) h)).map lower.toMonoidHom =
      lineCopies lowerLineH s
  upper_mark :
    (upperImage D g h (W D g h)).map upper.toMonoidHom = lineCopies d.point r

namespace MarkedLayers
variable {d : Hypothesis D F n g h} {hLI : D.L ≤ I D g h} {r s : ℕ}
  [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  (c : MarkedLayers d hLI r s)

include c

theorem card_lowerImage_g :
    Nat.card (lowerImage D g h (W D g h ⊓ Setup.conjugate (W D g h) g)) =
      2 ^ (n * s) := by
  rw [← card_map_of_injective (f := c.lower.toMonoidHom) c.lower.injective, c.lower_mark_g,
    card_lineCopies _ _ c.lowerLineG_dimension, d.field_card, ← pow_mul]

theorem card_lowerImage_h :
    Nat.card (lowerImage D g h (W D g h ⊓ Setup.conjugate (W D g h) h)) =
      2 ^ (n * s) := by
  rw [← card_map_of_injective (f := c.lower.toMonoidHom) c.lower.injective, c.lower_mark_h,
    card_lineCopies _ _ c.lowerLineH_dimension, d.field_card, ← pow_mul]

theorem card_upperImage : Nat.card (upperImage D g h (W D g h)) = 2 ^ (n * r) := by
  rw [← card_map_of_injective (f := c.upper.toMonoidHom) c.upper.injective, c.upper_mark,
    card_lineCopies _ _ d.point_dimension, d.field_card, ← pow_mul]

end MarkedLayers
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
