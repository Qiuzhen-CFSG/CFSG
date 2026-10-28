module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.FourRelators.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.FourRelators.Certificate.Context

/-!
# Realization of the local coset certificate

Every relator loop is an inverse or cyclic rotation of a defining word of
`Presented`. The only subgroup loop is its second generator. These are
equalities in the smaller abstract presentation, independently of any claim
that its candidate relations lift to the original M24 presentation.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.FourRelators.Certificate
open Subgroup.CosetWordCertificate

def certificateGenerator (n : ℕ) : Presented :=
  localGenerator (if n = 0 then 0 else 1)

@[simp] theorem certificateGenerator_fin (i : Fin 2) :
    certificateGenerator i.val = localGenerator i := by
  fin_cases i <;> rfl

private theorem eval_map_letters (w : Word (Fin 2)) :
    eval certificateGenerator (w.map fun a => (a.1.val, a.2)) = eval localGenerator w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, eval_cons, certificateGenerator_fin, ih]

private theorem originals_exact : ∀ i : Fin 4,
    originals i = (relatorLetters i).map (fun a => (a.1.val, a.2)) := by
  decide +kernel

private theorem original_eval (i : Fin 4) : eval certificateGenerator (originals i) = 1 := by
  rw [originals_exact, eval_map_letters, generator_relations]

def variant (w : Word Nat) (inv : Bool) (offset : Nat) : Word Nat :=
  (if inv then FreeGroup.invRev w else w).rotate offset

private theorem eval_variant (w : Word Nat) (hw : eval certificateGenerator w = 1)
    (inv : Bool) (offset : Nat) : eval certificateGenerator (variant w inv offset) = 1 := by
  have h : eval certificateGenerator (if inv then FreeGroup.invRev w else w) = 1 := by
    cases inv <;> simp [hw, eval_invRev]
  simpa [eval, FreeGroup.lift_mk, variant, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one (by simpa [eval, FreeGroup.lift_mk] using h) offset

set_option maxRecDepth 10000 in
private theorem variants_exact : ∀ i : Fin 78,
    relatorTable i.val = variant (originals (variantTable i.val).1)
      (variantTable i.val).2.1 (variantTable i.val).2.2 := by decide +kernel

private theorem relator_ok (r : Nat) : eval certificateGenerator (relatorWords r) = 1 := by
  let i : Fin 78 := ⟨min r 77, by omega⟩
  rw [relatorWords, variants_exact i]
  exact eval_variant _ (original_eval _) _ _

/-- The complete context is sound in the smaller abstract presentation. -/
theorem certificate_valid :
    Valid context localCyclic certificateGenerator (definitions.repr certificateGenerator) := by
  apply definitions.valid
  · intro a ha
    have he : a = (1, true) := beq_iff_eq.mp ha
    subst a
    simp [certificateGenerator, localCyclic]
  · exact relator_ok

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.FourRelators.Certificate
