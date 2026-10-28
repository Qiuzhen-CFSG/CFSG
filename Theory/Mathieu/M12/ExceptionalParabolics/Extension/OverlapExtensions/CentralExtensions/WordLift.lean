module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Basic
/-!
# Homomorphisms from finite word coordinates

A function on an exhaustive word enumeration is multiplicative when it
respects the right Cayley edges. Induction on the word for the right factor
proves multiplicativity. The endpoint parity characters use this construction
with the certified coordinate equivalence and all four actual Cayley edges.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
namespace FiniteWords
variable {G H : Type*} [Group G] [Group H] {n m : ℕ}

/-- A function on checked normal forms is a homomorphism if it respects the
right Cayley edges. Only one edge per element and generator is needed. -/
noncomputable def lift (g : Fin n → G) (words : Fin m → List (Fin n))
    (e : Fin m ≃ G) (he : ∀ i, e i = evaluate g (words i))
    (zero : Fin m) (hz : e zero = 1)
    (step : Fin m → Fin n → Fin m) (hs : ∀ i j, e (step i j) = e i * g j)
    (f : Fin m → H) (v : Fin n → H)
    (hf : f zero = 1) (hstep : ∀ i j, f (step i j) = f i * v j) : G →* H := by
  let F : G → H := fun x => f (e.symm x)
  have hF (i : Fin m) : F (e i) = f i := by simp [F]
  have hFone : F 1 = 1 := by rw [← hz, hF, hf]
  have hFs (x : G) (j : Fin n) : F (x * g j) = F x * v j := by
    obtain ⟨i, rfl⟩ := e.surjective x
    rw [← hs, hF, hF, hstep]
  have hword (x : G) (w : List (Fin n)) :
      F (x * evaluate g w) = F x * evaluate v w := by
    induction w generalizing x with
    | nil => simp only [evaluate, mul_one]
    | cons j w ih => rw [evaluate, ← mul_assoc, ih, hFs, evaluate, mul_assoc]
  refine { toFun := F, map_one' := hFone, map_mul' := ?_ }
  intro x y
  obtain ⟨i, rfl⟩ := e.surjective y
  rw [he, hword]
  have h := hword 1 (words i)
  simpa only [one_mul, hFone] using congrArg (F x * ·) h.symm

theorem lift_element (g : Fin n → G) (words : Fin m → List (Fin n))
    (e : Fin m ≃ G) (he : ∀ i, e i = evaluate g (words i))
    (zero : Fin m) (hz : e zero = 1)
    (step : Fin m → Fin n → Fin m) (hs : ∀ i j, e (step i j) = e i * g j)
    (f : Fin m → H) (v : Fin n → H)
    (hf : f zero = 1) (hstep : ∀ i j, f (step i j) = f i * v j) (i : Fin m) :
    lift g words e he zero hz step hs f v hf hstep (e i) = f i := by
  change f (e.symm (e i)) = f i
  rw [e.symm_apply_apply]
end FiniteWords


end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
