module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Card
/-!
# Nonbacktracking walks in a bipartite graph of prescribed valences

After its first edge, a nonbacktracking walk chooses a neighbor other than its
predecessor. A recursive forward-walk type makes this a product of successive
branching factors. An explicit equivalence retains the existing `BasedWalk`
and nonbacktracking predicate. Counting works in locally finite graphs without
assuming the whole vertex set finite.

In the binary Ree application the valences alternate between five and three;
nine-edge paths therefore have cardinalities 20480 and 12288, exactly the two
vertex stabilizer orders.

Source: Aschbacher--Smith, F.4.4--6 and F.4.16, printed pp.274--277 and 282.
-/

@[expose] public section
noncomputable section
namespace SimpleGraph.BasedWalk
universe u
variable {V : Type u} (Γ : SimpleGraph V)

def Forward : ℕ → V → V → Type u
  | 0, _, _ => PUnit
  | n + 1, a, b => Σ c : {c : Γ.neighborSet b // c.val ≠ a}, Forward n b c.val

/-- Nonbacktracking together with avoidance of the vertex immediately before
this walk's origin. The avoidance condition is empty at length zero. -/
def Avoids : {n : ℕ} → {x : V} → V → BasedWalk Γ n x → Prop
  | 0, _, _, _ => True
  | _ + 1, _, a, p => (p.1 : V) ≠ a ∧ p.Nonbacktracking

theorem avoids_cons_iff {n : ℕ} {x a : V} (y : Γ.neighborSet x) (p : BasedWalk Γ n y) :
    Avoids Γ (n := n + 1) (x := x) a ⟨y, p⟩ ↔ (y : V) ≠ a ∧ Avoids Γ (n := n) (x := (y : V)) x p := by
  cases n <;> rfl

def forwardEquiv : (n : ℕ) → (a b : V) → Forward Γ n a b ≃ {p : BasedWalk Γ n b // Avoids Γ a p}
  | 0, a, b => {
      toFun := fun _ => ⟨PUnit.unit, trivial⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  | n + 1, a, b => {
      toFun := fun p => ⟨⟨p.1.val, (forwardEquiv n b p.1.val p.2).val⟩,
        (avoids_cons_iff Γ _ _).mpr ⟨p.1.property, (forwardEquiv n b p.1.val p.2).property⟩⟩
      invFun := fun p => ⟨⟨p.val.1, ((avoids_cons_iff Γ _ _).mp p.property).1⟩,
        (forwardEquiv n b p.val.1).symm ⟨p.val.2, ((avoids_cons_iff Γ _ _).mp p.property).2⟩⟩
      left_inv := by
        rintro ⟨⟨y, hy⟩, p⟩
        exact congrArg (fun q : Forward Γ n b y =>
          (⟨⟨y, hy⟩, q⟩ : Forward Γ (n + 1) a b))
          ((forwardEquiv n b y).symm_apply_apply p)
      right_inv := by
        rintro ⟨⟨y, p⟩, hp⟩
        apply Subtype.ext
        exact congrArg (Sigma.mk y) (congrArg Subtype.val
          ((forwardEquiv n b y).apply_symm_apply ⟨p, ((avoids_cons_iff Γ _ _).mp hp).2⟩)) }

/-- The first edge is unrestricted; all subsequent edges avoid their predecessor. -/
def nonbacktrackingEquivForward (n : ℕ) (x : V) :
    {p : BasedWalk Γ (n + 1) x // p.Nonbacktracking} ≃
      Σ y : Γ.neighborSet x, Forward Γ n x y where
  toFun p := ⟨p.val.1, (forwardEquiv Γ n x p.val.1).symm ⟨p.val.2, by
    cases n <;> exact p.property⟩⟩
  invFun p := ⟨⟨p.1, (forwardEquiv Γ n x p.1 p.2).val⟩, by
    have h := (forwardEquiv Γ n x p.1 p.2).property
    cases n <;> exact h⟩
  left_inv := by
    rintro ⟨⟨y, p⟩, hp⟩
    apply Subtype.ext
    exact congrArg (Sigma.mk y) (congrArg Subtype.val
      ((forwardEquiv Γ n x y).apply_symm_apply ⟨p, by cases n <;> exact hp⟩))
  right_inv := by
    rintro ⟨y, p⟩
    exact congrArg (Sigma.mk y) ((forwardEquiv Γ n x y).symm_apply_apply p)

variable [∀ x, Finite (Γ.neighborSet x)]
instance forwardFinite (n : ℕ) (a b : V) : Finite (Forward Γ n a b) := by
  induction n generalizing a b with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n ih =>
    have := fun c : {c : Γ.neighborSet b // c.val ≠ a} => ih b c.val
    exact inferInstanceAs (Finite (Σ c : {c : Γ.neighborSet b // c.val ≠ a}, Forward Γ n b c.val))

variable (τ : V → Bool) (degree : Bool → ℕ)
variable (hflip : ∀ {a b}, Γ.Adj a b → τ b = !(τ a))
variable (hdegree : ∀ x, Nat.card (Γ.neighborSet x) = degree (τ x))

def forwardCount (degree : Bool → ℕ) : ℕ → Bool → ℕ
  | 0, _ => 1
  | n + 1, b => (degree b - 1) * forwardCount degree n (!b)

include hflip hdegree

theorem card_forward (n : ℕ) (a b : V) (hab : Γ.Adj a b) :
    Nat.card (Forward Γ n a b) = forwardCount degree n (τ b) := by
  classical
  induction n generalizing a b with
  | zero => simp [Forward, forwardCount]
  | succ n ih =>
    let := Fintype.ofFinite (Γ.neighborSet b)
    have hremove : Nat.card {c : Γ.neighborSet b // c.val ≠ a} = degree (τ b) - 1 := by
      have he : {c : Γ.neighborSet b // c.val ≠ a} ≃
          {c : Γ.neighborSet b // c ≠ ⟨a, hab.symm⟩} := Equiv.subtypeEquivRight (by
        intro c
        apply not_congr
        constructor
        · intro h
          apply Subtype.ext
          exact h
        · exact congrArg Subtype.val)
      rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        ← Nat.card_eq_fintype_card, hdegree b]
      simp
    let := Fintype.ofFinite {c : Γ.neighborSet b // c.val ≠ a}
    change Nat.card (Σ c : {c : Γ.neighborSet b // c.val ≠ a}, Forward Γ n b c.val) = _
    rw [Nat.card_sigma]
    have hs : (∑ c : {c : Γ.neighborSet b // c.val ≠ a}, Nat.card (Forward Γ n b c.val)) =
        ∑ _c : {c : Γ.neighborSet b // c.val ≠ a}, forwardCount degree n (!(τ b)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [ih b c.val c.val.property, hflip c.val.property]
    rw [hs]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hremove, forwardCount]
    all_goals rfl

theorem card_nonbacktracking_succ (n : ℕ) (x : V) :
    Nat.card {p : BasedWalk Γ (n + 1) x // p.Nonbacktracking} =
      degree (τ x) * forwardCount degree n (!(τ x)) := by
  classical
  let := Fintype.ofFinite (Γ.neighborSet x)
  rw [Nat.card_congr (nonbacktrackingEquivForward Γ n x), Nat.card_sigma]
  have hs : (∑ y : Γ.neighborSet x, Nat.card (Forward Γ n x y)) =
      ∑ _y : Γ.neighborSet x, forwardCount degree n (!(τ x)) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [card_forward Γ τ degree hflip hdegree n x y y.property, hflip y.property]
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, hdegree x]
  all_goals rfl
end SimpleGraph.BasedWalk
