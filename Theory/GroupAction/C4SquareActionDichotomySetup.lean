module

public import Theory.GroupAction.C4SquareHallJankoActions

/-!
# Finite coordinates for the C₄-square action dichotomy

An involution-fixing automorphism has the form `I + 2M` for a binary matrix
`M`. Two such automorphisms give four words; adjoining one outer
automorphism gives the four words in its coset. The finite certificate uses
only these words, their values on the sixteen base elements, and a marked
basis. Its output reconstructs either of the two action frames.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

set_option synthInstance.maxSize 4096

@[expose] public section
namespace C4SquareExtension.ActionDichotomy

abbrev Code := Fin 2 × Fin 2 × Fin 2 × Fin 2
abbrev OuterCode := Model × Model

def zeroCode : Code := (0, 0, 0, 0)
def e₁ : Model := (Multiplicative.ofAdd 1, 1)
def e₂ : Model := (1, Multiplicative.ofAdd 1)

def congruenceAct (m : Code) (x : Model) : Model :=
  (Multiplicative.ofAdd ((1 + 2 * (m.1.val : ZMod 4)) * x.1.toAdd +
    2 * (m.2.1.val : ZMod 4) * x.2.toAdd),
   Multiplicative.ofAdd (2 * (m.2.2.1.val : ZMod 4) * x.1.toAdd +
    (1 + 2 * (m.2.2.2.val : ZMod 4)) * x.2.toAdd))

theorem congruenceAct_involutive :
    ∀ m : Code, ∀ x : Model, congruenceAct m (congruenceAct m x) = x := by decide

def congruenceAut (m : Code) : MulAut Model where
  toFun := congruenceAct m
  invFun := congruenceAct m
  left_inv := congruenceAct_involutive m
  right_inv := congruenceAct_involutive m
  map_mul' x y := by
    ext <;> simp only [congruenceAct, Prod.fst_mul, Prod.snd_mul,
      toAdd_mul, toAdd_ofAdd] <;> ring

/-- The four words in two congruence generators. -/
def word (m n : Code) (i : Fin 4) : MulAut Model :=
  if i = 0 then 1 else if i = 1 then congruenceAut m else
    if i = 2 then congruenceAut n else congruenceAut m * congruenceAut n

/-- Evaluation of a homomorphism from its two columns. -/
def outerAct (p : OuterCode) (x : Model) : Model :=
  p.1 ^ x.1.toAdd.val * p.2 ^ x.2.toAdd.val

def outerWord (m n : Code) (p : OuterCode) (i : Fin 4) (x : Model) : Model :=
  word m n i (outerAct p x)

def GoodBasis (a b : Model) : Prop :=
  a ^ 2 ≠ 1 ∧ b ^ 2 ≠ 1 ∧ a ^ 2 ≠ b ^ 2

instance (a b : Model) : Decidable (GoodBasis a b) := by
  unfold GoodBasis
  infer_instance

/-- A finite input contract. The last two clauses say that the outer square
lies in the four words and the outer action normalizes their group. -/
def Valid (m n : Code) (p : OuterCode) : Prop :=
  m ≠ zeroCode ∧ n ≠ zeroCode ∧ m ≠ n ∧
  (∀ i : Fin 4, i ≠ 0 → ∃ a : Model, word m n i a = a⁻¹ ∧ a ^ 2 ≠ 1) ∧
  GoodBasis p.1 p.2 ∧
  (∃ a : Model, a ^ 2 = 1 ∧ outerAct p a ≠ a) ∧
  (∃ i : Fin 4, ∀ x : Model, outerAct p (outerAct p x) = word m n i x) ∧
  (∀ i : Fin 4, ∃ j : Fin 4, ∀ x : Model,
    outerAct p (word m n i x) = word m n j (outerAct p x))

instance (m n : Code) (p : OuterCode) : Decidable (Valid m n p) := by
  unfold Valid
  infer_instance

/-- The six equations for the Hall–Janko alternative. -/
def HallWitness (m n : Code) (p : OuterCode) (a b : Model) (i j k : Fin 4) : Prop :=
  word m n i a = a⁻¹ * b ^ 2 ∧ word m n i b = b⁻¹ ∧
  word m n j a = a * b ^ 2 ∧ word m n j b = a ^ 2 * b ∧
  outerWord m n p k a = a * b ∧ outerWord m n p k b = b⁻¹

instance (m n : Code) (p : OuterCode) (a b : Model) (i j k : Fin 4) :
    Decidable (HallWitness m n p a b i j k) := by
  unfold HallWitness
  infer_instance

/-- Partial inversions exchanged by the outer action. Conjugation is written
as an intertwining identity, so no inverse matrix needs to be computed. -/
def SplitWitness (m n : Code) (p : OuterCode) (a b : Model) (i j k : Fin 4) : Prop :=
  word m n i a = a⁻¹ ∧ word m n i b = b ∧
  word m n j a = a ∧ word m n j b = b⁻¹ ∧
  outerWord m n p k (a ^ 2) = b ^ 2 ∧
  outerWord m n p k (b ^ 2) = a ^ 2 ∧
  (∀ x : Model, outerWord m n p k (word m n i x) =
    word m n j (outerWord m n p k x)) ∧
  (∀ x : Model, outerWord m n p k (word m n j x) =
    word m n i (outerWord m n p k x))

instance (m n : Code) (p : OuterCode) (a b : Model) (i j k : Fin 4) :
    Decidable (SplitWitness m n p a b i j k) := by
  unfold SplitWitness
  infer_instance

def Witness (m n : Code) (p : OuterCode) : Prop :=
  ∃ a b : Model, GoodBasis a b ∧
    ((∃ i j k : Fin 4, HallWitness m n p a b i j k) ∨
     (∃ i j k : Fin 4, SplitWitness m n p a b i j k))

instance (m n : Code) (p : OuterCode) : Decidable (Witness m n p) := by
  unfold Witness
  infer_instance

/-- The bridge from subgroup hypotheses to a finite input. -/
structure EncodedActionPair (H K : Subgroup (MulAut Model)) where
  m : Code
  n : Code
  t : MulAut Model
  words_mem : ∀ i : Fin 4, word m n i ∈ H
  t_mem : t ∈ K
  valid : Valid m n (t e₁, t e₂)

theorem model_decomp : ∀ x : Model,
    x = e₁ ^ x.1.toAdd.val * e₂ ^ x.2.toAdd.val := by decide

theorem aut_eq_outerAct (t : MulAut Model) (x : Model) :
    t x = outerAct (t e₁, t e₂) x := by
  conv_lhs => rw [model_decomp x, map_mul, map_pow, map_pow]
  rfl

theorem aut_ext (f g : MulAut Model) (h₁ : f e₁ = g e₁) (h₂ : f e₂ = g e₂) :
    f = g := by
  apply MulEquiv.ext
  intro x
  rw [aut_eq_outerAct f, aut_eq_outerAct g, h₁, h₂]

theorem congruenceAut_injective : Function.Injective congruenceAut := by
  intro m n h
  have h₁ := congrArg (fun f : MulAut Model => f e₁) h
  have h₂ := congrArg (fun f : MulAut Model => f e₂) h
  exact (by decide : ∀ m n : Code,
    congruenceAct m e₁ = congruenceAct n e₁ →
    congruenceAct m e₂ = congruenceAct n e₂ → m = n) m n h₁ h₂

theorem congruenceAut_zero : congruenceAut zeroCode = 1 := by
  apply aut_ext <;> decide

theorem congruenceAut_fix : ∀ m : Code, ∀ x : Model,
    x ^ 2 = 1 → congruenceAut m x = x := by decide

/-- Every automorphism fixing the involutions is one of the sixteen binary
congruence automorphisms. -/
theorem exists_congruenceAut (f : MulAut Model)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x) :
    ∃ m : Code, f = congruenceAut m := by
  have h₁ : (f e₁) ^ 2 = e₁ ^ 2 := by
    rw [← map_pow]
    exact hf _ (by decide)
  have h₂ : (f e₂) ^ 2 = e₂ ^ 2 := by
    rw [← map_pow]
    exact hf _ (by decide)
  obtain ⟨m, hm₁, hm₂⟩ := (by decide : ∀ a b : Model,
    a ^ 2 = e₁ ^ 2 → b ^ 2 = e₂ ^ 2 →
    ∃ m : Code, a = congruenceAct m e₁ ∧ b = congruenceAct m e₂)
      (f e₁) (f e₂) h₁ h₂
  exact ⟨m, aut_ext _ _ hm₁ hm₂⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem goodBasis_decomp : ∀ a b : Model, GoodBasis a b → ∀ x : Model,
    ∃ i j : Fin 4, x = a ^ i.val * b ^ j.val := by decide

theorem goodBasis_base {a b : Model} (h : GoodBasis a b) :
    Subgroup.closure ({a,b} : Set Model) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i,j,rfl⟩ := goodBasis_decomp a b h x
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

set_option maxRecDepth 4096 in
private theorem goodBasis_squares : ∀ a b : Model, GoodBasis a b →
    ∀ x : Model, x ^ 2 = 1 → x = 1 ∨ x = a ^ 2 ∨ x = b ^ 2 ∨ x = a ^ 2 * b ^ 2 := by
  decide

theorem model_four : ∀ a : Model, a ^ 4 = 1 := by decide

theorem goodBasis_omega {a b : Model} (h : GoodBasis a b) :
    omega₁ Model (p := 2) = Subgroup.closure ({a ^ 2,b ^ 2} : Set Model) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases goodBasis_squares a b h x (by simpa using hx) with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases (by simpa using hx : x = a ^ 2 ∨ x = b ^ 2) with rfl | rfl
    · apply Subgroup.subset_closure
      simpa [← pow_mul] using model_four a
    · apply Subgroup.subset_closure
      simpa [← pow_mul] using model_four b

/-- Reconstruct an actual action frame from the checked coordinate output. -/
theorem actions_of_witness {H K : Subgroup (MulAut Model)} (hHK : H ≤ K)
    (d : EncodedActionPair H K) (hw : Witness d.m d.n (d.t e₁, d.t e₂)) :
    Nonempty (HallJankoAutActions H K) ∨ Nonempty (SplitInversionAutActions H K) := by
  obtain ⟨a,b,hbasis,hw⟩ := hw
  have hout (i : Fin 4) (x : Model) :
      (word d.m d.n i * d.t) x = outerWord d.m d.n (d.t e₁, d.t e₂) i x := by
    change word d.m d.n i (d.t x) = _
    rw [aut_eq_outerAct d.t x]
    rfl
  have htmem (i : Fin 4) : word d.m d.n i * d.t ∈ K :=
    K.mul_mem (hHK (d.words_mem i)) d.t_mem
  rcases hw with ⟨i,j,k,hu₁,hu₂,hv₁,hv₂,ht₁,ht₂⟩ |
    ⟨i,j,k,hu₁,hu₂,hv₁,hv₂,ht₁,ht₂,htu,htv⟩
  · exact Or.inl ⟨{
      a := a, b := b, a_four := model_four a, b_four := model_four b
      ba := mul_comm b a, base := goodBasis_base hbasis, four := goodBasis_omega hbasis
      u := word d.m d.n i, v := word d.m d.n j, t := word d.m d.n k * d.t
      u_mem := d.words_mem i, v_mem := d.words_mem j, t_mem := htmem k
      ua := hu₁, ub := hu₂, va := hv₁, vb := hv₂
      ta := (hout k a).trans ht₁, tb := (hout k b).trans ht₂ }⟩
  · refine Or.inr ⟨{
      a := a, b := b, a_four := model_four a, b_four := model_four b
      ba := mul_comm b a, base := goodBasis_base hbasis
      a_two_ne := hbasis.1, b_two_ne := hbasis.2.1, squares_ne := hbasis.2.2
      u := word d.m d.n i, v := word d.m d.n j, t := word d.m d.n k * d.t
      u_mem := d.words_mem i, v_mem := d.words_mem j, t_mem := htmem k
      ua := hu₁, ub := hu₂, va := hv₁, vb := hv₂
      ta_two := (hout k (a ^ 2)).trans ht₁, tb_two := (hout k (b ^ 2)).trans ht₂
      tut := ?_, tvt := ?_ }⟩
    · apply (mul_inv_eq_iff_eq_mul).mpr
      apply MulEquiv.ext
      intro x
      change (word d.m d.n k * d.t) (word d.m d.n i x) =
        word d.m d.n j ((word d.m d.n k * d.t) x)
      simpa only [hout] using htu x
    · apply (mul_inv_eq_iff_eq_mul).mpr
      apply MulEquiv.ext
      intro x
      change (word d.m d.n k * d.t) (word d.m d.n j x) =
        word d.m d.n i ((word d.m d.n k * d.t) x)
      simpa only [hout] using htv x

end C4SquareExtension.ActionDichotomy
