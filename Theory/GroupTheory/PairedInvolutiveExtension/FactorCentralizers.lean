module

public import Theory.GroupTheory.PairedInvolutiveExtension.Centralizers
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Centralizing one factor in a paired involutive extension

If K is centerless and the simultaneous automorphism is outer, the first
full factor has centralizer exactly the second factor. Interchanging actors
cannot centralize a nontrivial factor, and the graph actor would make the
automorphism inner. Intersecting with the paired subgroup based on D gives
an explicit multiplicative equivalence with D, with inverse d ↦ (1,d).

Source application: the core embedding in the paired Sylow model in
Aschbacher--Smith, proof of 2.4.34, printed p.548 of the 1 March 2004 manuscript.
-/

@[expose] public section
namespace Theory.GroupTheory.PairedInvolutiveExtension
open Subgroup
variable {K : Type*} [Group K] (α : MulAut K) (hα : Function.Involutive α)
private theorem mk_eq_iff (a b c d : K) (p q r s : Bit) :
    mk α hα a b p q = mk α hα c d r s ↔ a = c ∧ b = d ∧ p = r ∧ q = s := by
  simp [mk, SemidirectProduct.ext_iff, Prod.ext_iff, and_assoc]
private theorem mem_firstFactorCentralizer (x : Model α hα) :
    x ∈ centralizer (Set.range (fun a : K => base α hα a 1)) ↔
      ∀ a, base α hα a 1 * x = x * base α hα a 1 := by
  simp only [mem_centralizer_iff, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
private theorem inner_of_twisted_commute (a : K) (h : ∀ c, c * a = a * α c) :
    α = MulAut.conj a⁻¹ := by
  ext c
  change α c = a⁻¹ * c * (a⁻¹)⁻¹
  calc
    α c = a⁻¹ * (a * α c) := by group
    _ = a⁻¹ * (c * a) := by rw [h c]
    _ = a⁻¹ * c * (a⁻¹)⁻¹ := by group

private theorem mem_firstFactorCentralizer_mk [Nontrivial K]
    (hcenter : center K = ⊥) (houter : ∀ c, α ≠ MulAut.conj c)
    (a b : K) (p q : Bit) :
    mk α hα a b p q ∈ centralizer (Set.range (fun c : K => base α hα c 1)) ↔
      a = 1 ∧ p = 1 ∧ q = 1 := by
  rw [mem_firstFactorCentralizer]
  rcases bit_cases p with rfl | rfl <;> rcases bit_cases q with rfl | rfl
  · simp only [base, mk_mul, action_one, one_mul, mul_one, mk_eq_iff, and_true]
    constructor
    · intro hc
      have ha : a ∈ center K := mem_center_iff.mpr hc
      rwa [hcenter, mem_bot] at ha
    · rintro rfl c
      simp
  · simp only [base, mk_mul, action_one, action_swap, one_mul, mul_one, mk_eq_iff,
      on_ne, and_false, and_true, iff_false]
    intro hc
    obtain ⟨c,hcne⟩ := exists_ne (1 : K)
    exact hcne (mul_right_cancel (show c*a=1*a by simpa only [one_mul] using (hc c).1))
  · simp only [base, mk_mul, action_one, action_graph, one_mul, mul_one, map_one,
      mk_eq_iff, on_ne, and_false, and_true, iff_false]
    intro hc
    exact houter a⁻¹ (inner_of_twisted_commute α a hc)
  · simp only [base, mk_mul, action_one, action_graphSwap, one_mul, mul_one, map_one,
      mk_eq_iff, on_ne, and_false, and_true, iff_false]
    intro hc
    obtain ⟨c,hcne⟩ := exists_ne (1 : K)
    exact hcne (mul_right_cancel (show c*a=1*a by simpa only [one_mul] using (hc c).1))
/-- Centralizing the first full factor forces a pure second-factor element. -/
theorem mem_firstFactorCentralizer_iff [Nontrivial K]
    (hcenter : center K = ⊥) (houter : ∀ c, α ≠ MulAut.conj c)
    (x : Model α hα) :
    x ∈ centralizer (Set.range (fun c : K => base α hα c 1)) ↔
      x = base α hα 1 x.left.2 := by
  rcases x with ⟨⟨a,b⟩,⟨p,q⟩⟩
  change mk α hα a b p q ∈ _ ↔ mk α hα a b p q = mk α hα 1 b 1 1
  rw [mem_firstFactorCentralizer_mk α hα hcenter houter,mk_eq_iff]
  simp only [true_and]

/-- The literal right-base map identifies D with the factor centralizer intersection. -/
def rightBaseEquiv [Nontrivial K]
    (hcenter : center K = ⊥) (houter : ∀ c, α ≠ MulAut.conj c)
    (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) :
    D ≃* (centralizer (Set.range (fun c : K => base α hα c 1)) ⊓ subgroup α hα D hD :
      Subgroup (Model α hα)) where
  toFun d := ⟨base α hα 1 d,
    (mem_firstFactorCentralizer_iff α hα hcenter houter _).mpr rfl, D.one_mem, d.2⟩
  invFun x := ⟨x.1.left.2,x.2.2.2⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext ((mem_firstFactorCentralizer_iff α hα hcenter houter x).mp x.2.1).symm
  map_mul' d e := by
    apply Subtype.ext
    change base α hα 1 (d.val*e.val) = base α hα 1 d * base α hα 1 e
    simp [base]

/-- Reading the second coordinate identifies the factor centralizer intersection with D. -/
def firstFactorCentralizerEquiv [Nontrivial K]
    (hcenter : center K = ⊥) (houter : ∀ c, α ≠ MulAut.conj c)
    (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) :
    (centralizer (Set.range (fun c : K => base α hα c 1)) ⊓ subgroup α hα D hD :
      Subgroup (Model α hα)) ≃* D :=
  (rightBaseEquiv α hα hcenter houter D hD).symm
@[simp] theorem firstFactorCentralizerEquiv_apply [Nontrivial K]
    (hcenter : center K = ⊥) (houter : ∀ c, α ≠ MulAut.conj c)
    (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D)
    (x : (centralizer (Set.range (fun c : K => base α hα c 1)) ⊓ subgroup α hα D hD :
      Subgroup (Model α hα))) :
    (firstFactorCentralizerEquiv α hα hcenter houter D hD x : K) = x.val.left.2 := rfl

@[simp] theorem firstFactorCentralizerEquiv_symm_apply [Nontrivial K]
    (hcenter : center K = ⊥) (houter : ∀ c, α ≠ MulAut.conj c)
    (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) (d : D) :
    ((firstFactorCentralizerEquiv α hα hcenter houter D hD).symm d : Model α hα) =
      base α hα 1 d := rfl

theorem card_firstFactorCentralizer [Nontrivial K]
    (hcenter : center K = ⊥) (houter : ∀ c, α ≠ MulAut.conj c)
    (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) :
    Nat.card (centralizer (Set.range (fun c : K => base α hα c 1)) ⊓ subgroup α hα D hD :
      Subgroup (Model α hα)) = Nat.card D :=
  Nat.card_congr (firstFactorCentralizerEquiv α hα hcenter houter D hD).toEquiv
end Theory.GroupTheory.PairedInvolutiveExtension
