module
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# Commuting actions controlled by a full-rank involution

Let x be an involution of a finite elementary abelian two-group W.
Suppose the order of W is the square of the order of its x-fixed subgroup.
If a subgroup B of automorphisms commutes with x and fixes [W,x]
pointwise, then [W,B] is contained in [W,x]. The literal automorphisms
and their canonical actions are retained throughout.

Involution rank-nullity and quadraticity identify [W,x] with C_W(x).
For b in B, the identity bx=xb and fixation of w⁻¹*x(w) show that
w⁻¹*b(w) is fixed by x. Every B-action commutator therefore belongs to
C_W(x)=[W,x]. No solvability or odd-order acting group is needed.

This elementary transfer supplies the four- and sixteen-element quotient
branches after the application of (1.3) in Stellmacher (9.1), Journal of
Algebra 190 (1997), p.47. The source-specific cardinal and centralization
hypotheses belong to the graph adapter.
-/

namespace Subgroup

/-- A commuting action that fixes a full-rank involution commutator has no
larger action commutator. -/
public theorem commutatorAction_le_of_commuting_full_rank_involution
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (x : MulAut W) (hx : x ≠ 1 ∧ x ^ 2 = 1) (B : Subgroup (MulAut W))
    (hcomm : ∀ b ∈ B, Commute b x)
    (hfix : ∀ b ∈ B, ∀ w ∈ commutatorAction (zpowers x) W, b w = w)
    (hcard : Nat.card W = Nat.card (FixedPoints.subgroup (zpowers x) W) ^ 2) :
    commutatorAction B W ≤ commutatorAction (zpowers x) W := by
  have hW : Nontrivial W := by
    by_contra hn
    have _ : Subsingleton W := not_nontrivial_iff_subsingleton.mp hn
    exact hx.1 (MulEquiv.ext (fun _ => Subsingleton.elim _ _))
  let _ := hW
  have hXcard : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx.2 hx.1
  let xX : zpowers x := ⟨x, mem_zpowers x⟩
  have hxX : xX ≠ 1 ∧ xX ^ 2 = 1 :=
    ⟨fun h => hx.1 (congrArg Subtype.val h), Subtype.ext hx.2⟩
  obtain ⟨hprod, hle⟩ := card_two_action_fixed_commutator_card_data (U := W) xX hxX hXcard
  have hsize : Nat.card (commutatorAction (zpowers x) W) =
      Nat.card (FixedPoints.subgroup (zpowers x) W) := by
    rw [hcard, pow_two] at hprod
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hprod).symm
  have heq : commutatorAction (zpowers x) W =
      FixedPoints.subgroup (zpowers x) W := eq_of_le_of_card_ge hle hsize.ge
  rw [heq, commutatorAction_eq_closure]
  apply (closure_le (K := FixedPoints.subgroup (zpowers x) W)).mpr
  rintro _ ⟨b, w, rfl⟩ a
  have hd : w⁻¹ * (x w) ∈ commutatorAction (zpowers x) W := by
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨xX, w, rfl⟩
  have hb := hfix b b.property _ hd
  have hbx : (b : MulAut W) (x w) = x ((b : MulAut W) w) :=
    DFunLike.congr_fun (hcomm b b.property).eq w
  have hfixed : x (w⁻¹ * (b : MulAut W) w) = w⁻¹ * (b : MulAut W) w := by
    rw [map_mul, map_inv]
    rw [map_mul, map_inv, hbx] at hb
    have hexpr : x ((b : MulAut W) w) = (b : MulAut W) w * (w⁻¹ * x w) :=
      inv_mul_eq_iff_eq_mul.mp hb
    rw [hexpr]
    calc
      (x w)⁻¹ * ((b : MulAut W) w * (w⁻¹ * x w)) =
          ((x w)⁻¹ * x w) * (w⁻¹ * (b : MulAut W) w) := by ac_rfl
      _ = w⁻¹ * (b : MulAut W) w := by simp
  exact smul_eq_self_of_mem_zpowers a.property hfixed

end Subgroup
