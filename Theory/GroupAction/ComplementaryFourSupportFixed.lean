module
public import Theory.GroupAction.CardTwoDisplacementInvolution
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Fixed points on complementary four-element supports

Let a finite elementary abelian two-group be the product of two complementary
subgroups of order four. Suppose two automorphisms have displacement of order
two in their respective supports and each fixes the opposite support. Their
common fixed subgroup is exactly the join of the two displacement lines and
has order four. The order-two displacement theorem supplies involutivity, so
no separate assumptions about the automorphism orders are required.

The whole group has order sixteen. Rank-nullity makes each cyclic fixed
subgroup have order eight. Cross-fixing and the support decomposition show
that the fixed subgroups generate the whole group, so the subgroup product
formula gives their intersection order four. The disjoint displacement lines
lie in that intersection, and cardinality gives equality.

This independent action-theoretic calculation is used for the paired canonical
transvection supports on the terminal quotient V/Z in Stellmacher (9.5),
Journal of Algebra 190 (1997), printed pp.52–53. The graph application supplies
the actual supports and induced automorphisms separately.
-/

open scoped IsMulCommutative
namespace MulAut

private theorem cyclic_fixed_of_fixed
    {W : Type*} [Group W] (a : MulAut W) (x : W) (hx : a x = x) :
    x ∈ FixedPoints.subgroup (Subgroup.zpowers a) W := by
  intro mover
  exact smul_eq_self_of_mem_zpowers mover.property hx

private theorem displacement_fixed_data
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (a : MulAut W)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers a) W) = 2) :
    Nat.card W = 2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) W) ∧
      commutatorAction (Subgroup.zpowers a) W ≤
        FixedPoints.subgroup (Subgroup.zpowers a) W := by
  have ha := isInvolution_of_card_two_displacement a hrank
  let _ : Nontrivial W := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    let _ := hsub
    apply ha.1
    ext x
    exact Subsingleton.elim _ _
  let generator : Subgroup.zpowers a := ⟨a, Subgroup.mem_zpowers a⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun h => ha.1 (congrArg Subtype.val h), Subtype.ext ha.2⟩
  have hcyclic : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha.2 ha.1]
  obtain ⟨hcard, hle⟩ := card_two_action_fixed_commutator_card_data
    (U := W) generator hgenerator hcyclic
  exact ⟨by simpa only [hrank, Nat.mul_comm] using hcard, hle⟩

/-- Complementary four-element supports determine the exact common fixed subgroup. -/
public theorem complementary_four_support_common_fixed
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (A B : Subgroup W) (hcompl : IsCompl A B)
    (hA : Nat.card A = 4) (hB : Nat.card B = 4)
    (a b : MulAut W)
    (harank : Nat.card (commutatorAction (Subgroup.zpowers a) W) = 2)
    (hbrank : Nat.card (commutatorAction (Subgroup.zpowers b) W) = 2)
    (haA : commutatorAction (Subgroup.zpowers a) W ≤ A)
    (hbB : commutatorAction (Subgroup.zpowers b) W ≤ B)
    (haB : ∀ x ∈ B, a x = x) (hbA : ∀ x ∈ A, b x = x) :
    FixedPoints.subgroup (Subgroup.zpowers a) W ⊓
        FixedPoints.subgroup (Subgroup.zpowers b) W =
      commutatorAction (Subgroup.zpowers a) W ⊔
        commutatorAction (Subgroup.zpowers b) W ∧
    Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) W ⊓
      FixedPoints.subgroup (Subgroup.zpowers b) W : Subgroup W) = 4 ∧
    Nat.card (commutatorAction (Subgroup.zpowers a) W ⊔
      commutatorAction (Subgroup.zpowers b) W : Subgroup W) = 4 := by
  let Fa := FixedPoints.subgroup (Subgroup.zpowers a) W
  let Fb := FixedPoints.subgroup (Subgroup.zpowers b) W
  let Da := commutatorAction (Subgroup.zpowers a) W
  let Db := commutatorAction (Subgroup.zpowers b) W
  have hnorm (L K : Subgroup W) : K ≤ Subgroup.normalizer (L : Set W) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hW : Nat.card W = 16 := by
    have hh := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint A B (hnorm A B)
      hcompl.disjoint
    rw [hcompl.sup_eq_top, Subgroup.card_top, hA, hB] at hh
    exact hh
  obtain ⟨hacard, haFix⟩ := displacement_fixed_data a harank
  obtain ⟨hbcard, hbFix⟩ := displacement_fixed_data b hbrank
  have hFacard : Nat.card Fa = 8 := by change Nat.card W = 2 * Nat.card Fa at hacard; omega
  have hFbcard : Nat.card Fb = 8 := by change Nat.card W = 2 * Nat.card Fb at hbcard; omega
  have hBfa : B ≤ Fa := fun x hx => cyclic_fixed_of_fixed a x (haB x hx)
  have hAfb : A ≤ Fb := fun x hx => cyclic_fixed_of_fixed b x (hbA x hx)
  have hFjoin : Fa ⊔ Fb = ⊤ := by
    apply top_unique
    rw [← hcompl.sup_eq_top]
    exact sup_le (hAfb.trans le_sup_right) (hBfa.trans le_sup_left)
  have hFcard : Nat.card (Fa ⊓ Fb : Subgroup W) = 4 := by
    have hh := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Fa Fb (hnorm Fa Fb)
    rw [hFacard, hFbcard, hFjoin, Subgroup.card_top, hW] at hh
    omega
  have hDdisjoint : Disjoint Da Db := hcompl.disjoint.mono haA hbB
  have hDcard : Nat.card (Da ⊔ Db : Subgroup W) = 4 := by
    rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint Da Db (hnorm Da Db) hDdisjoint]
    exact congrArg₂ (· * ·) harank hbrank
  have hDle : Da ⊔ Db ≤ Fa ⊓ Fb :=
    sup_le (le_inf haFix (haA.trans hAfb)) (le_inf (hbB.trans hBfa) hbFix)
  have heq : Fa ⊓ Fb = Da ⊔ Db :=
    (Subgroup.eq_of_le_of_card_ge hDle (by omega)).symm
  exact ⟨heq, hFcard, hDcard⟩

end MulAut
