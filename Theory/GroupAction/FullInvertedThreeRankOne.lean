module
public import Theory.Representation.InvertedOddSubgroup
public import Theory.GroupAction.CardTwoDisplacementInvolution

/-!
# A full inverted C3 action with a displacement line

Let r and t act on a finite elementary abelian two-group W, with r³=1
and t inverting r. If r has full displacement and the displacement of t
has order two, then W has order four. No faithful-action, acting-group
order, or separately assumed involution condition is needed.

The rank-one displacement theorem first makes t an involution. The cyclic
r-subgroup has odd order, and coprime splitting together with its full
displacement makes its fixed subgroup trivial. Inversion extends from r
to all its powers. The existing inverted-odd-subgroup theorem then gives
|W|=|[W,t]|²=4.

Full displacement is essential: adjoining any trivial summand to a natural
four-element S3 module preserves the involution displacement line while
increasing the module order. The statement explicitly excludes that case.
This source-neutral action theorem supplies the cardinal step in the small
Section Ten quotient action of Stellmacher (10.1), Journal of Algebra190
(1997); the consumer supplies the actual module and quotient operators.
-/

open scoped IsMulCommutative

public theorem card_four_of_full_inverted_three_rank_one
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (r t : MulAut W) (hr : r ^ 3 = 1)
    (hinv : t * r * t⁻¹ = r⁻¹)
    (hfull : commutatorAction (Subgroup.zpowers r) W = ⊤)
    (hline : Nat.card (commutatorAction (Subgroup.zpowers t) W) = 2) :
    Nat.card W = 4 := by
  let F := Subgroup.zpowers r
  have hFdiv : Nat.card F ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hr
  have hFodd : Odd (Nat.card F) := Odd.of_dvd_nat (by decide : Odd 3) hFdiv
  have hcop : Nat.Coprime (Nat.card F) (Nat.card W) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact hFodd.coprime_two_right.pow_right n
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := W) (A := F) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have hfixed : FixedPoints.subgroup F W = ⊥ := by
    have hh := hcompl.inf_eq_bot
    rw [hfull, inf_top_eq] at hh
    exact hh
  have ht := isInvolution_of_card_two_displacement t hline
  have hinvF : ∀ a : F, t * (a : MulAut W) * t⁻¹ = (a : MulAut W)⁻¹ := by
    rintro ⟨a,ha⟩
    obtain ⟨n,rfl⟩ := ha
    change (MulAut.conj t) (r ^ n) = (r ^ n)⁻¹
    rw [map_zpow]
    change (t * r * t⁻¹) ^ n = (r ^ n)⁻¹
    rw [hinv, inv_zpow]
  have hcard := invertedOddSubgroup_card_eq_commutator_sq F hFodd t ht hinvF hfixed
  rw [hline] at hcard
  exact hcard

