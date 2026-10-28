module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# The standard semidihedral group and recognition by its presentation

For `n ≥ 4`, `Semidihedral.StandardModel n hn` is the explicit semidirect product
`C_(2^(n-1)) ⋊ C₂`, with cyclic factors modeled by multiplicative copies of
`ZMod`. The nonidentity element of `C₂` acts by exponent `2^(n-2)-1`.
The exponent squares to one modulo `2^(n-1)`, which constructs the automorphism
and makes the action well-defined. The underlying set is the product of the
two cyclic factors, so the group has cardinality `2^n`. Its canonical generators
have the required orders, satisfy the conjugation relation, and generate it.

`Semidihedral.standardModel_equiv_of_presentation` identifies any group of the
same cardinality with this fixed model when it has the stated presentation.
The cyclic homomorphisms sending the canonical generators to the supplied
ones extend over the semidirect product. Generation makes the resulting map
surjective, and equality of finite cardinalities makes it an isomorphism.

Source: Alperin–Brauer–Gorenstein, *Finite Groups with Quasi-Dihedral and Wreathed
Sylow 2-Subgroups*, Chapter I, article p.2
(`refs/latex/alperin-brauer-gorenstein-pages/page-003.tex`). Our order parameter
is one larger than theirs. The involution makes their conjugation convention
equivalent to the displayed relation here. This supplies the standard model
needed for the semidihedral alternative in Aschbacher–Smith, I.7.7(5a), printed
p.427 / PDF p.438 of `refs/quasithin.pdf`.
-/

namespace Semidihedral

private def cyclicHom {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (a : G) (ha : a ^ m = 1) : Multiplicative (ZMod m) →* G where
  toFun i := a ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change a ^ (i.toAdd + j.toAdd).val = a ^ i.toAdd.val * a ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ ha).symm

private theorem cyclicHom_one {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (a : G) (ha : a ^ m = 1) : cyclicHom a ha (.ofAdd 1) = a := by
  change a ^ (1 : ZMod m).val = a
  rw [← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod 1 ha, pow_one]

private theorem exponent_square {n : ℕ} (hn : 4 ≤ n) :
    (↑(2 ^ (n - 2) - 1 : ℕ) : ZMod (2 ^ (n - 1))) ^ 2 = 1 := by
  have hp : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
  have he : n - 1 = (n - 2) + 1 := by omega
  have he' : n - 2 = (n - 3) + 1 := by omega
  have hz : (2 : ZMod (2 ^ (n - 1))) ^ (n - 2) * 2 = 0 := by
    rw [← pow_succ, ← he]
    exact_mod_cast ZMod.natCast_self (2 ^ (n - 1))
  have hsq : ((2 : ZMod (2 ^ (n - 1))) ^ (n - 2)) ^ 2 = 0 := by
    calc
      _ = ((2 : ZMod (2 ^ (n - 1))) ^ (n - 2) * 2) * 2 ^ (n - 3) := by
        conv_lhs => rw [pow_two]; rhs; rw [he', pow_succ]
        ring
      _ = 0 := by rw [hz, zero_mul]
  rw [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  linear_combination hsq - hz

/-- The automorphism of the cyclic factor in the standard semidihedral group. -/
public def standardTwist (n : ℕ) (hn : 4 ≤ n) : MulAut (Multiplicative (ZMod (2 ^ (n - 1)))) where
  toFun x := .ofAdd (↑(2 ^ (n - 2) - 1 : ℕ) * x.toAdd)
  invFun x := .ofAdd (↑(2 ^ (n - 2) - 1 : ℕ) * x.toAdd)
  left_inv x := by
    change Multiplicative.ofAdd (_ * (_ * x.toAdd)) = x
    rw [← mul_assoc, ← pow_two, exponent_square hn, one_mul]
    rfl
  right_inv x := by
    change Multiplicative.ofAdd (_ * (_ * x.toAdd)) = x
    rw [← mul_assoc, ← pow_two, exponent_square hn, one_mul]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (_ * (x.toAdd + y.toAdd)) = .ofAdd (_ * x.toAdd + _ * y.toAdd)
    rw [mul_add]

/-- The twist is involutory, so it defines an action of the cyclic group of order two. -/
public theorem standardTwist_sq (n : ℕ) (hn : 4 ≤ n) : standardTwist n hn ^ 2 = 1 := by
  ext x
  change Multiplicative.ofAdd (_ * (_ * x.toAdd)) = x
  rw [← mul_assoc, ← pow_two, exponent_square hn, one_mul]
  rfl

/-- The twist raises each element of the cyclic factor to the semidihedral exponent. -/
public theorem standardTwist_apply (n : ℕ) (hn : 4 ≤ n)
    (x : Multiplicative (ZMod (2 ^ (n - 1)))) :
    standardTwist n hn x = x ^ (2 ^ (n - 2) - 1) := by
  change Multiplicative.ofAdd (_ * x.toAdd) = .ofAdd ((2 ^ (n - 2) - 1) • x.toAdd)
  rw [nsmul_eq_mul]

/-- The action of `C₂` on `C_(2^(n-1))` by the semidihedral twist. -/
public def standardAction (n : ℕ) (hn : 4 ≤ n) :
    Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod (2 ^ (n - 1)))) :=
  cyclicHom (standardTwist n hn) (standardTwist_sq n hn)

/-- The nonidentity element of `C₂` acts by the specified twist. -/
public theorem standardAction_generator (n : ℕ) (hn : 4 ≤ n) :
    standardAction n hn (.ofAdd 1) = standardTwist n hn :=
  cyclicHom_one _ _

/-- The standard semidihedral group of order `2^n`, defined independently of
any presentation witnesses. -/
public abbrev StandardModel (n : ℕ) (hn : 4 ≤ n) :=
  Multiplicative (ZMod (2 ^ (n - 1))) ⋊[standardAction n hn] Multiplicative (ZMod 2)

public instance instFiniteStandardModel (n : ℕ) (hn : 4 ≤ n) : Finite (StandardModel n hn) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

/-- The standard semidihedral group has order `2^n`. -/
public theorem standardModel_card (n : ℕ) (hn : 4 ≤ n) : Nat.card (StandardModel n hn) = 2 ^ n := by
  rw [SemidirectProduct.card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [← pow_succ, show n - 1 + 1 = n by omega]

/-- The canonical generator of the normal cyclic factor. -/
public def standardRotation (n : ℕ) (hn : 4 ≤ n) : StandardModel n hn :=
  SemidirectProduct.inl (.ofAdd 1)

/-- The canonical generator of the involutory factor. -/
public def standardReflection (n : ℕ) (hn : 4 ≤ n) : StandardModel n hn :=
  SemidirectProduct.inr (.ofAdd 1)

/-- The canonical rotation has the full order of the cyclic factor. -/
public theorem standardRotation_order (n : ℕ) (hn : 4 ≤ n) :
    orderOf (standardRotation n hn) = 2 ^ (n - 1) := by
  rw [standardRotation, orderOf_injective _ SemidirectProduct.inl_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- The canonical reflection is an involution. -/
public theorem standardReflection_order (n : ℕ) (hn : 4 ≤ n) :
    orderOf (standardReflection n hn) = 2 := by
  rw [standardReflection, orderOf_injective _ SemidirectProduct.inr_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- The canonical generators satisfy the semidihedral conjugation relation. -/
public theorem standard_conjugation (n : ℕ) (hn : 4 ≤ n) :
    standardReflection n hn * standardRotation n hn * (standardReflection n hn)⁻¹ =
      standardRotation n hn ^ (2 ^ (n - 2) - 1) := by
  rw [standardReflection, standardRotation, ← map_inv, ← SemidirectProduct.inl_aut,
    standardAction_generator, standardTwist_apply, map_pow]

private theorem cyclic_generator_pow {m : ℕ} [NeZero m] (x : Multiplicative (ZMod m)) :
    (Multiplicative.ofAdd (1 : ZMod m)) ^ x.toAdd.val = x := by
  change Multiplicative.ofAdd (x.toAdd.val • (1 : ZMod m)) = x
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rfl

/-- The canonical rotation and reflection generate the standard group. -/
public theorem standard_generators (n : ℕ) (hn : 4 ≤ n) :
    Subgroup.closure ({standardRotation n hn, standardReflection n hn} :
      Set (StandardModel n hn)) = ⊤ := by
  let K := Subgroup.closure ({standardRotation n hn, standardReflection n hn} :
    Set (StandardModel n hn))
  have ha : standardRotation n hn ∈ K := Subgroup.subset_closure (by simp)
  have hb : standardReflection n hn ∈ K := Subgroup.subset_closure (by simp)
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply K.mul_mem
  · have h := K.pow_mem ha x.left.toAdd.val
    simpa only [standardRotation, ← map_pow, cyclic_generator_pow] using h
  · have h := K.pow_mem hb x.right.toAdd.val
    simpa only [standardReflection, ← map_pow, cyclic_generator_pow] using h

private def presentationHom {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (a b : G) (ha : a ^ (2 ^ (n - 1)) = 1) (hb : b ^ 2 = 1)
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) : StandardModel n hn →* G :=
  SemidirectProduct.lift (cyclicHom a ha) (cyclicHom b hb) (by
    intro g
    have hg : g = .ofAdd 0 ∨ g = .ofAdd 1 := by
      have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
        intro z
        fin_cases z
        · exact Or.inl rfl
        · exact Or.inr rfl
      exact h g.toAdd
    rcases hg with rfl | rfl
    · apply MonoidHom.ext
      intro x
      change cyclicHom a ha (standardAction n hn 1 x) = _
      simp
    · apply MonoidHom.ext
      intro x
      change cyclicHom a ha (standardAction n hn (.ofAdd 1) x) =
        cyclicHom b hb (.ofAdd 1) * cyclicHom a ha x * (cyclicHom b hb (.ofAdd 1))⁻¹
      rw [standardAction, cyclicHom_one, cyclicHom_one, standardTwist_apply, map_pow]
      change (a ^ x.toAdd.val) ^ (2 ^ (n - 2) - 1) = b * a ^ x.toAdd.val * b⁻¹
      rw [← conj_pow, hab, ← pow_mul, ← pow_mul, Nat.mul_comm])

/-- The presentation homomorphism retains the specified rotation and reflection.
This public specification does not expose the model's coordinate definitions. -/
public theorem standardModel_hom_of_relations
    {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (a b : G) (ha : a ^ (2 ^ (n - 1)) = 1) (hb : b ^ 2 = 1)
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) :
    ∃ f : StandardModel n hn →* G,
      f (standardRotation n hn) = a ∧ f (standardReflection n hn) = b := by
  refine ⟨presentationHom hn a b ha hb hab, ?_, ?_⟩
  · exact (SemidirectProduct.lift_inl _ _ _ _).trans (cyclicHom_one a ha)
  · exact (SemidirectProduct.lift_inr _ _ _ _).trans (cyclicHom_one b hb)

/-- The semidihedral relations, generation, and expected cardinality determine the group. -/
public theorem standardModel_equiv_of_relations
    {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (a b : G) (ha : a ^ (2 ^ (n - 1)) = 1) (hb : b ^ 2 = 1)
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hcard : Nat.card G = 2 ^ n) : Nonempty (G ≃* StandardModel n hn) := by
  let f := presentationHom hn a b ha hb hab
  have hs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      refine ⟨SemidirectProduct.inl (.ofAdd 1), ?_⟩
      exact (SemidirectProduct.lift_inl _ _ _ _).trans (cyclicHom_one a ha)
    · have hx : x = b := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨SemidirectProduct.inr (.ofAdd 1), ?_⟩
      exact (SemidirectProduct.lift_inr _ _ _ _).trans (cyclicHom_one b hb)
  exact ⟨(MulEquiv.ofBijective f (hs.bijective_of_nat_card_le
    (by rw [standardModel_card, hcard]))).symm⟩

/-- The exact-order presentation determines the standard semidihedral group. -/
public theorem standardModel_equiv_of_presentation
    {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (a b : G) (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hcard : Nat.card G = 2 ^ n) : Nonempty (G ≃* StandardModel n hn) :=
  standardModel_equiv_of_relations hn a b (ha ▸ pow_orderOf_eq_one a)
    (hb ▸ pow_orderOf_eq_one b) hab hgen hcard

end Semidihedral
