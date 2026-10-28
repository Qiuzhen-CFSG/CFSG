module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.SL3.SplitMonomial.ProjectiveLift
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.RepresentationTheory.Maschke

/-!
# Inputs and exclusions for elementary PSL₃ positioning

Transport the elementary subgroup, genuine ambient Sylow and product order
through an actual matrix-group equivalence. The full SL₃ inverse image retains
the scalar kernel; its order has only primes two and three, so Maschke applies
in characteristic greater than three.

The odd-field PSL₃ order has a factor sixteen, retained by its ambient Sylow.
This excludes the odd Singer normalizer and the primitive extraspecial bound
216. The latter bound must come from the determinant-one automizer in GLS3.
A permuted line basis gives actual monomial placement by change of basis and
central descent. Involution placement pulls back with the entire mapped
intrinsic Sylow center.

`ModelInput` contains only facts proved here from `PairInput`. `ReduciblePreimage`
means preservation of an actual nonzero proper subspace. Neither definition
assumes a placement conclusion. The remaining geometric cases are assembled
conditionally in the parent module.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Theorem 6.5.3(a–d) and its proof,
`refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Matrix.SL3.SplitMonomial
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial

/-- Reducibility of the full inverse image on the actual natural module. -/
def ReduciblePreimage {F : Type*} [Field F] (H : Subgroup PSL(3,F)) : Prop :=
  ∃ W : Submodule F (Fin 3 → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
    ∀ g ∈ projectivePreimage H, ∀ v ∈ W, g • v ∈ W

/-- Facts about the transported pair, all derived from the original input. -/
structure ModelInput {G : Type*} [Group G]
    (T : Sylow 2 G) (U : Subgroup G) : Prop where
  rank : primeRank 3 G = 2
  elementary : IsElementaryAbelian 3 U
  card : Nat.card U = 9
  product_card : Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) = 9 * Nat.card T
  solvable : Group.IsSolvable (U ⊔ (T : Subgroup _) : Subgroup _)
  prime_divisors : ∀ r : ℕ, r.Prime →
    r ∣ Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) → r = 2 ∨ r = 3

variable {Q : Type*} [Group Q]

private theorem transported_solvable [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {G : Type*} [Group G] (e : Q ≃* G) :
    Group.IsSolvable ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom) := by
  let _ := EvenRankTwo.product_solvable h
  exact Group.isSolvable_of_surjective
    (f := (e.subgroupMap (R ⊔ (S : Subgroup Q))).toMonoidHom)
    (e.subgroupMap (R ⊔ (S : Subgroup Q))).surjective

/-- Transport the genuine Sylow and all local numerical inputs. -/
theorem modelInput_of_pair [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9)
    {G : Type*} [Group G] [Finite G] (e : Q ≃* G) :
    ModelInput (S.mapSurjective (f := e.toMonoidHom) e.surjective) (R.map e.toMonoidHom) := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let U := R.map e.toMonoidHom
  have hT : (T : Subgroup _) = (S : Subgroup Q).map e.toMonoidHom := rfl
  have hUT : U ⊔ (T : Subgroup _) = (R ⊔ (S : Subgroup Q)).map e.toMonoidHom := by
    rw [hT, Subgroup.map_sup]
  have hcardT : Nat.card T = Nat.card S := Subgroup.card_map_of_injective e.injective
  have hcard : Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) =
      Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q) := by
    rw [hUT, Subgroup.card_map_of_injective e.injective]
  refine ⟨(primeRank_equiv 3 e).symm.trans h.rank, ?_, ?_, ?_, ?_, ?_⟩
  · let _ := he
    let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsElementaryAbelian.map e.toMonoidHom
  · exact (Subgroup.card_map_of_injective e.injective).trans hc
  · change Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) = 9 * Nat.card T
    rw [hcard, EvenRankTwo.product_card h, hc, hcardT]
  · exact hUT.symm ▸ transported_solvable h e
  · intro r hr hd
    exact EvenRankTwo.product_prime_divisors h hr (hcard ▸ hd)


private theorem card_preimage {F : Type*} [Field F] [Finite F]
    (H : Subgroup PSL(3,F)) :
    Nat.card (projectivePreimage H) = Nat.card H * Nat.card (center SL(3,F)) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero H.index_ne_zero_of_finite)
  calc
    Nat.card (projectivePreimage H) * H.index = Nat.card SL(3,F) := by
      rw [← H.index_comap_of_surjective (Matrix.PSL3.projection_surjective F)]
      exact (projectivePreimage H).card_mul_index
    _ = Nat.card PSL(3,F) * Nat.card (center SL(3,F)) :=
      card_eq_card_quotient_mul_card_subgroup (center SL(3,F))
    _ = (Nat.card H * Nat.card (center SL(3,F))) * H.index := by
      rw [← H.card_mul_index]
      ac_rfl

/-- The central scalar kernel introduces no prime other than three. -/
theorem ModelInput.preimage_prime_divisors {F : Type*} [Field F] [Finite F]
    {T : Sylow 2 PSL(3,F)} {U : Subgroup PSL(3,F)} (h : ModelInput T U)
    {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card (projectivePreimage (U ⊔ (T : Subgroup _)))) : r = 2 ∨ r = 3 := by
  rw [card_preimage] at hd
  rcases hr.dvd_mul.mp hd with hd | hd
  · exact h.prime_divisors r hr hd
  · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
      (hd.trans (Matrix.SL3.card_center_dvd_three F))).resolve_left hr.ne_one)

/-- Maschke applies to the full inverse image, retaining its central kernel. -/
theorem ModelInput.preimage_semisimple {F : Type*} [Field F] [Finite F]
    {T : Sylow 2 PSL(3,F)} {U : Subgroup PSL(3,F)} (h : ModelInput T U)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p) (hF : Nat.card F = p) :
    Representation.IsSemisimpleRepresentation
      ((Representation.specialLinearNatural (k := F) 3).comp
        (projectivePreimage (U ⊔ (T : Subgroup _))).subtype) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F p := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hn : (Nat.card (projectivePreimage (U ⊔ (T : Subgroup _))) : F) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff F p]
    intro hd
    rcases h.preimage_prime_divisors hp hd with hp | hp <;> omega
  let _ : NeZero (Nat.card (projectivePreimage (U ⊔ (T : Subgroup _))) : F) := ⟨hn⟩
  infer_instance

private theorem sixteen_dvd_order_factors (q : ℕ) (hq : Odd q) :
    16 ∣ (q ^ 3 - 1) * (q ^ 2 - 1) := by
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp hq
  have hq8 : q % 8 < 8 := Nat.mod_lt q (by decide)
  have hmod : q % 8 % 2 = 1 := by omega
  have hcases : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  have hsquare : q ^ 2 % 8 = 1 := by
    rcases hcases with h | h | h | h <;> norm_num [Nat.pow_mod, h]
  have hcube : q ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hq2]
  have h8 : 8 ∣ q ^ 2 - 1 := by omega
  have h2 : 2 ∣ q ^ 3 - 1 := by omega
  exact Nat.mul_dvd_mul h2 h8

/-- The full ambient Sylow has a factor sixteen; the odd scalar quotient
cannot remove any factor two. -/
theorem sixteen_dvd_card_sylow {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (T : Sylow 2 PSL(3,F)) : 16 ∣ Nat.card T := by
  have h : 16 ∣ Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) := by
    rw [Matrix.PSL3.LinearThree.card_projective_mul_scalar]
    simpa only [mul_assoc] using (sixteen_dvd_order_factors (Nat.card F) hF).mul_left (Nat.card F ^ 3)
  have hg : Nat.Coprime 16 (Nat.gcd 3 (Nat.card F - 1)) :=
    Nat.Coprime.of_dvd_right (Nat.gcd_dvd_left _ _) (by decide : Nat.Coprime 16 3)
  exact T.pow_dvd_card_of_pow_dvd_card (n := 4) (hg.dvd_of_dvd_mul_right h)

/-- A subgroup containing the ambient Sylow also has a factor sixteen. -/
theorem sixteen_dvd_card_product {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F)) :
    16 ∣ Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) :=
  (sixteen_dvd_card_sylow hF T).trans (Subgroup.card_dvd_of_le le_sup_right)

/-- In particular the odd Singer-normalizer alternative cannot contain this pair. -/
theorem product_not_odd {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F)) :
    ¬ Odd (Nat.card (U ⊔ (T : Subgroup _) : Subgroup _)) := by
  have hd := (by decide : 2 ∣ 16).trans (sixteen_dvd_card_product hF T U)
  intro ho
  have := Nat.odd_iff.mp ho
  omega

/-- The primitive extraspecial normalizer has order dividing 216, which
cannot contain the ambient Sylow. A GL₂(3) bound would not suffice. -/
theorem product_card_not_dvd_216 {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F)) :
    ¬ Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) ∣ 216 := by
  intro hd
  exact (by decide : ¬ 16 ∣ 216) ((sixteen_dvd_card_product hF T U).trans hd)

private theorem mapped_center_mem {G : Type*} [Group G]
    (S : Subgroup Q) (e : Q ≃* G) {x : Q}
    (hx : x ∈ (center S).map S.subtype) :
    e x ∈ (center (S.map e.toMonoidHom)).map (S.map e.toMonoidHom).subtype := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨⟨e z, mem_map_of_mem _ z.property⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  obtain ⟨w, hw, hwy⟩ := y.property
  apply Subtype.ext
  change (y : G) * e z = e z * (y : G)
  rw [← hwy]
  change e w * e z = e z * e w
  rw [← map_mul, ← map_mul]
  exact congrArg e (congrArg Subtype.val (mem_center_iff.mp hz ⟨w, hw⟩))

/-- Pull back the involution and the containment for the whole intrinsic
Sylow center, rather than only its involution. -/
theorem involutionPosition_of_map {G : Type*} [Group G]
    (S R : Subgroup Q) (e : Q ≃* G)
    (h : InvolutionPosition (S.map e.toMonoidHom) (R.map e.toMonoidHom)) :
    InvolutionPosition S R := by
  obtain ⟨z, hz, hR, hC⟩ := h
  refine ⟨e.symm z, (e.symm.orderOf_eq z).trans hz, ?_, ?_⟩
  · intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] using
      mem_centralizer_singleton_iff.mp (hR (mem_map_of_mem _ hx))
  · intro x hx y hy
    have hx' : e x ∈ centralizer ({z} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul, e.apply_symm_apply] using
        congrArg e (mem_centralizer_singleton_iff.mp hx)
    apply e.injective
    simpa only [map_mul] using hC hx' (e y) (mapped_center_mem S e hy)

/-- A line basis for the full projective preimage produces the required
actual model equivalence, including its change of coordinates. -/
theorem monomialPosition_of_invariantBasis {S R : Subgroup Q} {p : ℕ}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p) (e : Q ≃* PSL(3,F))
    (hb : HasInvariantBasis (projectivePreimage ((R ⊔ S).map e.toMonoidHom))) :
    MonomialPosition p S R := by
  obtain ⟨a, ha⟩ := exists_projective_map_le_of_invariant_basis _ hb
  refine ⟨F, inferInstance, inferInstance, hF, e.trans a, ?_⟩
  rw [Subgroup.map_map] at ha
  exact ha


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
