module

public import ABG.Basic
public import BenderSuzuki.MatrixGroups.RankThreeScalarCongruence
public import Theory.GroupTheory.AutomizerEmbedding
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.RankThreeAbelianAutomizer
public import Theory.Representation.RankThreeNonabelianAutomizer

/-!
# Odd-subgroup automizers in the concrete rank-three groups

We use SL₃ over `ZMod p` and the determinant-one isometries of the standard
Hermitian form over `GaloisField p 2`. The natural actions are faithful,
and their automizers embed in the automizers of their images in GL₃.
An order-three scalar forces the linear or unitary congruence respectively.

For an abelian cross-characteristic subgroup, the GL₃ weight-space action
embeds the automizer in S₃. For a nonabelian odd prime-subgroup, the faithful
degree-three action is absolutely irreducible, the prime is three, and its
automizer is solvable. Its order-three scalar supplies the congruence above.
Transport along the actual SL₃ and SU₃ embeddings proves both alternatives
without any involution-centralizer or SQTK classification hypotheses.

Source: Aschbacher–Smith, Lemma A.3.21(c), printed pp. 55–56
(PDF pp. 66–67 of `refs/quasithin.pdf`).
-/

public section

namespace CFSG.Quasithin.ChapterA.Section03

open BenderSuzuki.MatrixGroups

/-- The linear model uses the field of exactly `p` elements. -/
theorem rankThree_primeField_card (p : ℕ) [Fact p.Prime] :
    Nat.card (ZMod p) = p := by simp

/-- The unitary model uses the quadratic field, of exactly `p²` elements. -/
theorem rankThree_quadraticField_card (p : ℕ) [Fact p.Prime] :
    Nat.card (GaloisField p (2 * 1)) = p ^ 2 := by
  simpa using GaloisField.card p (2 * 1) (by decide)

/-- The standard unitary conjugation is the `p`-power map. -/
theorem rankThree_unitaryForm_conj (p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm 3 p 1 (by decide)).conj x = x ^ p := by
  simp [ABG.unitaryForm, frobenius_def]

/-- The actual linear group's natural degree-three representation is faithful. -/
theorem sl3_natural_faithful (p : ℕ) [Fact p.Prime] :
    Function.Injective (Representation.specialLinearNatural (k := ZMod p) 3) :=
  Representation.specialLinearNatural_injective 3

/-- The natural degree-three action of the actual special unitary group. -/
@[expose] noncomputable def su3_natural (p : ℕ) [Fact p.Prime] :
    Representation (GaloisField p (2 * 1))
      (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup
      (Fin 3 → GaloisField p (2 * 1)) :=
  (Representation.generalLinearNatural 3).comp
    (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup.subtype

/-- The special unitary action is faithful because its matrices act faithfully. -/
theorem su3_natural_faithful (p : ℕ) [Fact p.Prime] :
    Function.Injective (su3_natural p) :=
  (Representation.generalLinearNatural_injective 3).comp Subtype.val_injective

/-- Linear automizers embed in those of the corresponding GL₃ subgroup. -/
theorem sl3_automizer_embedding (p : ℕ) [Fact p.Prime]
    (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) :
    ∃ j : Q.normalizerMonoidHom.range →*
        (Q.map Matrix.SpecialLinearGroup.toGL).normalizerMonoidHom.range,
      Function.Injective j :=
  Q.exists_injective_automizer_map _ Matrix.SpecialLinearGroup.toGL_injective

/-- Unitary automizers embed in those of the corresponding GL₃ subgroup. -/
theorem su3_automizer_embedding (p : ℕ) [Fact p.Prime]
    (Q : Subgroup (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup) :
    ∃ j : Q.normalizerMonoidHom.range →*
        (Q.map (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup.subtype
          ).normalizerMonoidHom.range,
      Function.Injective j :=
  Q.exists_injective_automizer_map _ Subtype.val_injective

/-- The scalar restriction in the linear case of A.3.21(c). -/
theorem sl3_scalar_order_three_congruence (p : ℕ) [Fact p.Prime]
    (a : (ZMod p)ˣ) (ha : orderOf a = 3) : p % 3 = 1 :=
  card_mod_three_of_scalar_order_three (rankThree_primeField_card p) a ha

/-- The scalar restriction in the unitary case of A.3.21(c). -/
theorem su3_scalar_order_three_congruence (p : ℕ) [Fact p.Prime]
    (a : (GaloisField p (2 * 1))ˣ) (ha : orderOf a = 3)
    (g : (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup)
    (hg : (g.val : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * 1))) =
      Matrix.scalar (Fin 3) (a : GaloisField p (2 * 1))) : p % 3 = 2 :=
  (ABG.unitaryForm 3 p 1 (by decide)).mod_three_of_scalar_order_three
    (rankThree_unitaryForm_conj p) a ha g hg

private theorem rankThree_not_isMulCommutative_map {G H : Type*} [Group G] [Group H]
    (Q : Subgroup G) (f : G →* H) (hf : Function.Injective f)
    (hn : ¬ IsMulCommutative Q) : ¬ IsMulCommutative (Q.map f) := by
  intro hc
  let : IsMulCommutative (Q.map f) := hc
  let e := Q.equivMapOfInjective f hf
  apply hn
  exact .of_comm fun a b => e.injective (by simp only [map_mul]; exact mul_comm' _ _)

/-- A.3.21(c) for the actual special linear group over the prime field. -/
theorem sl3_odd_subgroup_automizer (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (_hp : Odd p) (hq : Odd q) (hqp : q ≠ p)
    (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))
    (hQ : IsPGroup q Q) :
    (IsMulCommutative Q ∧
      ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm (Fin 3), Function.Injective j) ∨
    (q = 3 ∧ p % 3 = 1 ∧ Group.IsSolvable Q.normalizerMonoidHom.range) := by
  let f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) →* GL (Fin 3) (ZMod p) :=
    Matrix.SpecialLinearGroup.toGL
  have hf : Function.Injective f := Matrix.SpecialLinearGroup.toGL_injective
  by_cases hc : IsMulCommutative Q
  · let : IsMulCommutative Q := hc
    exact Or.inl ⟨hc, Q.automizer_embeds_perm_of_map f hf
      (Representation.rankThree_abelian_automizer_embeds_perm p q hqp (Q.map f) (hQ.map f))⟩
  · have hn := rankThree_not_isMulCommutative_map Q f hf hc
    have hthree := Representation.RankThreeNonabelianAutomizer.prime_eq_three
      hq hqp (Q.map f) (hQ.map f) hn
    let : Group.IsSolvable (Q.map f).normalizerMonoidHom.range :=
      Representation.RankThreeNonabelianAutomizer.automizer_isSolvable
        hq hqp (Q.map f) (hQ.map f) hn
    obtain ⟨a, ha, _⟩ := Representation.RankThreeNonabelianAutomizer.exists_scalar_order_three
      hq hqp (Q.map f) (hQ.map f) hn
    exact Or.inr ⟨hthree, sl3_scalar_order_three_congruence p a ha,
      Q.automizer_isSolvable_of_map f hf⟩

/-- A.3.21(c) for the actual special unitary group over the quadratic field. -/
theorem su3_odd_subgroup_automizer (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (_hp : Odd p) (hq : Odd q) (hqp : q ≠ p)
    (Q : Subgroup (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup)
    (hQ : IsPGroup q Q) :
    (IsMulCommutative Q ∧
      ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm (Fin 3), Function.Injective j) ∨
    (q = 3 ∧ p % 3 = 2 ∧ Group.IsSolvable Q.normalizerMonoidHom.range) := by
  let f := (ABG.unitaryForm 3 p 1 (by decide)).specialSubgroup.subtype
  have hf : Function.Injective f := Subtype.val_injective
  by_cases hc : IsMulCommutative Q
  · let : IsMulCommutative Q := hc
    exact Or.inl ⟨hc, Q.automizer_embeds_perm_of_map f hf
      (Representation.rankThree_abelian_automizer_embeds_perm p q hqp (Q.map f) (hQ.map f))⟩
  · have hn := rankThree_not_isMulCommutative_map Q f hf hc
    have hthree := Representation.RankThreeNonabelianAutomizer.prime_eq_three
      hq hqp (Q.map f) (hQ.map f) hn
    let : Group.IsSolvable (Q.map f).normalizerMonoidHom.range :=
      Representation.RankThreeNonabelianAutomizer.automizer_isSolvable
        hq hqp (Q.map f) (hQ.map f) hn
    obtain ⟨a, ha, g, hg⟩ := Representation.RankThreeNonabelianAutomizer.exists_scalar_order_three
      hq hqp (Q.map f) (hQ.map f) hn
    obtain ⟨u, _hu, heq⟩ := g.property
    have hscalar : (u.val : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * 1))) =
        Matrix.scalar (Fin 3) (a : GaloisField p (2 * 1)) := by
      change ((f u : GL (Fin 3) (GaloisField p (2 * 1))) :
        Matrix (Fin 3) (Fin 3) (GaloisField p (2 * 1))) = _
      rw [heq]
      exact hg
    exact Or.inr ⟨hthree, su3_scalar_order_three_congruence p a ha u hscalar,
      Q.automizer_isSolvable_of_map f hf⟩

end CFSG.Quasithin.ChapterA.Section03
