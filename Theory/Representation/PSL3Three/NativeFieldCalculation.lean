module

public import Theory.Representation.PSL3Three.AbsoluteDegrees
public import Theory.Representation.EndFieldFrobenius
public import Theory.SpecificGroups.PSL3Three.BinaryPowerClasses

/-!
# A native Frobenius obstruction for degree-sixteen PSL₃(3) modules

The seven constructed simples of degrees 1, 12, 26 and four times 16 exhaust
all simples by the odd-order conjugacy-class bound. Frobenius therefore permutes
them, fixing the three unique degrees. If a degree-sixteen character were fixed
as well, those four characters and the sum of the remaining three would be five
independent functions invariant under squaring. Native matrix calculations give
only four odd-order conjugacy classes up to iterated squaring, a contradiction.

This proves the field obstruction and applies it to binary scalar descent from
three construction/counting inputs, without a character table, prescribed trace
value or lifting theorem. The independent native model constructions and odd-class
bound remain premises; the unconditional field theorem requires their discharge.

Source context: Guralnick--Malle, *Classification of 2F-modules I*, Proposition
4.2, and Aschbacher--Smith, Chapter K.2. The Frobenius argument here proves the
separate field restriction required by that application's scalar descent; it
is not an invocation of the offender hypotheses in Proposition 4.2.
-/


open scoped BigOperators

private theorem matrix_trace_sq {F n : Type*} [Field F] [CharP F 2]
    [Fintype n] [DecidableEq n] (A : Matrix n n F) :
    Matrix.trace (A ^ 2) = Matrix.trace A ^ 2 := by
  classical
  have hoff : (∑ ij : n × n, if ij.1 = ij.2 then 0 else A ij.1 ij.2 * A ij.2 ij.1) = 0 := by
    apply Finset.sum_involution (fun ij _ => (ij.2, ij.1))
    · intro ij _
      by_cases h : ij.1 = ij.2
      · simp [h]
      · simp only [h, Ne.symm h, if_false]
        rw [mul_comm (A ij.2 ij.1), CharTwo.add_self_eq_zero]
    · intro ij _ h hs
      apply h
      have he : ij.1 = ij.2 := (congrArg Prod.fst hs).symm
      simp [he]
    · intros; exact Finset.mem_univ _
    · intros; rfl
  have hsum : (∑ ij : n × n, A ij.1 ij.2 * A ij.2 ij.1) = ∑ i, A i i ^ 2 := by
    calc
      _ = (∑ ij : n × n, if ij.1 = ij.2 then A ij.1 ij.2 * A ij.2 ij.1 else 0) +
          (∑ ij : n × n, if ij.1 = ij.2 then 0 else A ij.1 ij.2 * A ij.2 ij.1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ij _
        split_ifs <;> simp
      _ = _ := by
        rw [hoff, add_zero, Fintype.sum_prod_type]
        simp [pow_two]
  rw [pow_two]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  change (∑ i, ∑ j, A i j * A j i) = (∑ i, A i i) ^ 2
  simp only [Fintype.sum_prod_type] at hsum
  rw [hsum]
  exact (map_sum (frobenius F 2) (fun i => A i i) Finset.univ).symm

namespace Representation

private theorem character_sq {F G V : Type*} [Field F] [CharP F 2] [Monoid G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (g : G) : ρ.character (g ^ 2) = ρ.character g ^ 2 := by
  classical
  rw [character, character, map_pow]
  rw [LinearMap.trace_eq_matrix_trace F (Module.finBasis F V),
    LinearMap.trace_eq_matrix_trace F (Module.finBasis F V), ← LinearMap.toMatrix_pow]
  exact matrix_trace_sq _

/-- A group-theoretic coverage contract; no representation or trace premise. -/
private def BinaryPowerClassCover (G : Type*) [Group G] : Prop :=
  ∃ r : Fin 4 → G, ∀ g : G, ¬ 2 ∣ orderOf g →
    ∃ i n, IsConj g (r i ^ (2 ^ n))

/-- Squaring-invariant class functions with common p-regular reduction are
 determined by a binary power class cover. -/
private theorem invariant_family_card_le_four
    {F G ι : Type*} [Field F] [Group G] [Fintype ι]
    (hcover : BinaryPowerClassCover G) (χ : ι → G → F)
    (hli : LinearIndependent F χ)
    (hconj : ∀ i g h, IsConj g h → χ i g = χ i h)
    (hsq : ∀ i g, χ i (g ^ 2) = χ i g)
    (hreg : ∀ g, ∃ h, ¬ 2 ∣ orderOf h ∧ ∀ i, χ i g = χ i h) :
    Fintype.card ι ≤ 4 := by
  classical
  obtain ⟨r, hr⟩ := hcover
  have hpow (i : ι) (g : G) (n : ℕ) : χ i (g ^ (2 ^ n)) = χ i g := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, hsq, ih]
  let ψ : ι → Fin 4 → F := fun i k => χ i (r k)
  have hind : LinearIndependent F ψ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply (Fintype.linearIndependent_iff.mp hli) c
    funext g
    obtain ⟨h, hh, he⟩ := hreg g
    obtain ⟨k, n, hk⟩ := hr h hh
    have hval (i : ι) : χ i g = ψ i k :=
      (he i).trans ((hconj i h _ hk).trans (hpow i _ n))
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, hval] using congrFun hc k
  simpa using hind.fintype_card_le_finrank

end Representation

namespace Representation

private def sevenDegrees : Fin 7 → ℕ := ![1, 12, 26, 16, 16, 16, 16]

universe u v

private theorem fourth_character_not_fixed
    {F : Type v} {G : Type u} [Field F] [IsAlgClosed F] [CharP F 2] [Group G] [Finite G]
    (V : Fin 7 → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F G (V i))
    [∀ i, IsIrreducible (ρ i)]
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hd : ∀ i, Module.finrank F (V i) = sevenDegrees i)
    (hclasses : Nat.card (ConjClasses.mk '' {g : G | ¬ 2 ∣ orderOf g}) ≤ 7)
    (hcover : BinaryPowerClassCover G)
    (hfixed : ∀ g, (ρ 3).character g ^ 2 = (ρ 3).character g) : False := by
  classical
  let χ : Fin 7 → G → F := fun i => (ρ i).character
  have hli : LinearIndependent F χ :=
    linearIndependent_characters_of_pairwise_inequivalent V ρ hne
  have htwist (i : Fin 7) : ∃ j, Nonempty ((frobeniusConjugate 2 1 (ρ i)).Equiv (ρ j)) := by
    let : IsIrreducible (frobeniusConjugate 2 1 (ρ i)) :=
      frobeniusConjugate_isIrreducible 2 1 _
    exact exists_equiv_of_pRegular_class_bound V ρ 2 hne
      (by simpa using hclasses) _
  choose f hf using htwist
  have hχ (i : Fin 7) (g : G) : χ (f i) g = χ i g ^ 2 := by
    obtain ⟨e⟩ := hf i
    have hh := congrFun (char_iso e) g
    simpa only [χ, character_frobeniusConjugate, pow_one] using hh.symm
  have hinj : Function.Injective f := by
    intro i j hij
    apply hli.injective
    funext g
    apply frobenius_inj F 2
    change χ i g ^ 2 = χ j g ^ 2
    rw [← hχ, ← hχ, hij]
  let e : Equiv.Perm (Fin 7) :=
    Equiv.ofBijective f ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have hechar (i : Fin 7) (g : G) : χ (e i) g = χ i g ^ 2 := hχ i g
  have hed (i : Fin 7) : sevenDegrees (e i) = sevenDegrees i := by
    obtain ⟨t⟩ := hf i
    exact (hd _).symm.trans (t.toLinearEquiv.finrank_eq.symm.trans (hd i))
  have he0 : e 0 = 0 :=
    (by decide : ∀ i : Fin 7, sevenDegrees i = 1 → i = 0) _ (hed 0)
  have he1 : e 1 = 1 :=
    (by decide : ∀ i : Fin 7, sevenDegrees i = 12 → i = 1) _ (hed 1)
  have he2 : e 2 = 2 :=
    (by decide : ∀ i : Fin 7, sevenDegrees i = 26 → i = 2) _ (hed 2)
  have he3 : e 3 = 3 := by
    apply hli.injective
    funext g
    exact (hechar 3 g).trans (hfixed g)
  have hfix0 (g : G) : χ 0 g ^ 2 = χ 0 g := (hechar 0 g).symm.trans (by rw [he0])
  have hfix1 (g : G) : χ 1 g ^ 2 = χ 1 g := (hechar 1 g).symm.trans (by rw [he1])
  have hfix2 (g : G) : χ 2 g ^ 2 = χ 2 g := (hechar 2 g).symm.trans (by rw [he2])
  have hfix3 (g : G) : χ 3 g ^ 2 = χ 3 g := hfixed g
  have hfixsum (g : G) : (χ 4 g + χ 5 g + χ 6 g) ^ 2 = χ 4 g + χ 5 g + χ 6 g := by
    have hs : (∑ i, χ i g ^ 2) = ∑ i, χ i g :=
      Fintype.sum_equiv e _ _ (fun i => (hechar i g).symm)
    simp [Fin.sum_univ_succ] at hs
    rw [hfix0, hfix1, hfix2, hfix3] at hs
    have ht := add_left_cancel (add_left_cancel (add_left_cancel (add_left_cancel hs)))
    simpa only [add_pow_char, add_assoc] using ht
  let ψ : Fin 5 → G → F := ![χ 0, χ 1, χ 2, χ 3, χ 4 + χ 5 + χ 6]
  have hψ : LinearIndependent F ψ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hrel : ∑ i : Fin 7, (![c 0, c 1, c 2, c 3, c 4, c 4, c 4] i) • χ i = 0 := by
      simpa [ψ, Fin.sum_univ_succ, smul_add, add_assoc] using hc
    have hzero := (Fintype.linearIndependent_iff.mp hli) _ hrel
    fin_cases k
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3
    · exact hzero 4
  have hconj (i : Fin 7) (g h : G) (hc : IsConj g h) : χ i g = χ i h := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hc
    dsimp [χ]
    rw [← ha, (ρ i).char_conj]
  have hbound := invariant_family_card_le_four hcover ψ hψ
    (fun i g h hc => by fin_cases i <;> simp [ψ, hconj _ g h hc])
    (fun i g => by
      have hs (j : Fin 7) : χ j (g ^ 2) = χ j g ^ 2 := character_sq (ρ j) g
      fin_cases i <;> simp [ψ, hs, hfix0, hfix1, hfix2, hfix3,
        ← add_pow_char, hfixsum])
    (fun g => by
      obtain ⟨h, hh, he⟩ := exists_pRegular_same_character (F := F) 2 g
      refine ⟨h, hh, ?_⟩
      intro i
      have ht (j : Fin 7) : χ j g = χ j h := he _ (ρ j)
      fin_cases i <;> simp [ψ, ht])
  norm_num at hbound

end Representation

namespace Representation.PSL3Three.NativeFieldCalculation
open AbsoluteDegrees
open scoped _root_.TensorProduct
universe v

set_option backward.isDefEq.respectTransparency false in
/-- For the native group, the construction inputs and power-class coverage
force a nonbinary trace on every simple of degree sixteen. -/
public theorem exists_character_sq_ne
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v})
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Matrix.PSL3Three.PSL | ¬ 2 ∣ orderOf g}) ≤ 7)
    {F W : Type v} [Field F] [IsAlgClosed F] [CharP F 2]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hdim : Module.finrank F W = 16) :
    ∃ g, σ.character g ^ 2 ≠ σ.character g := by
  classical
  have hcover : BinaryPowerClassCover Matrix.PSL3Three.PSL :=
    Matrix.PSL3Three.BinaryPowerClasses.cover_of_class_bound hclasses
  obtain ⟨ρ₁₂, ρ₂₆, h₁₂, h₂₆⟩ := hprincipal F
  obtain ⟨ρ₁₆, h₁₆, hdistinct⟩ := hsixteen F
  let := h₁₂
  let := h₂₆
  let := h₁₆
  let V : Fin 7 → Type v := fun i => Fin (sevenDegrees i) → F
  let ρ : ∀ i, Representation F Matrix.PSL3Three.PSL (V i) :=
    Fin.cases (Representation.trivial F _ (Fin 1 → F)) <|
      Fin.cases ρ₁₂ <| Fin.cases ρ₂₆ <| Fin.cases (ρ₁₆ 0) <|
        Fin.cases (ρ₁₆ 1) <| Fin.cases (ρ₁₆ 2) <| Fin.cases (ρ₁₆ 3) <|
          fun i => Fin.elim0 i
  let irr : ∀ i, IsIrreducible (ρ i) := fun i => by
    fin_cases i
    · change IsIrreducible (Representation.trivial F _ (Fin 1 → F))
      have : IsSimpleOrder (Submodule F (Fin 1 → F)) :=
        is_simple_module_of_finrank_eq_one (K := F) (by simp)
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    · change IsIrreducible ρ₁₂; exact h₁₂
    · change IsIrreducible ρ₂₆; exact h₂₆
    · change IsIrreducible (ρ₁₆ 0); exact h₁₆ 0
    · change IsIrreducible (ρ₁₆ 1); exact h₁₆ 1
    · change IsIrreducible (ρ₁₆ 2); exact h₁₆ 2
    · change IsIrreducible (ρ₁₆ 3); exact h₁₆ 3
  have hd (i : Fin 7) : Module.finrank F (V i) = sevenDegrees i := by
    fin_cases i <;> simp [V, sevenDegrees]
  have hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)) := by
    intro i j hij
    constructor
    intro t
    have ht := t.toLinearEquiv.finrank_eq
    rw [hd, hd] at ht
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hij rfl
      | solve | norm_num [sevenDegrees] at ht
      | exact (hdistinct (by decide)).false t
  obtain ⟨i, ⟨t⟩⟩ := exists_equiv_of_pRegular_class_bound V ρ 2 hne
    (by simpa using hclasses) σ
  have hi : sevenDegrees i = 16 :=
    (hd i).symm.trans (t.toLinearEquiv.finrank_eq.symm.trans hdim)
  let e : Equiv.Perm (Fin 7) := Equiv.swap 3 i
  have heswap : ∀ j, sevenDegrees (e j) = sevenDegrees j :=
    (by decide : ∀ k : Fin 7, sevenDegrees k = 16 →
      ∀ j, sevenDegrees (Equiv.swap 3 k j) = sevenDegrees j) i hi
  by_contra! hf
  apply fourth_character_not_fixed (fun j => V (e j)) (fun j => ρ (e j))
    (fun j k hjk => hne (fun h => hjk (e.injective h)))
    (fun j => (hd _).trans (heswap j)) hclasses hcover
  intro g
  have ht : (ρ (e 3)).character g = σ.character g := by
    have hei : e 3 = i := Equiv.swap_apply_left 3 i
    exact (congrArg (fun j => (ρ j).character g) hei).trans
      (congrFun (char_iso t) g).symm
  rw [ht]
  exact hf g

/-- The precise finite-field obstruction from native constructions and the
odd-class bound. These inputs remain explicit until their independent producers
are complete. -/
public theorem degreeSixteenFieldObstruction_of_native_inputs
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v})
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Matrix.PSL3Three.PSL | ¬ 2 ∣ orderOf g}) ≤ 7) :
    DegreeSixteenFieldObstruction.{v} := by
  intro K _ _ _ W _ _ _ σ _hf ha hd
  classical
  let : Fintype K := Fintype.ofFinite K
  have hcard : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card (α := K)
  by_contra hn
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; omega
  let F := AlgebraicClosure K
  let := ha.irreducible_of_closure
  obtain ⟨g, hg⟩ := exists_character_sq_ne hprincipal hsixteen hclasses
    (extendScalars F σ) (by simpa only [Module.finrank_baseChange] using hd)
  have he : (extendScalars F σ).character g =
      algebraMap K F (σ.character g) := LinearMap.trace_baseChange (σ g) F
  apply hg
  rw [he, ← map_pow]
  congr 1
  simpa only [hc] using FiniteField.pow_card (σ.character g)

/-- The actual binary scalar-descent consumer, with the field obstruction
proved from construction and group inputs rather than assumed. -/
public theorem binary_degree_twelve_of_native_inputs
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v})
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Matrix.PSL3Three.PSL | ¬ 2 ∣ orderOf g}) ≤ 7)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 18) :
    Module.finrank (ZMod 2) W = 12 :=
  binary_degree_twelve_of_absolute_calculations
    (absoluteDegreeWindow_of_constructions hprincipal hsixteen hclasses)
    (degreeSixteenFieldObstruction_of_native_inputs hprincipal hsixteen hclasses)
    σ hf hd

end Representation.PSL3Three.NativeFieldCalculation
