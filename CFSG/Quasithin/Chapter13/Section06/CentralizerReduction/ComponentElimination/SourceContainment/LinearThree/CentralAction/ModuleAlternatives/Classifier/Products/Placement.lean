module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Groups
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# Locating the actual PSL₃(2) component in the product alternatives

The component dichotomy puts a normal PSL₃(2) in one of the two original
factors. Containment in an SL₃ factor is equality by component maximality.
An S₅ factor is excluded by order, and an SL₂ factor in characteristic two
is excluded by an explicit element of order four: its Sylow two-subgroups
are additive groups of fields and have exponent two.

The applications exhaust every factor constructor of B.5.6(3) and (5),
including the exceptional four-space and both hyperplane second rows. These
are subgroup equalities only; no quotient module is identified with its cover.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6,
printed p.105, as used in the proof of 13.6.20, printed p.931.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction

variable {D : Type*} [Group D] {A B C : Subgroup D}

private theorem product_commute (h : InternalProduct A B) (a : A) (b : B) :
    (a : D) * b = (b : D) * a := by
  calc
    (a : D) * b = h.equiv (a, 1) * h.equiv (1, b) := by simp [h.apply_eq]
    _ = h.equiv ((a, 1) * (1, b)) := (map_mul _ _ _).symm
    _ = h.equiv ((1, b) * (a, 1)) := by simp
    _ = (b : D) * a := by rw [map_mul]; simp [h.apply_eq]

/-- Reverse the original factors without changing their inclusions. -/
def swapProduct (h : InternalProduct A B) : InternalProduct B A where
  equiv := (MulEquiv.prodComm (M := B) (N := A)).trans h.equiv
  apply_eq b a := by exact (h.apply_eq a b).trans (product_commute h a b)

/-- Component dichotomy in the actual normal factors rules out a diagonal copy. -/
theorem component_le_factor [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (h : InternalProduct A B) : C ≤ A ∨ C ≤ B := by
  let : A.Normal := (swapProduct h).second_normal
  let : B.Normal := h.second_normal
  let : IsQuasisimple C := component_quasisimple e
  have hC : IsComponent D C := ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hz : ⁅C, C⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (le_top : C ≤ ⊤).trans
    rw [← h.sup_eq_top]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [commutator_eq_self] at hz
  let : Nontrivial C := e.symm.injective.nontrivial
  exact ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance hz).elim

/-- Containment in a degree-three special linear factor is equality of the
original subgroups, by maximality of quasisimple components. -/
theorem component_eq_linearThree [C.Normal] [A.Normal]
    (e : C ≃* Matrix.PSL3Two.PSL) (hCA : C ≤ A) (F : BinaryField)
    (a : A ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : C = A := by
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect (F := F.Carrier) 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  have hA : IsQuasisimple A := IsQuasisimple.of_mulEquiv a.symm
  exact (show IsComponent D C from
    ⟨(inferInstance : C.Normal).isSubnormal, component_quasisimple e⟩).eq_of_le
      ⟨(inferInstance : A.Normal).isSubnormal, hA⟩ hCA


/-- The order of the actual PSL₃(2) subgroup excludes an S₅ factor. -/
theorem no_symmetricFive_factor (e : C ≃* Matrix.PSL3Two.PSL)
    (hCA : C ≤ A) (a : A ≃* Equiv.Perm (Fin 5)) : False := by
  have hd := card_dvd_of_le hCA
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_PSL,
    Nat.card_congr a.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin] at hd
  norm_num [Nat.factorial] at hd

private def fourElement : Matrix.PSL3Two.SL :=
  ⟨!![1,1,0; 0,1,1; 0,0,1], by decide⟩

private theorem fourElement_order : orderOf fourElement = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4)
  · decide
  · intro p hp hpd
    have hp2 : p = 2 := by
      have hd : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hpd)
      exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    subst p
    decide

private theorem no_linearTwo_embedding (F : BinaryField)
    (f : Matrix.PSL3Two.SL →* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (hf : Function.Injective f) : False := by
  let x := f fourElement
  have ho : orderOf x = 4 := (orderOf_injective f hf fourElement).trans fourElement_order
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ho]; decide)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive F.Carrier 2 P
  let y : P := ⟨x, hP (mem_zpowers x)⟩
  have hy : y ^ 2 = 1 := by
    apply e.symm.injective
    rw [map_pow, map_one]
    rw [pow_two]
    change Multiplicative.ofAdd ((e.symm y).toAdd + (e.symm y).toAdd) = 1
    rw [CharTwo.add_self_eq_zero]
    rfl
  have hx : x ^ 2 = 1 := congrArg Subtype.val hy
  have hd := orderOf_dvd_of_pow_eq_one hx
  norm_num [ho] at hd


/-- The given component cannot be contained in a binary SL₂ factor. -/
theorem no_linearTwo_factor (e : C ≃* Matrix.PSL3Two.PSL)
    (hCA : C ≤ A) (F : BinaryField)
    (a : A ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) : False := by
  let c := Matrix.PSL3Two.equiv.trans e.symm
  exact no_linearTwo_embedding F
    (a.toMonoidHom.comp ((Subgroup.inclusion hCA).comp c.toMonoidHom))
    (a.injective.comp ((Subgroup.inclusion_injective hCA).comp c.injective))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- Exhaust the three natural factor actors on the actual quotient image. -/
theorem component_eq_natural_factor [C.Normal] [A.Normal]
    (e : C ≃* Matrix.PSL3Two.PSL) (hCA : C ≤ A)
    {U : Subrepresentation ρ}
    (h : FactorNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)) :
    C = A := by
  cases h with
  | linearTwo F hn =>
      obtain ⟨a⟩ := hn
      exact (no_linearTwo_factor e hCA F a.groupEquiv).elim
  | symmetricFive hn =>
      obtain ⟨a⟩ := hn
      exact (no_symmetricFive_factor e hCA a.groupEquiv).elim
  | linearThree F _ hn =>
      obtain ⟨a⟩ := hn
      exact component_eq_linearThree e hCA F a.groupEquiv

/-- All source rows make the containing factor equal to the original C. -/
theorem component_eq_source_factor [C.Normal] [A.Normal]
    (e : C ≃* Matrix.PSL3Two.PSL) (hCA : C ≤ A)
    {U : Subrepresentation ρ} (h : SourceFactorCase ρ A U) : C = A := by
  cases h with
  | natural _ hn => exact component_eq_natural_factor e hCA hn
  | doubleNatural F _ _ hn =>
      obtain ⟨a⟩ := hn
      exact component_eq_linearThree e hCA F a.groupEquiv
  | exceptional _ h =>
      exact component_eq_linearThree e hCA BinaryField.two h.natural.groupEquiv

/-- Both original summands are treated; no factor selection is an assumption. -/
theorem twoFactor_component_eq [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SourceTwoFactorCase ρ) : C = c.first ∨ C = c.second := by
  let : c.first.Normal := (swapProduct c.product).second_normal
  let : c.second.Normal := c.product.second_normal
  rcases component_le_factor e c.product with h | h
  · exact Or.inl (component_eq_source_factor e h c.firstCase)
  · exact Or.inr (component_eq_source_factor e h c.secondCase)

/-- In the hyperplane branch the SL₂ second row is impossible for C, while
all repeated SL₃ multiplicities retain the same actor identification. -/
theorem hyperplane_component_eq [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (c : HyperplaneCase ρ) : C = c.first ∨ C = c.second := by
  let : c.first.Normal := (swapProduct c.product).second_normal
  let : c.second.Normal := c.product.second_normal
  rcases component_le_factor e c.product with h | h
  · exact Or.inl (component_eq_linearThree e h BinaryField.two c.firstEquiv)
  · cases c.secondCase with
    | linearThree r _ hn =>
        obtain ⟨a⟩ := hn
        exact Or.inr (component_eq_linearThree e h BinaryField.two a.groupEquiv)
    | linearTwo F hn =>
        obtain ⟨a⟩ := hn
        exact (no_linearTwo_factor e h F a.groupEquiv).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
