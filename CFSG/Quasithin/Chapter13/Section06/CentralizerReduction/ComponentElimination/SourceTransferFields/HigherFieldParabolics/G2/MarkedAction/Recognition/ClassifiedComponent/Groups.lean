module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent.Rows
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Excluding the other adequate B.5.6 branches

Component normality dichotomies place a component in one of the two factors of
an actual internal product. An SL₂ or SL₃ factor is quasisimple (apart from the
small SL₂(2) endpoint), so its contained component is the whole factor. The
actual factor action equivalences and ModelSeparation exclude every natural,
double-natural and exceptional factor in (3), and both second factors in (5).

For the outer A₆–C₃ configuration, the displayed product is normal with cyclic
quotient. Perfectness puts the component inside this product and kills its C₃
projection, placing it in the literal A₆ factor. No order bound on the ambient
outer extension or on its specified generator is assumed.

Source: Aschbacher–Smith B.5.6(2)–(5), printed p.105, as used before 13.6.14
and in 13.6.19, pp.929–931. Component calculus and the attributed ATLAS matrix
simplicity proofs are reused from the imports.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent
variable {D : Type*} [Group D] [Finite D] {C A B : Subgroup D} {F : BinaryField}

private theorem no_small_overgroup (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (hCA : C ≤ A)
    (hA : Nat.card A ≤ 9999360) : False :=
  no_small_equiv sep mark (MulEquiv.refl C)
    ((Nat.card_le_card_of_injective (inclusion hCA) (inclusion_injective hCA)).trans hA)

omit [Finite D] in
private theorem component_eq_of_quasisimple (hC : IsComponent D C) (hCA : C ≤ A)
    [IsQuasisimple A] : C = A := by
  have ht : IsComponent A ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv (topEquiv).symm⟩
  exact le_antisymm hCA (subgroupOf_eq_top.mp ((hC.subgroupOf hCA).eq_of_le ht le_top))

private theorem slTwo_quasisimple (E : BinaryField) (hn : 2 ≤ E.degree) :
    IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) E.Carrier) := by
  have hcard : 4 ≤ Nat.card E.Carrier := by
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hfield : ∃ a : E.Carrier, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ : IsCyclic E.Carrierˣ := inferInstance
    refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
    grw [Nat.card_eq_card_units_add_one E.Carrier,
      ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hcard
    omega
  exact { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top hfield.choose_spec.1 hfield.choose_spec.2⟩
          simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard }

private theorem no_linearTwo_factor (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (hC : IsComponent D C) (hCA : C ≤ A)
    (E : BinaryField) (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) : False := by
  by_cases hn : E.degree = 1
  · apply no_small_overgroup sep mark hCA
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, E.card_eq, hn]
    norm_num
  · let := slTwo_quasisimple E (by have := E.degree_pos; omega)
    let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
    exact sep.not_linearTwo E ⟨mark.symm.trans
      ((MulEquiv.subgroupCongr (component_eq_of_quasisimple hC hCA)).trans e)⟩

omit [Finite D] in
private theorem no_linearThree_factor (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (hC : IsComponent D C) (hCA : C ≤ A)
    (E : BinaryField) (e : A ≃* Matrix.SpecialLinearGroup (Fin 3) E.Carrier) : False := by
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) E.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  exact sep.not_linearThree E ⟨mark.symm.trans
    ((MulEquiv.subgroupCongr (component_eq_of_quasisimple hC hCA)).trans e)⟩

omit [Finite D] in
private theorem product_commute (p : InternalProduct A B) (a : A) (b : B) :
    (a : D) * (b : D) = (b : D) * (a : D) := by
  have hh : p.equiv ((a,1) * (1,b)) = p.equiv ((1,b) * (a,1)) := by simp
  rw [map_mul, map_mul] at hh
  simpa only [p.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hh

omit [Finite D] in
private theorem product_first_normal (p : InternalProduct A B) : A.Normal := by
  let e : (B × A) ≃* D := MulEquiv.prodComm.trans p.equiv
  let p' : InternalProduct B A := ⟨e, fun b a => (p.apply_eq a b).trans (product_commute p a b)⟩
  exact p'.second_normal

omit [Finite D] in
private theorem component_in_product (hC : IsComponent D C) (p : InternalProduct A B) :
    C ≤ A ∨ C ≤ B := by
  let := product_first_normal p
  let := p.second_normal
  rcases hC.normal_dichotomy A with h | hA
  · exact Or.inl h
  rcases hC.normal_dichotomy B with h | hB
  · exact Or.inr h
  have hle : C ≤ A ⊔ B := by rw [p.sup_eq_top]; exact le_top
  have hcomm : ⁅C, C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hle.trans (sup_le
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hA))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hB))))
  let := hC.2
  rw [commutator_eq_self] at hcomm
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  exact ((nontrivial_iff_ne_bot C).mp inferInstance hcomm).elim

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

private theorem no_source_factor (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (hC : IsComponent D C) (hCA : C ≤ A)
    {U : Subrepresentation ρ} (a : SourceFactorCase ρ A U) : False := by
  cases a with
  | natural _ h =>
    cases h with
    | linearTwo E hn =>
      obtain ⟨e⟩ := hn
      exact no_linearTwo_factor sep mark hC hCA E e.groupEquiv
    | symmetricFive hn =>
      obtain ⟨e⟩ := hn
      apply no_small_overgroup sep mark hCA
      rw [Nat.card_congr e.groupEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    | linearThree E _ hn =>
      obtain ⟨e⟩ := hn
      exact no_linearThree_factor sep mark hC hCA E e.groupEquiv
  | doubleNatural E _ _ hn =>
    obtain ⟨e⟩ := hn
    exact no_linearThree_factor sep mark hC hCA E e.groupEquiv
  | exceptional _ e =>
    exact no_linearThree_factor sep mark hC hCA BinaryField.two e.natural.groupEquiv

theorem no_twoFactors (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (hC : IsComponent D C)
    (c : SourceTwoFactorCase ρ) : False := by
  rcases component_in_product hC c.product with h | h
  · exact no_source_factor sep mark hC h c.firstCase
  · exact no_source_factor sep mark hC h c.secondCase

theorem no_hyperplane (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (hC : IsComponent D C)
    (c : HyperplaneCase ρ) : False := by
  rcases component_in_product hC c.product with h | h
  · exact no_linearThree_factor sep mark hC h BinaryField.two c.firstEquiv
  · cases c.secondCase with
    | linearThree _ _ hn =>
      obtain ⟨e⟩ := hn
      exact no_linearThree_factor sep mark hC h BinaryField.two e.groupEquiv
    | linearTwo E hn =>
      obtain ⟨e⟩ := hn
      exact no_linearTwo_factor sep mark hC h E e.groupEquiv

theorem no_symmetricThree (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (c : SymmetricThreeCase ρ) : False := by
  apply no_small_equiv sep mark (MulEquiv.refl C)
  apply (Nat.card_le_card_of_injective C.subtype C.subtype_injective).trans
  rw [Nat.card_congr c.equiv.toEquiv, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

omit [Finite D] in
private theorem normalizes_of_automorphism (S : Subgroup D) (t : D)
    (α : MulAut S) (hα : ∀ a : S, (α a : D) = t * a * t⁻¹) :
    t ∈ normalizer (S : Set D) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    rw [← hα ⟨x, hx⟩]
    exact (α ⟨x, hx⟩).property
  · intro hx
    let y : S := ⟨t * x * t⁻¹, hx⟩
    have he := hα (α.symm y)
    rw [α.apply_symm_apply] at he
    have hx' : x = (α.symm y : D) := (MulAut.conj t).injective he
    rw [hx']
    exact (α.symm y).property

omit [Finite D] in
theorem outer_component_le_first (hC : IsComponent D C) (c : OuterSixThreeShape D) :
    C ≤ c.first := by
  let := hC.2
  let P := c.first ⊔ c.second
  let : P.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← c.generates]
    refine sup_le P.le_normalizer (zpowers_le.mpr ?_)
    obtain ⟨a, ha, _⟩ := c.firstOuter
    obtain ⟨b, hb, _⟩ := c.secondOuter
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
      ⟨normalizes_of_automorphism _ _ a ha, normalizes_of_automorphism _ _ b hb⟩
  let : IsCyclic (D ⧸ P) := by
    let q := QuotientGroup.mk' P
    apply isCyclic_iff_exists_zpowers_eq_top.mpr
    refine ⟨q c.element, ?_⟩
    have h := congrArg (Subgroup.map q) c.generates
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h
  have hCP : C ≤ P := le_of_isPerfect_of_solvable_quotient C P
  let f : C →* c.second := (MonoidHom.snd c.first c.second).comp
    (c.product.symm.toMonoidHom.comp (inclusion hCP))
  let : IsMulCommutative c.second := ⟨⟨fun a b => c.secondEquiv.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf (x : C) : f x = 1 := congrArg f.range.subtype
    (Subsingleton.elim (⟨f x, ⟨x, rfl⟩⟩ : f.range) 1)
  intro x hx
  let xp : P := ⟨x, hCP hx⟩
  let ab := c.product.symm xp
  have hb : ab.2 = 1 := hf ⟨x, hx⟩
  have he := c.product_apply ab.1 ab.2
  have he' : x = (ab.1 : D) := by
    change (c.product (c.product.symm xp) : D) = (ab.1 : D) * (ab.2 : D) at he
    rw [c.product.apply_symm_apply, hb, OneMemClass.coe_one, mul_one] at he
    exact he
  rw [he']
  exact ab.1.property

theorem no_outerSixThree (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (hC : IsComponent D C)
    (c : OuterSixThreeShape D) : False := by
  apply no_small_overgroup sep mark (outer_component_le_first hC c)
  rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent
