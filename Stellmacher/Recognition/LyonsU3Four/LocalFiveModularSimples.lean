module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveLinearCharacters
public import Theory.Character.ModularBlock.BrauerLinearCharacters
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient

/-!
# The five genuine modular simple modules of the Lyons local group

The normal Sylow two-subgroup acts trivially on a simple module in
characteristic two. Restriction to the complement therefore preserves
irreducibility. The complement is abelian, so every simple module over the
prescribed splitting field has dimension one. Its determinant lifts through
the datum's coefficient map to one of the five complex linear characters.
Conversely, reducing those five characters constructs the five scalar modules.
Their eigenvalue-defined Brauer values are the original complex characters,
and evaluation on the complement proves their linear independence.

No assertion about principal-block membership is used here.
Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace Stellmacher.Recognition.LyonsU3Four
open ModularBlock PrincipalBlockConstruction BrauerCoefficientExtension BrauerLinearCharacters

private theorem fiveComplement_pow_five (a : FiveComplement) : a ^ 5 = 1 := by
  simpa [FiveComplement, Nat.card_eq_fintype_card] using (pow_card_eq_one' (x := a))

variable {G : Type*} [Group G] [Finite G]
  (S : Sylow 2 G) (α : FiveComplement →* MulAut S)

omit [Finite G] in
private theorem five_dvd_local_card : 5 ∣ Nat.card (LocalFiveGroup S α) := by
  rw [SemidirectProduct.card]
  have hc : Nat.card FiveComplement = 5 := by simp [FiveComplement, Nat.card_eq_fintype_card]
  rw [hc]
  exact dvd_mul_left 5 _

/-- The normal Sylow subgroup acts trivially on every modular simple module. -/
theorem localFive_modular_inl_eq_one
    {F V : Type*} [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F (LocalFiveGroup S α) V) [Representation.IsIrreducible ρ]
    (s : S) : ρ (SemidirectProduct.inl s) = 1 := by
  let N := (SemidirectProduct.inl : S →* LocalFiveGroup S α).range
  have hN : N = (SemidirectProduct.rightHom : LocalFiveGroup S α →* FiveComplement).ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  let : N.Normal := hN ▸ inferInstance
  have hp : IsPGroup 2 N := S.isPGroup'.of_surjective
    (SemidirectProduct.inl : S →* LocalFiveGroup S α).rangeRestrict
    (SemidirectProduct.inl : S →* LocalFiveGroup S α).rangeRestrict_surjective
  exact MonoidHom.mem_ker.mp (Representation.normal_p_subgroup_le_ker ρ N hp ⟨s, rfl⟩)

/-- Every simple action factors through the order-five complement. -/
theorem localFive_modular_eq_right
    {F V : Type*} [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F (LocalFiveGroup S α) V) [Representation.IsIrreducible ρ]
    (x : LocalFiveGroup S α) : ρ x = ρ (SemidirectProduct.inr x.right) := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul,
    localFive_modular_inl_eq_one S α ρ, one_mul]

/-- All simple modules over an algebraically closed field of characteristic two are linear. -/
theorem localFive_modular_finrank_eq_one
    {F V : Type*} [Field F] [CharP F 2] [IsAlgClosed F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F (LocalFiveGroup S α) V) [Representation.IsIrreducible ρ] :
    Module.finrank F V = 1 := by
  let σ := ρ.comp (SemidirectProduct.inr : FiveComplement →* LocalFiveGroup S α)
  have he : σ.comp SemidirectProduct.rightHom = ρ := by
    ext x v
    exact LinearMap.congr_fun (localFive_modular_eq_right S α ρ x).symm v
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff SemidirectProduct.rightHom
      SemidirectProduct.rightHom_surjective σ).mp (by rw [he]; infer_instance)
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative σ

variable (d : PrincipalCongruenceBlockData (LocalFiveGroup S α))

/-- A complement character takes values in the actual cyclotomic order. -/
@[expose] def localFiveIntegralHom (χ : FiveLinearIndex) :
    FiveComplement →* cyclotomicOrder d.eta where
  toFun a := ⟨χ a, root_mem_cyclotomicOrder_of_pow_eq_one_of_dvd (n := 5) d.eta_spec
    Nat.card_pos.ne' (by rw [← map_pow, fiveComplement_pow_five, map_one])
    (by exact five_dvd_local_card S α)⟩
  map_one' := Subtype.ext χ.map_one
  map_mul' a b := Subtype.ext (χ.map_mul a b)

/-- The modular complement character uses the prescribed reduction map. -/
@[expose] def localFiveReducedHom (χ : FiveLinearIndex) :
    FiveComplement →* splittingField d :=
  (reduction d).toMonoidHom.comp (localFiveIntegralHom S α d χ)

/-- A genuine characteristic-two simple representation, indexed by a complex linear row. -/
@[expose] def localFiveModularRep (χ : FiveLinearIndex) :
    Representation (splittingField d) (LocalFiveGroup S α) (Fin 1 → splittingField d) :=
  scalarRepresentation ((localFiveReducedHom S α d χ).comp SemidirectProduct.rightHom)

theorem localFiveModularRep_irreducible (χ : FiveLinearIndex) :
    Representation.IsIrreducible (localFiveModularRep S α d χ) :=
  scalarRepresentation_irreducible _

/-- The actual eigenvalue lifts recover the specified ordinary linear row. -/
theorem localFiveModularRep_value (χ : FiveLinearIndex) (u : LocalFiveGroup S α) :
    BrauerCharacter.value d (localFiveModularRep S α d χ) u = χ u.right := by
  rw [localFiveModularRep, scalarRepresentation_value]
  change (BrauerCharacter.eigenvalueLift d
    (reduction d (localFiveIntegralHom S α d χ u.right)) : ℂ) = _
  rw [eigenvalueLift_reduction d (by decide : Odd 5) (five_dvd_local_card S α)
    _ (by rw [← map_pow, fiveComplement_pow_five, map_one])]
  rfl

/-- These five modules exhaust every finite-dimensional irreducible over the splitting field. -/
theorem localFiveModularRep_complete
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) (LocalFiveGroup S α) V)
    [Representation.IsIrreducible ρ] :
    ∃ χ : FiveLinearIndex, Nonempty (ρ.Equiv (localFiveModularRep S α d χ)) := by
  let ψ : FiveComplement →* splittingField d := LinearMap.det.comp
    (ρ.comp (SemidirectProduct.inr : FiveComplement →* LocalFiveGroup S α))
  have hp (a : FiveComplement) : ψ a ^ 5 = 1 := by
    rw [← map_pow, fiveComplement_pow_five, map_one]
  let l := liftHom d ψ 5 (by decide) (five_dvd_local_card S α) hp
  let χ : FiveLinearIndex := (cyclotomicOrder d.eta).subtype.toMonoidHom.comp l
  have hl (a : FiveComplement) : localFiveIntegralHom S α d χ a = l a := by
    apply Subtype.ext
    rfl
  have he : (localFiveReducedHom S α d χ).comp SemidirectProduct.rightHom =
      LinearMap.det.comp ρ := by
    ext x
    change reduction d (localFiveIntegralHom S α d χ x.right) = LinearMap.det (ρ x)
    rw [hl, reduction_liftHom]
    exact congrArg LinearMap.det (localFive_modular_eq_right S α ρ x).symm
  refine ⟨χ, ?_⟩
  unfold localFiveModularRep
  rw [he]
  exact equiv_scalarRepresentation_det ρ (localFive_modular_finrank_eq_one S α ρ)

/-- Independence of the genuine Brauer characters follows by evaluation on the complement. -/
theorem localFiveModularRep_linearIndependent :
    LinearIndependent ℂ (fun χ : FiveLinearIndex =>
      BrauerCharacter.character d (localFiveModularRep S α d χ)) := by
  let c (a : FiveComplement) : BrauerCharacter.TwoRegularClasses (LocalFiveGroup S α) :=
    BrauerCharacter.twoRegularClass (SemidirectProduct.inr a)
      ((by decide : Odd 5).of_dvd_nat (orderOf_dvd_of_pow_eq_one (by
        rw [← map_pow, fiveComplement_pow_five, map_one])))
  apply LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ c)
  have he : (LinearMap.funLeft ℂ ℂ c) ∘ (fun χ : FiveLinearIndex =>
      BrauerCharacter.character d (localFiveModularRep S α d χ)) =
      (fun χ : FiveLinearIndex => (χ : FiveComplement → ℂ)) := by
    funext χ a
    exact localFiveModularRep_value S α d χ (SemidirectProduct.inr a)
  rw [he]
  exact linearIndependent_monoidHom FiveComplement ℂ

/-- An enumeration of the five actual complex complement characters. -/
def fiveLinearEnumeration : Fin 5 ≃ FiveLinearIndex := by
  let : Fintype FiveLinearIndex := Fintype.ofFinite _
  exact (Fintype.equivFinOfCardEq (by simpa only [← Nat.card_eq_fintype_card]
    using fiveLinearIndex_card)).symm

/-- Five genuine simple modules, their exhaustive classification, prescribed values,
and independent Brauer characters. No principal-membership premise is required. -/
theorem exists_localFiveModularSimples :
    ∃ (e : Fin 5 ≃ FiveLinearIndex)
      (ρ : Fin 5 → Representation (splittingField d) (LocalFiveGroup S α)
        (Fin 1 → splittingField d)),
      (∀ j, Representation.IsIrreducible (ρ j)) ∧
      (∀ (V : Type*) [AddCommGroup V] [Module (splittingField d) V]
        [FiniteDimensional (splittingField d) V]
        (σ : Representation (splittingField d) (LocalFiveGroup S α) V)
        [Representation.IsIrreducible σ], ∃ j, Nonempty (σ.Equiv (ρ j))) ∧
      (∀ j u, Odd (orderOf u) → BrauerCharacter.value d (ρ j) u = e j u.right) ∧
      LinearIndependent ℂ (fun j => BrauerCharacter.character d (ρ j)) := by
  refine ⟨fiveLinearEnumeration, fun j => localFiveModularRep S α d (fiveLinearEnumeration j),
    fun j => localFiveModularRep_irreducible S α d _, ?_, ?_, ?_⟩
  · intro V _ _ _ σ _
    obtain ⟨χ, hχ⟩ := localFiveModularRep_complete S α d σ
    exact ⟨fiveLinearEnumeration.symm χ, by simpa using hχ⟩
  · intro j u _
    exact localFiveModularRep_value S α d _ u
  · exact (localFiveModularRep_linearIndependent S α d).comp
      fiveLinearEnumeration fiveLinearEnumeration.injective

end Stellmacher.Recognition.LyonsU3Four
