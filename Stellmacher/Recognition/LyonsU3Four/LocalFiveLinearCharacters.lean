module

public import Stellmacher.Recognition.LyonsU3Four.OrderFourFusionFromAutomizer
public import Theory.Character.AbelianLinearCharacters

/-!
# Characters of the supplied Lyons local group

For the semidirect product of the intrinsic Sylow group by a cyclic group of
order five, this module constructs the five distinct ordinary linear rows by
inflation. Their values and restrictions are explicit, and every linear character is one
of these rows: the displacement map on the central quotient is surjective,
forcing an invariant linear character of the Sylow group to be principal.
The order-five action
fixes exactly the center of the Sylow group and is fixed-point-free on its
central quotient. These facts supply the local input for the nonlinear rows.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 2,
p. 373, and Lemma 4, p. 381.
-/

namespace Stellmacher.Recognition.LyonsU3Four

public abbrev FiveComplement := Multiplicative (ZMod 5)

/-- The local group for a supplied action of the complement. -/
public abbrev LocalFiveGroup {G : Type*} [Group G] (S : Sylow 2 G)
    (α : FiveComplement →* MulAut S) := S ⋊[α] FiveComplement

public instance localFiveGroup_finite {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (α : FiveComplement →* MulAut S) : Finite (LocalFiveGroup S α) :=
  Finite.of_equiv (S × FiveComplement) SemidirectProduct.equivProd.symm

/-- The explicit local group has order 320. -/
public theorem localFiveGroup_card {G : Type*} [Group G] (S : Sylow 2 G)
    (h : SylowStructure S) (α : FiveComplement →* MulAut S) :
    Nat.card (LocalFiveGroup S α) = 320 := by
  rw [SemidirectProduct.card, h.card]
  norm_num [FiveComplement, Nat.card_eq_fintype_card]

/-- The cube of the supplied automorphism has order five. -/
public theorem order_fifteen_cube_order {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (β : MulAut S) (hβ : orderOf β = 15) :
    orderOf (β ^ (3 : ℕ)) = 5 := by
  rw [orderOf_pow, hβ]
  decide

/-- The complement action fixes the center pointwise. -/
public theorem order_fifteen_cube_fixes_center {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (z : Subgroup.center S) : (β ^ (3 : ℕ)) (z : S) = z := by
  have he : MulAut.characteristic (Subgroup.center S) (β ^ (3 : ℕ)) = 1 := by
    rw [map_pow, ← order_fifteen_center_order S h β hβ]
    exact pow_orderOf_eq_one _
  exact congrArg Subtype.val (DFunLike.congr_fun he z)

/-- No nonidentity central coset is fixed by the complement generator. -/
public theorem order_fifteen_cube_quotient_fixed_eq_one
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (x : S ⧸ Subgroup.center S)
    (hx : (Subgroup.quotientAut (Subgroup.center S) β ^ (3 : ℕ)) x = x) : x = 1 := by
  let a := Subgroup.quotientAut (Subgroup.center S) β ^ (3 : ℕ)
  have ha : orderOf a = 5 := by
    rw [orderOf_pow, order_fifteen_quotient_order S h β hβ]
    decide
  by_contra hne
  have he := MulAut.eq_one_of_commute_five_of_fixed (center_quotient_card S h)
    a a ha (Commute.refl a) x hne hx
  simp [he] at ha

/-- The fixed subgroup of the order-five generator is exactly the Sylow center. -/
public theorem order_fifteen_cube_fixed_iff_mem_center
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (s : S) : (β ^ (3 : ℕ)) s = s ↔ s ∈ Subgroup.center S := by
  constructor
  · intro hs
    apply (QuotientGroup.eq_one_iff s).mp
    apply order_fifteen_cube_quotient_fixed_eq_one S h β hβ
    change (Subgroup.quotientAut (Subgroup.center S) β ^ (3 : ℕ))
      (QuotientGroup.mk' (Subgroup.center S) s) = QuotientGroup.mk' (Subgroup.center S) s
    rw [← map_pow, Subgroup.quotientAut_apply_mk, hs]
  · exact fun hs => order_fifteen_cube_fixes_center S h β hβ ⟨s, hs⟩

/-- The five indices are actual complex characters of the complement. -/
public abbrev FiveLinearIndex := FiveComplement →* ℂ

public theorem fiveLinearIndex_card : Nat.card FiveLinearIndex = 5 := by
  rw [AbelianLinearCharacters.card]
  simp [FiveComplement, Nat.card_eq_fintype_card]

/-- Inflation of a complement character to the supplied semidirect product. -/
@[expose] public noncomputable def localFiveLinearHom
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (χ : FiveLinearIndex) : LocalFiveGroup S α →* ℂ :=
  χ.comp SemidirectProduct.rightHom

/-- Every constructed row is a genuine irreducible degree-one character. -/
public theorem localFiveLinear_isLinear
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (χ : FiveLinearIndex) :
    IsLinearCharacter (localFiveLinearHom S α χ : LocalFiveGroup S α → ℂ) :=
  (localFiveLinearHom S α χ).isLinearCharacter

/-- Each linear row restricts to the principal character on the Sylow group. -/
@[simp] public theorem localFiveLinear_inl
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (χ : FiveLinearIndex) (s : S) :
    localFiveLinearHom S α χ (SemidirectProduct.inl s) = 1 := by
  simp [localFiveLinearHom]

/-- The complement values of a linear row are its indexing character. -/
@[simp] public theorem localFiveLinear_inr
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (χ : FiveLinearIndex) (a : FiveComplement) :
    localFiveLinearHom S α χ (SemidirectProduct.inr a) = χ a := by
  simp [localFiveLinearHom]

/-- The value formula applies to all elements, in particular odd-order elements. -/
public theorem localFiveLinear_apply
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (χ : FiveLinearIndex) (x : LocalFiveGroup S α) :
    localFiveLinearHom S α χ x = χ x.right := rfl

/-- The five linear rows are pairwise distinct as ordinary characters. -/
public theorem localFiveLinear_injective
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S) :
    Function.Injective (fun χ => (localFiveLinearHom S α χ : LocalFiveGroup S α → ℂ)) := by
  intro χ ψ he
  ext a
  exact congrFun he (SemidirectProduct.inr a)

/-- Every linear character trivial on the Sylow group is one of these rows. -/
public theorem localFiveLinear_exhausts_trivial_restriction
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (φ : LocalFiveGroup S α → ℂ) (hφ : IsLinearCharacter φ)
    (hS : ∀ s : S, φ (SemidirectProduct.inl s) = 1) :
    ∃ χ : FiveLinearIndex, (localFiveLinearHom S α χ : LocalFiveGroup S α → ℂ) = φ := by
  refine ⟨hφ.toMonoidHom.comp SemidirectProduct.inr, ?_⟩
  funext x
  change φ (SemidirectProduct.inr x.right) = φ x
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hφ.map_mul, hS, one_mul]

/-- A linear character invariant under the order-five generator is principal on S. -/
public theorem cube_invariant_linear_eq_one
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (θ : S →* ℂˣ) (hθ : ∀ s, θ ((β ^ (3 : ℕ)) s) = θ s) (s : S) : θ s = 1 := by
  let Z := Subgroup.center S
  let Q := S ⧸ Z
  let a := Subgroup.quotientAut Z β ^ (3 : ℕ)
  have hker : Z ≤ θ.ker := by
    rw [show Z = commutator S from h.center_eq_commutator]
    exact Abelianization.commutator_subset_ker θ
  let f : Q →* ℂˣ := QuotientGroup.lift Z θ hker
  have hfix (x : Q) (hx : a x = x) : x = 1 :=
    order_fifteen_cube_quotient_fixed_eq_one S h β hβ x hx
  have hf (x : Q) : f (a x) = f x := by
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective Z x
    change f ((Subgroup.quotientAut Z β ^ (3 : ℕ)) (QuotientGroup.mk' Z t)) = _
    rw [← map_pow, Subgroup.quotientAut_apply_mk]
    exact hθ t
  have hinj : Function.Injective (fun x : Q => a x * x⁻¹) := by
    intro x y he
    change a x * x⁻¹ = a y * y⁻¹ at he
    have hh : a (y⁻¹ * x) = y⁻¹ * x := by
      rw [map_mul, map_inv]
      calc
        (a y)⁻¹ * a x = (a y)⁻¹ * (a x * x⁻¹) * x := by group
        _ = (a y)⁻¹ * (a y * y⁻¹) * x := by rw [he]
        _ = y⁻¹ * x := by group
    exact (inv_mul_eq_one.mp (hfix _ hh)).symm
  obtain ⟨x, hx⟩ := (Finite.surjective_of_injective hinj) (QuotientGroup.mk' Z s)
  change f (QuotientGroup.mk' Z s) = 1
  rw [← hx, map_mul, map_inv, hf, mul_inv_cancel]

/-- Every linear character of the supplied local group is trivial on its Sylow subgroup. -/
public theorem localFiveLinear_trivial_on_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (φ : LocalFiveGroup S α → ℂ) (hφ : IsLinearCharacter φ) (s : S) :
    φ (SemidirectProduct.inl s) = 1 := by
  let f := hφ.toMonoidHom.toHomUnits
  let θ : S →* ℂˣ := f.comp SemidirectProduct.inl
  have hθ (t : S) : θ ((β ^ (3 : ℕ)) t) = θ t := by
    change f (SemidirectProduct.inl ((β ^ (3 : ℕ)) t)) = f (SemidirectProduct.inl t)
    rw [← hα, SemidirectProduct.inl_aut]
    simp [mul_comm]
  exact congrArg Units.val (cube_invariant_linear_eq_one S h β hβ θ hθ s)

/-- These five rows exhaust all degree-one irreducible characters. -/
public theorem localFiveLinear_complete
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (φ : LocalFiveGroup S α → ℂ) (hφ : IsLinearCharacter φ) :
    ∃! χ : FiveLinearIndex, (localFiveLinearHom S α χ : LocalFiveGroup S α → ℂ) = φ := by
  obtain ⟨χ, hχ⟩ := localFiveLinear_exhausts_trivial_restriction S α φ hφ
    (localFiveLinear_trivial_on_sylow S h β hβ α hα φ hφ)
  exact ⟨χ, hχ, fun ψ hψ => localFiveLinear_injective S α (hψ.trans hχ.symm)⟩

/-- The linear rows as class functions, for assembling the complete ordinary table. -/
@[expose] public noncomputable def localFiveLinear
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (χ : FiveLinearIndex) : ConjClassFunction (LocalFiveGroup S α) :=
  toConjClassFunction (localFiveLinearHom S α χ) (by
    intro x y
    change χ (y.right * x.right * y.right⁻¹) = χ x.right
    congr 1
    simp [mul_comm])

@[simp] public theorem localFiveLinear_mk
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S)
    (χ : FiveLinearIndex) (x : LocalFiveGroup S α) :
    localFiveLinear S α χ (ConjClasses.mk x) = χ x.right := rfl

/-- The class-function rows are afforded by irreducible complex representations. -/
public theorem localFiveLinear_irreducible
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (α : FiveComplement →* MulAut S) (χ : FiveLinearIndex) :
    IsIrreducibleConjCharacter (localFiveLinear S α χ) := by
  obtain ⟨n, ρ, hρ, he⟩ := (localFiveLinear_isLinear S α χ).1
  have hc : localFiveLinear S α χ = characterClassFunction ρ := by
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    exact congrFun he x
  rw [hc]
  exact isIrreducibleCharacter_characterClassFunction ρ hρ

/-- Pairwise distinctness in the same interface as complete character families. -/
public theorem localFiveLinear_class_injective
    {G : Type*} [Group G] (S : Sylow 2 G) (α : FiveComplement →* MulAut S) :
    Function.Injective (localFiveLinear S α) := by
  intro χ ψ he
  apply localFiveLinear_injective S α
  funext x
  exact congrFun he (ConjClasses.mk x)

end Stellmacher.Recognition.LyonsU3Four
