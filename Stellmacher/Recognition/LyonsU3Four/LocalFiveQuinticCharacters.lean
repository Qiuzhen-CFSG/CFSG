module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveLinearOrbits
public import Theory.Character.SemidirectLinearInduction
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveOddElements
public import Theory.Character.CharacterKernel

/-!
# The three degree-five characters of the Lyons local group

The nonprincipal linear characters of the Sylow subgroup occur in three free
orbits under the complement.  Induction from one representative of each orbit
therefore gives three genuine irreducible characters of degree five.  This
file records their values on the Sylow factor, on odd-order elements, and on
central products, in the form used in Lyons' Lemma 4 (p. 381).
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))

/-- The induced row attached to a linear character of the Sylow subgroup. -/
def localFiveQuintic (ψ : S →* ℂ) : ConjClassFunction (LocalFiveGroup S α) :=
  SemidirectLinearInduction.induced α ψ

@[simp] theorem localFiveQuintic_apply (ψ : S →* ℂ) (x : LocalFiveGroup S α) :
    localFiveQuintic S α ψ (ConjClasses.mk x) =
      if x.right = 1 then ∑ a : FiveComplement, ψ (α a x.left) else 0 := by
  exact SemidirectLinearInduction.induced_apply α ψ x

theorem localFiveQuintic_isCharacter (ψ : S →* ℂ) :
    IsConjCharacter (localFiveQuintic S α ψ) :=
  SemidirectLinearInduction.induced_isCharacter α ψ

theorem localFiveQuintic_irreducible (h : SylowStructure S) (β : MulAut S)
    (hβ : orderOf β = 15) (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (ψ : S →* ℂ) (hψ : ψ ≠ 1) :
    IsIrreducibleConjCharacter (localFiveQuintic S α ψ) := by
  exact SemidirectLinearInduction.induced_irreducible α ψ
    (sylowLinear_orbit_injective S h β hβ α hα ψ hψ)

theorem localFiveQuintic_degree (ψ : S →* ℂ) :
    localFiveQuintic S α ψ (ConjClasses.mk 1) = 5 := by
  simpa [localFiveQuintic] using (SemidirectLinearInduction.induced_degree α ψ)

theorem localFiveQuintic_restriction (ψ : S →* ℂ) (s : S) :
    localFiveQuintic S α ψ (ConjClasses.mk (SemidirectProduct.inl s)) =
      ∑ a : FiveComplement, ψ (α a s) := by
  simp [localFiveQuintic, SemidirectLinearInduction.induced_apply]

theorem localFiveQuintic_vanishes_off_sylow (ψ : S →* ℂ) (x : LocalFiveGroup S α)
    (hx : x.right ≠ 1) :
    localFiveQuintic S α ψ (ConjClasses.mk x) = 0 := by
  simp [localFiveQuintic_apply, hx]

theorem localFiveQuintic_central_value (h : SylowStructure S)
    (ψ : S →* ℂ) (w : Subgroup.center S) :
    localFiveQuintic S α ψ
        (ConjClasses.mk (SemidirectProduct.inl (w : S))) = 5 := by
  rw [localFiveQuintic_restriction]
  have heq : (∑ a : FiveComplement, ψ (α a (w : S))) =
      ∑ _a : FiveComplement, (1 : ℂ) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hwc : α a (w : S) ∈ Subgroup.center S := by
      have hw : (w : S) ∈ Subgroup.comap (α a).toMonoidHom (Subgroup.center S) := by
        rw [Subgroup.centerCharacteristic.fixed (α a)]
        exact w.property
      exact hw
    exact sylowLinear_center S h ψ ⟨α a (w : S), hwc⟩
  rw [heq]
  simp [FiveComplement]

/- Every central Sylow element acts trivially in the induced realization. -/
theorem localFiveQuintic_representation_kernel (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (ψ : S →* ℂ) (hψ : ψ ≠ 1) (w : Subgroup.center S) :
    ∃ ρ : Representation ℂ (LocalFiveGroup S α) (Fin 5 → ℂ),
      Representation.IsIrreducible ρ ∧
      localFiveQuintic S α ψ = characterClassFunction ρ ∧
      (SemidirectProduct.inl (w : S) : LocalFiveGroup S α) ∈ ρ.ker := by
  have hi := localFiveQuintic_irreducible S α h β hβ hα ψ hψ
  obtain ⟨n, ρ, hr⟩ := hi.1
  have hirr : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (hr ▸ hi.2)
  have hn : n = 5 := by
    have hd := localFiveQuintic_degree S α ψ
    rw [hr] at hd
    change ρ.character 1 = _ at hd
    simp only [Representation.char_one, Module.finrank_fin_fun] at hd
    exact_mod_cast (by simpa using hd : (n : ℂ) = 5)
  subst n
  refine ⟨ρ, hirr, hr, ?_⟩
  rw [ρ.mem_ker_iff_character_eq_degree]
  change characterClassFunction ρ
      (ConjClasses.mk (SemidirectProduct.inl (w : S))) =
    characterClassFunction ρ (ConjClasses.mk 1)
  calc
    characterClassFunction ρ
        (ConjClasses.mk (SemidirectProduct.inl (w : S))) =
        localFiveQuintic S α ψ
          (ConjClasses.mk (SemidirectProduct.inl (w : S))) := by rw [hr]
    _ = 5 := localFiveQuintic_central_value S α h ψ w
    _ = localFiveQuintic S α ψ (ConjClasses.mk 1) :=
      (localFiveQuintic_degree S α ψ).symm
    _ = characterClassFunction ρ (ConjClasses.mk 1) := by rw [hr]

theorem localFiveQuintic_odd_value (ψ : S →* ℂ) (u : LocalFiveGroup S α)
    (hu : Odd (orderOf u)) :
    localFiveQuintic S α ψ (ConjClasses.mk u) = if u = 1 then 5 else 0 := by
  by_cases he : u = 1
  · subst u
    simp [localFiveQuintic_apply]
  · have hr : u.right ≠ 1 := mt (localFive_odd_right_eq_one_iff S α u hu).mp he
    simp [localFiveQuintic_apply, hr, he]

theorem localFiveQuintic_joint_injective (h : SylowStructure S) (β : MulAut S)
    (hβ : orderOf β = 15) (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (ψ : Fin 3 → S →* ℂ)
    (hψ : (∀ i, ψ i ≠ 1) ∧
      Function.Injective (fun p : Fin 3 × FiveComplement =>
        (ψ p.1).comp (α p.2).toMonoidHom)) :
    Function.Injective (fun i => localFiveQuintic S α (ψ i)) := by
  intro i j he
  obtain ⟨a, ha⟩ := SemidirectLinearInduction.orbit_of_induced_eq α (ψ i) (ψ j)
    (sylowLinear_orbit_injective S h β hβ α hα (ψ i) (hψ.1 i)) he
  apply Fin.ext
  have hh : (fun p : Fin 3 × FiveComplement =>
      (ψ p.1).comp (α p.2).toMonoidHom) (i, a) =
      (fun p : Fin 3 × FiveComplement =>
      (ψ p.1).comp (α p.2).toMonoidHom) (j, 1) := by
    have ha' : (ψ i).comp (α a).toMonoidHom =
        (ψ j).comp (α 1).toMonoidHom := by
      ext s
      simpa using congrArg (fun f : S →* ℂ => f s) ha
    exact ha'
  exact congrArg (fun p : Fin 3 × FiveComplement => p.1.val) (hψ.2 hh)

/-- The three genuine degree-five induced rows. -/
theorem exists_three_quintic_characters (h : SylowStructure S) (β : MulAut S)
    (hβ : orderOf β = 15) (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ)) :
    ∃ τ : Fin 3 → ConjClassFunction (LocalFiveGroup S α),
      (∀ i, IsIrreducibleConjCharacter (τ i)) ∧
      Function.Injective τ ∧
      (∀ i, τ i (ConjClasses.mk 1) = 5) := by
  obtain ⟨ψ, hnon, hinj, _⟩ := exists_three_linear_orbits S h β hβ α hα
  refine ⟨fun i => localFiveQuintic S α (ψ i), ?_,
    localFiveQuintic_joint_injective S α h β hβ hα ψ ⟨hnon, hinj⟩, ?_⟩
  · intro i
    exact localFiveQuintic_irreducible S α h β hβ hα (ψ i) (hnon i)
  · intro i
    exact localFiveQuintic_degree S α (ψ i)

theorem localFiveQuintic_lemma_five (h : SylowStructure S) (β : MulAut S)
    (_hβ : orderOf β = 15) (_hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (i : Fin 3) (ψ : Fin 3 → S →* ℂ)
    (_hψ : (∀ j, ψ j ≠ 1) ∧
      Function.Injective (fun p : Fin 3 × FiveComplement =>
        (ψ p.1).comp (α p.2).toMonoidHom))
    (w : Subgroup.center S) (_hw : w ≠ 1) (u : LocalFiveGroup S α)
    (hu : Odd (orderOf u)) :
    localFiveQuintic S α (ψ i)
        (ConjClasses.mk (SemidirectProduct.inl (w : S) * u)) =
      ∑ χ : FiveLinearIndex, χ u.right := by
  by_cases he : u = 1
  · subst u
    simp only [mul_one]
    rw [localFiveQuintic_central_value S α h]
    rw [AbelianLinearCharacters.sum_apply]
    simp
  · have hr : u.right ≠ 1 := mt (localFive_odd_right_eq_one_iff S α u hu).mp he
    rw [localFiveQuintic_apply]
    simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
    rw [if_neg hr, AbelianLinearCharacters.sum_apply, if_neg hr]

end
end Stellmacher.Recognition.LyonsU3Four
