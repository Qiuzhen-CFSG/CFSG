module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.Natural
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.OddCentralKernels
public import Theory.GroupTheory.UniversalCoverKernelTransport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Assembly of the exceptional PSU₄(3) covering kernel

Two actual perfect central covers give surjections from the canonical
universal kernel onto their kernels. If the two kernels have coprime orders,
the product map is surjective. An upper bound of 36 therefore identifies
that kernel with E₉ × C₄ once an exceptional E₉-cover is constructed; the
natural SU₄(3) map provides C₄ and its perfectness is proved in `Natural`.

The proved prime-support theorem reduces the upper bound to exclusion of
8, 27 and 5 as divisors. Model transport then supplies the literal finite
quasisimple universal covering over every allowed coefficient field and
Hermitian form, preserving the kernel's multiplicative structure.

The exported assembly is conditional. The exceptional E₉-cover and the
exclusions of 8 and 27 still require independent proofs. Exclusion of 5 is
the separate nondefining-prime input. Thus this module does not yet prove
the unconditional multiplier row in Aschbacher–Smith I.1.4(5),
`refs/quasithin.pdf`, printed p.408; see GLS3 §6.1, Tables 6.1.2–6.1.3.
-/

public section

open Matrix BenderSuzuki.MatrixGroups Theory.GroupTheory PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary

noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional

abbrev ExceptionalKernel := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
abbrev Kernel := ExceptionalKernel × Multiplicative (ZMod 4)

private theorem prod_surjective_of_coprime
    {K A B : Type*} [Group K] [Group A] [Group B] [Finite K] [Finite A] [Finite B]
    (f : K →* A) (g : K →* B) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) : Function.Surjective (f.prod g) := by
  let R := (f.prod g).range
  let a : R →* A := (MonoidHom.fst A B).comp R.subtype
  let b : R →* B := (MonoidHom.snd A B).comp R.subtype
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨⟨(f y, g y), y, rfl⟩, rfl⟩
  have hb : Function.Surjective b := by
    intro x
    obtain ⟨y, rfl⟩ := hg x
    exact ⟨⟨(f y, g y), y, rfl⟩, rfl⟩
  have hdiv : Nat.card A * Nat.card B ∣ Nat.card R :=
    hcop.mul_dvd_of_dvd_of_dvd
      (Subgroup.card_dvd_of_surjective a ha) (Subgroup.card_dvd_of_surjective b hb)
  have hsur : Function.Surjective R.subtype :=
    (Subtype.val_injective.bijective_of_nat_card_le (by
      rw [Nat.card_prod]
      exact Nat.le_of_dvd (Nat.card_pos (α := R)) hdiv)).2
  intro x
  obtain ⟨⟨_, hx⟩, rfl⟩ := hsur x
  exact hx

private def kernelMap {U L G : Type*} [Group U] [Group L] [Group G]
    (c : U →* G) (f : L →* G) (a : U →* L) (h : f.comp a = c) : c.ker →* f.ker :=
  (a.comp c.ker.subtype).codRestrict f.ker (fun x => by
    change f (a x) = 1
    rw [← MonoidHom.comp_apply, h]
    exact x.property)

private theorem kernelMap_surjective {U L G : Type*} [Group U] [Group L] [Group G]
    (c : U →* G) (f : L →* G) (a : U →* L) (h : f.comp a = c)
    (ha : Function.Surjective a) : Function.Surjective (kernelMap c f a h) := by
  intro x
  obtain ⟨y, hy⟩ := ha x
  have hcy : y ∈ c.ker := by
    change c y = 1
    rw [← h, MonoidHom.comp_apply, hy]
    exact x.property
  exact ⟨⟨y, hcy⟩, Subtype.ext hy⟩

private theorem exists_universal_kernel_surjection
    {G E : Type*} [Group G] [Finite G] [Group.IsPerfect G] [Group E] [Finite E]
    (f : Cover E G) : ∃ a : schurMultiplier G →* f.toMonoidHom.ker,
      Function.Surjective a := by
  obtain ⟨a, ha, _⟩ := universalCover_isUniversal (G := G) E f
  let := f.isPerfect
  have hasur := surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f.toMonoidHom a (ha ▸ (universalCover G).surjective) f.ker_le_center
  exact ⟨kernelMap (universalProjection G) f.toMonoidHom a ha,
    kernelMap_surjective _ _ _ ha hasur⟩

/-- The natural projective kernel is cyclic of order four, for every allowed form. -/
def naturalKernelEquiv {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) (hF : Nat.card F = 9) (hc : ∀ x, J.conj x = x ^ 3) :
    (ProjectiveKernel.project J).ker ≃* Multiplicative (ZMod 4) := by
  let e := ProjectiveKernel.scalarKernelEquiv J hc
  letI : IsCyclic (ProjectiveKernel.project J).ker :=
    isCyclic_of_surjective e e.surjective
  apply mulEquivOfCyclicCardEq
  rw [ProjectiveKernel.card_project_kernel J hc (by simpa using hF)]
  simp

/-- The three missing primary estimates, together with the proved prime support,
force every actual covering kernel to have order dividing 36. -/
theorem kernel_card_dvd_thirtySix_of_primary_bounds
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F) (hF : Nat.card F = 9)
    {E : Type*} [Group E] [Finite E] (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    (h2 : ¬ 8 ∣ Nat.card f.toMonoidHom.ker)
    (h3 : ¬ 27 ∣ Nat.card f.toMonoidHom.ker)
    (h5 : ¬ 5 ∣ Nat.card f.toMonoidHom.ker) : Nat.card f.toMonoidHom.ker ∣ 36 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  have hpd : p ∣ Nat.card f.toMonoidHom.ker :=
    (dvd_pow_self p hk).trans hpk
  rcases UnitaryFourThree.OddCentralKernels.prime_dvd_kernel_eq_two_or_three_or_five
      J hF f hp hpd with rfl | rfl | rfl
  · have hk2 : k ≤ 2 := by
      by_contra hn
      exact h2 ((pow_dvd_pow 2 (by omega : 3 ≤ k)).trans hpk)
    exact (pow_dvd_pow 2 hk2).trans (by decide : 2 ^ 2 ∣ 36)
  · have hk3 : k ≤ 2 := by
      by_contra hn
      exact h3 ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hpk)
    exact (pow_dvd_pow 3 hk3).trans (by decide : 3 ^ 2 ∣ 36)
  · exact (h5 hpd).elim

/-- Conditional assembly: an actual exceptional cover supplies the elementary
three-part, while the natural SU cover supplies the cyclic four-part. The kernel
upper bound makes their combined universal-kernel map an isomorphism. -/
def multiplierEquiv_of_exceptional_cover_and_bound
    [Group.IsPerfect (UnitaryFourThree.Carrier 4)]
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (UnitaryFourThree.Carrier 4))
    (he : f.toMonoidHom.ker ≃* ExceptionalKernel)
    (hbound : Nat.card (schurMultiplier (UnitaryFourThree.Carrier 4)) ≤ 36) :
    schurMultiplier (UnitaryFourThree.Carrier 4) ≃* Kernel := by
  let J := UnitaryFourThree.form 4
  letI : Group.IsPerfect J.specialSubgroup := natural_isPerfect
  letI : Finite (GL (Fin 4) FiniteField.Nine) :=
    Finite.of_injective Units.val Units.val_injective
  let s : Cover J.specialSubgroup (UnitaryFourThree.Carrier 4) :=
    { toMonoidHom := ProjectiveKernel.project J
      surjective := ProjectiveKernel.project_surjective J
      isPerfect := inferInstance
      ker_le_center := ProjectiveKernel.project_kernel_le_center J }
  let a := Classical.choose (exists_universal_kernel_surjection f)
  have ha := Classical.choose_spec (exists_universal_kernel_surjection f)
  let b := Classical.choose (exists_universal_kernel_surjection s)
  have hb := Classical.choose_spec (exists_universal_kernel_surjection s)
  let a' := he.toMonoidHom.comp a
  let b' := (naturalKernelEquiv J FiniteField.Nine.natCard
    (UnitaryFourThree.form_conj_cube 4)).toMonoidHom.comp b
  have hab : Function.Surjective (a'.prod b') :=
    prod_surjective_of_coprime a' b' (he.surjective.comp ha)
      ((naturalKernelEquiv J FiniteField.Nine.natCard
        (UnitaryFourThree.form_conj_cube 4)).surjective.comp hb) (by
          norm_num [ExceptionalKernel, Nat.card_prod])
  exact MulEquiv.ofBijective (a'.prod b')
    (hab.bijective_of_nat_card_le (by simpa [Kernel, ExceptionalKernel, Nat.card_prod] using hbound))

universe u v w

/-- The arbitrary-field and arbitrary-form consumer of the independent primary
calculations. This is conditional until the exceptional cover and the two- and
three-primary bounds are constructed. -/
theorem exists_universal_cover_of_primary_data
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 4 F)
    (hF : Nat.card F = 9) (hc : ∀ x, J.conj x = x ^ 3)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (UnitaryFourThree.Carrier 4))
    (he : f.toMonoidHom.ker ≃* ExceptionalKernel)
    (h2 : ∀ {D : Type} [Group D] [Finite D]
      (g : Cover D (UnitaryFourThree.Carrier 4)), ¬ 8 ∣ Nat.card g.toMonoidHom.ker)
    (h3 : ∀ {D : Type} [Group D] [Finite D]
      (g : Cover D (UnitaryFourThree.Carrier 4)), ¬ 27 ∣ Nat.card g.toMonoidHom.ker)
    (h5 : ∀ {D : Type} [Group D] [Finite D]
      (g : Cover D (UnitaryFourThree.Carrier 4)), ¬ 5 ∣ Nat.card g.toMonoidHom.ker) :
    ∃ (U : Type u) (_ : Group U) (_ : Finite U) (_ : IsQuasisimple U),
      ∃ c : Covering U (ProjectiveSpecialUnitaryMatrixGroup J),
        Covering.IsUniversal.{u, u, w} c ∧ Nonempty (c.toMonoidHom.ker ≃* Kernel) := by
  obtain ⟨e⟩ := UnitaryFourThree.exists_model_equiv J hF hc
  let : IsQuasisimple (UnitaryFourThree.Carrier 4) := IsQuasisimple.of_mulEquiv e
  let c₀ := universalCover (UnitaryFourThree.Carrier 4)
  have hd : Nat.card (schurMultiplier (UnitaryFourThree.Carrier 4)) ∣ 36 :=
    kernel_card_dvd_thirtySix_of_primary_bounds (UnitaryFourThree.form 4)
      FiniteField.Nine.natCard c₀ (h2 c₀) (h3 c₀) (h5 c₀)
  let k := multiplierEquiv_of_exceptional_cover_and_bound f he
    (Nat.le_of_dvd (by decide : 0 < 36) hd)
  refine ⟨UniversalGroup (ProjectiveSpecialUnitaryMatrixGroup J), inferInstance,
    inferInstance, inferInstance, universalQuasisimpleCover _,
    universalQuasisimpleCover_isUniversal _, ?_⟩
  exact ⟨(schurMultiplierCongr e).trans k⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional
