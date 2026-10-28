module
public import Theory.Representation.Suzuki.SteinbergCoordinates
public import Theory.SpecificGroups.Suzuki.NormalizerInnerActors
/-!
# The full elementary actor on an ambient Suzuki Steinberg part

An elementary actor normalizing a Suzuki component induces inner automorphisms.
A single marking places them in the literal root subgroup, with kernel exactly
the original actor's component centralizer. The canonical Steinberg isotypic
part then has twisted regular coordinates with its actual multiplicity action.
Quadraticity bounds the root image by two. A centralizer kernel of order at
most 2048 bounds the full actor rank by twelve, so the terminal ratio bound
moves at most 24 dimensions. A nontrivial root shift moves at least 32.

Source: Aschbacher–Smith §13.6, printed pp.934–935. The bound 2048 accommodates
the J₄ row as well as the stronger M₂₃ and L₃(4) kernel bounds.
-/
public noncomputable section
open scoped MonoidAlgebra
open Module Representation Subgroup
open Representation.BinaryOffender.NaturalTensor
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

/-- Twisted regular coordinates for the full original normalizing actor. -/
theorem ambient_steinberg_coordinates
    {H W K : Type*} [Group H] [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K H W) (D A : Subgroup H) (hAD : A ≤ normalizer (D : Set H))
    (m : ℕ) (hm : 1 ≤ m) [Algebra (F m) K]
    (e : D ≃* SuzukiMatrixGroup m) (hA : ∀ a : A, a ^ 2 = 1) :
    ∃ (f : D ≃* SuzukiMatrixGroup m) (φ : A →* SuzukiRootSubgroup m),
      φ.ker = (centralizer (D : Set H)).subgroupOf A ∧
      let R : Representation K (SuzukiMatrixGroup m) W := ρ.comp (D.subtype.comp f.symm.toMonoidHom)
      let S := Subrepresentation.ofSubmodule' (isotypicComponent K[SuzukiMatrixGroup m]
        R.asModule (tensorRep m K Finset.univ).asModule)
      ∃ (n : ℕ) (τS : Representation K A S.toSubmodule)
        (c : S.toSubmodule ≃ₗ[K] (SuzukiRootSubgroup m → Fin n → K))
        (μ : Representation K A (Fin n → K)),
        (∀ a v, (τS a v : W) = ρ a v) ∧
        ∀ a v x, c (τS a v) x = μ a (c v ((φ a)⁻¹*x)) := by
  obtain ⟨f,φ,hφ,hker,_⟩ := suzuki_normalizer_root_coordinates D A hAD m hm e hA
  refine ⟨f,φ,hker,?_⟩
  let R : Representation K (SuzukiMatrixGroup m) W := ρ.comp (D.subtype.comp f.symm.toMonoidHom)
  let τ := ρ.comp A.subtype
  apply steinberg_isotypic_twisted_coordinates m hm R τ φ
  intro a d
  have he : (f.symm ((φ a : SuzukiMatrixGroup m) * d * (φ a : SuzukiMatrixGroup m)⁻¹) : H) =
      (a : H) * (f.symm d : H) * (a : H)⁻¹ := by
    have h := hφ a (f.symm d)
    rw [f.apply_symm_apply] at h
    have hh := congrArg (fun x => (f.symm x : H)) h
    simpa using hh.symm
  change ρ (a : H) * ρ (f.symm d : H) =
    ρ (f.symm ((φ a : SuzukiMatrixGroup m) * d * (φ a : SuzukiMatrixGroup m)⁻¹) : H) * ρ (a : H)
  rw [he,← map_mul,← map_mul]
  congr 1
  group


/-- A quadratic twisted coordinate action with kernel at most 2048 is trivial
under the original actor ratio bound. -/
theorem fixed_of_twisted_coordinates
    (m : ℕ) (hm : 1 ≤ m) {K A W : Type*} [Field K] [Group A]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {n : ℕ} (τ : Representation K A W)
    (c : W ≃ₗ[K] (SuzukiRootSubgroup m → Fin n → K))
    (μ : Representation K A (Fin n → K)) (φ : A →* SuzukiRootSubgroup m)
    (hc : ∀ a v x, c (τ a v) x = μ a (c v ((φ a)⁻¹*x)))
    (hinvol : ∀ a : A, a * a = 1)
    (hquad : ∀ a b v, τ a (τ b v - v) = τ b v - v)
    (hker : Nat.card φ.ker ≤ 2048)
    (hsmall : ∀ a, operatorFixedCodim (τ a) ≤ 2 * Nat.log 2 (Nat.card A)) :
    ∀ a, τ a = 1 := by
  classical
  let : Fintype (SuzukiRootSubgroup m) := Fintype.ofFinite _
  by_cases hn : n = 0
  · subst n
    have hs : Subsingleton W := c.injective.subsingleton
    exact fun a => Subsingleton.elim _ _
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  let σ := c.conjRingEquiv.toMonoidHom.comp τ
  have he (a : A) (v : W) : σ a (c v) = c (τ a v) := by
    change c (τ a (c.symm (c v))) = _
    rw [c.symm_apply_apply]
  have hs (a : A) (f : SuzukiRootSubgroup m → Fin n → K) (x : SuzukiRootSubgroup m) :
      σ a f x = μ a (f ((φ a)⁻¹*x)) := by
    obtain ⟨v,rfl⟩ := c.surjective f
    rw [he]
    exact hc a v x
  have hq (a b : A) (f : SuzukiRootSubgroup m → Fin n → K) :
      σ a (σ b f - f) = σ b f - f := by
    obtain ⟨v,rfl⟩ := c.surjective f
    rw [he,← map_sub,he,hquad]
  have hdim (a : A) : operatorFixedCodim (σ a) = operatorFixedCodim (τ a) :=
    (operatorFixedCodim_eq_of_equiv (τ a) (σ a) c (fun v => (he a v).symm)).symm
  have hr := TwistedRegular.quadratic_projection_card_le_two φ μ σ hs hq
  have hcard : Nat.card A ≤ 4096 := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
    nlinarith
  have hrank : Nat.log 2 (Nat.card A) ≤ 12 :=
    (Nat.log_mono_right (b := 2) hcard).trans (by decide)
  have hbound (a : A) : operatorFixedCodim (σ a) < 32 := by
    have hh := (hdim a).trans_le (hsmall a)
    omega
  have hsize : 64 ≤ Fintype.card (SuzukiRootSubgroup m) := by
    rw [Fintype.card_eq_nat_card, suzukiRootSubgroup_card m (by omega), ← pow_mul]
    change 2 ^ 6 ≤ 2 ^ ((2 * m + 1) * 2)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hmdim : 1 ≤ finrank K (Fin n → K) := Module.finrank_pos
  have hf (a : A) : σ a = 1 := by
    have hphi : φ a = 1 := by
      by_contra hne
      have hh := TwistedRegular.shift_dimension_le_twice_displacement φ μ σ hs a hne
        (by rw [← map_mul, hinvol, map_one])
      have hd := hbound a
      nlinarith
    have hmult (v : Fin n → K) : μ a v = v := by
      by_contra hne
      have hh := TwistedRegular.card_le_displacement_of_pure_multiplicity
        φ μ σ hs a hphi ⟨v,hne⟩
      have hd := hbound a
      omega
    apply LinearMap.ext
    intro f
    funext x
    rw [hs,hphi,inv_one,one_mul,hmult]
    rfl
  intro a
  apply LinearMap.ext
  intro v
  apply c.injective
  rw [← he,hf,Module.End.one_apply]
  rfl

/-- The actual ambient actor fixes the full canonical Steinberg isotypic part.
The kernel bound concerns its literal centralizer of the Suzuki component. -/
theorem ambient_steinberg_fixed
    {H W K : Type*} [Group H] [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K H W) (D A : Subgroup H) (hAD : A ≤ normalizer (D : Set H))
    (m : ℕ) (hm : 1 ≤ m) [Algebra (F m) K]
    (e : D ≃* SuzukiMatrixGroup m) (hA : ∀ a : A, a ^ 2 = 1)
    (hquad : ∀ (a b : A) v, ρ a (ρ b v - v) = ρ b v - v)
    (hker : Nat.card ((centralizer (D : Set H)).subgroupOf A) ≤ 2048)
    (hsmall : ∀ a : A, operatorFixedCodim (ρ a) ≤ 2 * Nat.log 2 (Nat.card A)) :
    ∃ f : D ≃* SuzukiMatrixGroup m,
      let R : Representation K (SuzukiMatrixGroup m) W :=
        ρ.comp (D.subtype.comp f.symm.toMonoidHom)
      let S := Subrepresentation.ofSubmodule' (isotypicComponent K[SuzukiMatrixGroup m]
        R.asModule (tensorRep m K Finset.univ).asModule)
      ∀ (a : A) (v : S.toSubmodule), ρ a v = v := by
  obtain ⟨f,φ,hφ,n,τS,c,μ,hτ,hc⟩ := ambient_steinberg_coordinates ρ D A hAD m hm e hA
  refine ⟨f,?_⟩
  let R : Representation K (SuzukiMatrixGroup m) W :=
    ρ.comp (D.subtype.comp f.symm.toMonoidHom)
  let S := Subrepresentation.ofSubmodule' (isotypicComponent K[SuzukiMatrixGroup m]
    R.asModule (tensorRep m K Finset.univ).asModule)
  have hq (a b : A) (v : S.toSubmodule) : τS a (τS b v-v) = τS b v-v := by
    apply Subtype.ext
    simpa only [hτ, Submodule.coe_sub] using hquad a b (v : W)
  have hd (a : A) : operatorFixedCodim (τS a) ≤ 2 * Nat.log 2 (Nat.card A) :=
    (operatorFixedCodim_le_of_injective (τS a) (ρ a) S.toSubmodule.subtype
      Subtype.val_injective (hτ a)).trans (hsmall a)
  have hf := fixed_of_twisted_coordinates m hm τS c μ φ hc
    (fun a => by simpa only [pow_two] using hA a) hq (hφ ▸ hker) hd
  change ∀ (a : A) (v : S.toSubmodule), ρ a v = v
  intro a v
  rw [← hτ,hf,Module.End.one_apply]
end Representation.SuzukiSmallDegree
