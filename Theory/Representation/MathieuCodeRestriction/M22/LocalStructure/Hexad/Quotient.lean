module

public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Fixed spaces after quotienting by a fixed subspace

A surjective equivariant linear map whose kernel is fixed preserves fixed
spaces exactly whenever it preserves fixed codimension. Applying this to
each nonidentity actor gives the same result for every subgroup of the
specified kernel, and transports the actual span of element fixed spaces.

These are the linear algebra steps in the restriction from the Mathieu
cocode to its quotient by the distinguished pair line. The numerical
codimension equality must be supplied; equivariance alone is insufficient.

Source: Aschbacher--Smith, H.15.2, printed p.399 (1 March 2004 manuscript).
-/

public section
open Representation.BinaryOffender
namespace MathieuCode.HexadTransfer
noncomputable section
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) W] in
theorem finrank_map_add_ker (f : V →ₗ[ZMod 2] W) (U : Submodule (ZMod 2) V)
    (hk : f.ker ≤ U) :
    Module.finrank (ZMod 2) (U.map f) + Module.finrank (ZMod 2) f.ker =
      Module.finrank (ZMod 2) U := by
  have h := (f.comp U.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
    (Submodule.comapSubtypeEquivOfLe hk).finrank_eq] at h
  exact h

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W] in
theorem fixedSpace_map_le (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (A : Subgroup G) :
    (fixedSpace ρ A).map f ≤ fixedSpace σ A := by
  rintro _ ⟨v, hv, rfl⟩ g
  change σ g.val (f v) = f v
  rw [← he]
  exact congrArg f (hv g)

theorem fixedSpace_map_eq_of_codim (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (hs : Function.Surjective f) (he : ∀ g v, f (ρ g v) = σ g (f v))
    (A : Subgroup G) (hk : f.ker ≤ fixedSpace ρ A)
    (hd : fixedCodim ρ A = fixedCodim σ A) :
    (fixedSpace ρ A).map f = fixedSpace σ A := by
  apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_map_le ρ σ f he A)
  have h1 := finrank_map_add_ker f (fixedSpace ρ A) hk
  have h2 := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h2
  have h3 := fixedCodim_add_finrank ρ A
  have h4 := fixedCodim_add_finrank σ A
  omega

theorem fixedSpace_comap_eq_of_codim (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (hs : Function.Surjective f) (he : ∀ g v, f (ρ g v) = σ g (f v))
    (A : Subgroup G) (hk : f.ker ≤ fixedSpace ρ A)
    (hd : fixedCodim ρ A = fixedCodim σ A) :
    (fixedSpace σ A).comap f = fixedSpace ρ A := by
  rw [← fixedSpace_map_eq_of_codim ρ σ f hs he A hk hd,
    Submodule.comap_map_eq, sup_eq_left.mpr hk]

theorem fixedSpace_comap_eq_of_element_codim (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (hs : Function.Surjective f) (he : ∀ g v, f (ρ g v) = σ g (f v))
    (K : Subgroup G) (hk : f.ker ≤ fixedSpace ρ K)
    (hd : ∀ a ∈ K, a ≠ 1 →
      fixedCodim ρ (Subgroup.zpowers a) = fixedCodim σ (Subgroup.zpowers a))
    (A : Subgroup G) (hA : A ≤ K) :
    (fixedSpace σ A).comap f = fixedSpace ρ A := by
  ext v
  constructor
  · intro hv g
    by_cases hg : g.val = 1
    · change ρ g.val v = v
      rw [hg, map_one, Module.End.one_apply]
    have hker : f.ker ≤ fixedSpace ρ (Subgroup.zpowers g.val) := by
      intro u hu
      exact (mem_fixedSpace_zpowers_iff ρ g.val u).mpr (hk hu ⟨g.val, hA g.property⟩)
    have hfix : f v ∈ fixedSpace σ (Subgroup.zpowers g.val) :=
      (mem_fixedSpace_zpowers_iff σ g.val (f v)).mpr (hv g)
    have hv' : v ∈ (fixedSpace σ (Subgroup.zpowers g.val)).comap f := hfix
    rw [fixedSpace_comap_eq_of_codim ρ σ f hs he _ hker (hd _ (hA g.property) hg)] at hv'
    exact (mem_fixedSpace_zpowers_iff ρ g.val v).mp hv'
  · intro hv g
    change σ g.val (f v) = f v
    rw [← he]
    exact congrArg f (hv g)

theorem fixedSpace_map_eq_of_element_codim (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (hs : Function.Surjective f) (he : ∀ g v, f (ρ g v) = σ g (f v))
    (K : Subgroup G) (hk : f.ker ≤ fixedSpace ρ K)
    (hd : ∀ a ∈ K, a ≠ 1 →
      fixedCodim ρ (Subgroup.zpowers a) = fixedCodim σ (Subgroup.zpowers a))
    (A : Subgroup G) (hA : A ≤ K) :
    (fixedSpace ρ A).map f = fixedSpace σ A := by
  rw [← fixedSpace_comap_eq_of_element_codim ρ σ f hs he K hk hd A hA,
    Submodule.map_comap_eq, LinearMap.range_eq_top.mpr hs, top_inf_eq]

theorem fixedSpaceSpan_map_eq_of_element_codim (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (hs : Function.Surjective f) (he : ∀ g v, f (ρ g v) = σ g (f v))
    (K : Subgroup G) (hk : f.ker ≤ fixedSpace ρ K)
    (hd : ∀ a ∈ K, a ≠ 1 →
      fixedCodim ρ (Subgroup.zpowers a) = fixedCodim σ (Subgroup.zpowers a)) :
    (fixedSpaceSpan ρ K).map f = fixedSpaceSpan σ K := by
  simp only [fixedSpaceSpan, Submodule.map_iSup]
  apply iSup_congr
  intro a
  apply iSup_congr
  intro ha
  apply iSup_congr
  intro ha1
  apply fixedSpace_map_eq_of_codim ρ σ f hs he _ _ (hd a ha ha1)
  intro v hv
  exact (mem_fixedSpace_zpowers_iff ρ a v).mpr (hk hv ⟨a, ha⟩)
end
end MathieuCode.HexadTransfer
