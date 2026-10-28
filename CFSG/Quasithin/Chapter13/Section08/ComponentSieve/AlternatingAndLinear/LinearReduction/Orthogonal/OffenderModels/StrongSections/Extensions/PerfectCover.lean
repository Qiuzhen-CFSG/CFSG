module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.CoreQuotients
public import Theory.Representation.BinaryPermutationNaturalCover

/-!
# Perfect central covers of the marked orthogonal module

A perfect central cover of the six-dimensional natural A₈-module is a quotient
of the augmentation core. The proved dual H¹ dimension identifies that core
with the universal cover. Uniqueness of maps from a perfect module to a central
kernel promotes the comparison to the original marked S₈-action.

This constructs the actual natural-or-core equivalence, bounds the central
kernel by one dimension, and excludes both Full and Deleted using their
nonzero trivial quotients. No classification or indecomposability is assumed.
Constructing the central-cover map from a single noncentral factor remains a
separate prerequisite of the section-recognition argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.3.3 (printed p.84), I.1.5–6 (printed p.408),
and the extension deduction in 13.8.25 (printed p.960, PDF p.977).
-/

@[expose] public section

open Representation Representation.BinaryOffender Representation.OneCohomology BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

set_option maxHeartbeats 800000 in
private lemma universal_core_map :
    ∃ b : (universalAction (alternatingNaturalRepresentation (Fin 8)).dual).dual.IntertwiningMap
        (alternatingCoreRepresentation (Fin 8)),
      Function.Bijective b ∧ ∀ u,
        coreToNatural (Fin 8) (b u) = universalCoverProjection (alternatingNaturalRepresentation (Fin 8)) u := by
  obtain ⟨b, hb, hbq⟩ := exists_universalCover_quotient
    (alternatingCoreProjection (Fin 8)) alternatingEight_coreProjection_isCover
  have hu := (universalCoverProjection (alternatingNaturalRepresentation (Fin 8))).toLinearMap.finrank_range_add_finrank_ker
  have hsurU : Function.Surjective (universalCoverProjection (alternatingNaturalRepresentation (Fin 8))) := by
    intro v
    obtain ⟨w, rfl⟩ := coreToNatural_surjective v
    obtain ⟨x, rfl⟩ := hb w
    exact ⟨x, (hbq x).symm⟩
  rw [LinearMap.range_eq_top.mpr hsurU, finrank_top,
    finrank_ker_universalCoverProjection, alternatingEight_natural_dual_finrank_H1,
    finrank_natural_even (Fin 8) (by decide)] at hu
  have hbfin : Module.finrank (ZMod 2) (Module.Dual (ZMod 2)
      (cocycles (alternatingNaturalRepresentation (Fin 8)).dual)) =
      Module.finrank (ZMod 2) (core (Fin 8)) := by
    rw [finrank_core]
    simpa only [Fintype.card_fin] using hu.symm
  exact ⟨b, ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hbfin).mpr hb, hb⟩, hbq⟩

private lemma core_quotient_of_alternating_cover
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 8)) U)
    (P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 8))) (hP : IsCover P) :
    ∃ f : core (Fin 8) →ₗ[ZMod 2] U, Function.Surjective f ∧
      (∀ g : alternatingGroup (Fin 8), ∀ v,
        f (coreRepresentation (Fin 8) g.val v) = σ g (f v)) ∧
      ∀ v, P (f v) = coreToNatural (Fin 8) v := by
  obtain ⟨b, hb, hbq⟩ := universal_core_map
  obtain ⟨c, hc, hcp⟩ := exists_universalCover_quotient P hP
  let B := LinearEquiv.ofBijective b.toLinearMap hb
  let f : core (Fin 8) →ₗ[ZMod 2] U := c.toLinearMap.comp B.symm.toLinearMap
  have hf : Function.Surjective f := hc.comp B.symm.surjective
  have hpf (v : core (Fin 8)) : P (f v) = coreToNatural (Fin 8) v := by
    change P (c (B.symm v)) = _
    rw [hcp, ← hbq]
    change coreToNatural (Fin 8) (B (B.symm v)) = _
    rw [B.apply_symm_apply]
  have hfa (g : alternatingGroup (Fin 8)) (v : core (Fin 8)) :
      f (coreRepresentation (Fin 8) g.val v) = σ g (f v) := by
    have he : B.symm (coreRepresentation (Fin 8) g.val v) =
        (universalAction (alternatingNaturalRepresentation (Fin 8)).dual).dual g (B.symm v) := by
      apply B.injective
      rw [B.apply_symm_apply]
      exact (congrArg (coreRepresentation (Fin 8) g.val) (B.apply_symm_apply v)).symm.trans
        (LinearMap.congr_fun (b.isIntertwining' g) (B.symm v)).symm
    change c (B.symm _) = σ g (c (B.symm v))
    rw [he]
    exact LinearMap.congr_fun (c.isIntertwining' g) (B.symm v)
  exact ⟨f, hf, hfa, hpf⟩

omit [FiniteDimensional (ZMod 2) U] in
private lemma core_map_equivariant
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* Perm) (K : Subgroup H)
    (a : alternatingGroup (Fin 8) →* H)
    (ha : ∀ k, a k ∈ K) (hae : ∀ k, eH (a k) = k.val)
    (p : U →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 8) (eH g) (p u))
    (hker : p.ker ≤ fixedSpace ρ K)
    (f : core (Fin 8) →ₗ[ZMod 2] U)
    (hpf : ∀ v, p (f v) = coreToNatural (Fin 8) v)
    (hfa : ∀ g : alternatingGroup (Fin 8), ∀ v,
      f (coreRepresentation (Fin 8) g.val v) = ρ (a g) (f v))
    (g : H) (v : core (Fin 8)) :
    f (coreRepresentation (Fin 8) (eH g) v) = ρ g (f v) := by
  let d : core (Fin 8) →ₗ[ZMod 2] U :=
    f.comp (coreRepresentation (Fin 8) (eH g)) - (ρ g).comp f
  have hdker (v : core (Fin 8)) : d v ∈ p.ker := by
    change p (f (coreRepresentation (Fin 8) (eH g) v) - ρ g (f v)) = 0
    rw [map_sub, hpf, hp, hpf, coreToNatural_equivariant, sub_self]
  have hd (k : alternatingGroup (Fin 8)) (v : core (Fin 8)) :
      d (alternatingCoreRepresentation (Fin 8) k v) = d v := by
    let l : alternatingGroup (Fin 8) := ⟨eH g * k.val * (eH g)⁻¹,
      (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem _ k.property _⟩
    have hal : a l = g * a k * g⁻¹ := by
      apply eH.injective
      simp only [map_mul, map_inv, hae]
      rfl
    have he : coreRepresentation (Fin 8) (eH g) (coreRepresentation (Fin 8) k.val v) =
        coreRepresentation (Fin 8) l.val (coreRepresentation (Fin 8) (eH g) v) := by
      simp [l, ← Module.End.mul_apply, ← map_mul]
    change f (coreRepresentation (Fin 8) (eH g) (coreRepresentation (Fin 8) k.val v)) -
      ρ g (f (coreRepresentation (Fin 8) k.val v)) = d v
    rw [he, hfa, hfa]
    have hh : ρ (a l) (ρ g (f v)) = ρ g (ρ (a k) (f v)) := by
      rw [hal]
      simp [← Module.End.mul_apply, ← map_mul]
    rw [← hh, ← map_sub]
    exact hker (hdker v) ⟨a l, ha l⟩
  have hz : Coinvariants.ker (alternatingCoreRepresentation (Fin 8)) ≤ d.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, v⟩, rfl⟩
    change d (_ - _) = 0
    rw [map_sub, hd, sub_self]
  rw [alternatingEight_core_generated] at hz
  exact sub_eq_zero.mp (hz (Submodule.mem_top : v ∈ ⊤))

/-- A perfect central extension of the marked natural module is an equivariant
quotient of the augmentation core, over the same natural projection. -/
lemma core_surjection_of_central_cover (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (p : U →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 8) (eH g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    ∃ f : core (Fin 8) →ₗ[ZMod 2] U, Function.Surjective f ∧
      (∀ g v, f (coreRepresentation (Fin 8) (eH g) v) = ρ g (f v)) ∧
      ∀ v, p (f v) = coreToNatural (Fin 8) v := by
  let a : alternatingGroup (Fin 8) →* H :=
    eH.symm.toMonoidHom.comp (alternatingGroup (Fin 8)).subtype
  have ha (g : alternatingGroup (Fin 8)) : a g ∈ K := by
    have : (g : Perm) ∈ K.map eH.toMonoidHom := hK.symm ▸ g.property
    obtain ⟨k, hk, he⟩ := this
    have he' : k = a g := eH.injective (he.trans (eH.apply_symm_apply _).symm)
    exact he' ▸ hk
  have hag (k : H) (hk : k ∈ K) : ∃ g, a g = k := by
    let g : alternatingGroup (Fin 8) := ⟨eH k, hK ▸ Subgroup.mem_map_of_mem _ hk⟩
    exact ⟨g, eH.symm_apply_apply k⟩
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 8)) U := ρ.comp a
  let P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 8)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g u => by
      simpa [σ, a] using hp (a g) u)
  have hcoin : Coinvariants.ker σ = subspaceCommutator ρ ⊤ K := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, u⟩, rfl⟩
      exact Submodule.subset_span ⟨a g, ha g, u, Submodule.mem_top, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, u, _, rfl⟩
      obtain ⟨g, rfl⟩ := hag k hk
      exact Coinvariants.sub_mem_ker g u
  have hP : IsCover P := ⟨hsur, fun u hu g => hker hu ⟨a g, ha g⟩, hcoin.trans hgen⟩
  obtain ⟨f, hf, hfa, hpf⟩ := core_quotient_of_alternating_cover σ P hP
  exact ⟨f, hf, core_map_equivariant ρ eH K a ha
    (fun k => eH.apply_symm_apply k.val) p hp hker f hpf hfa, hpf⟩

/-- The other permutation extensions are excluded: a perfect central cover
is the natural module or its augmentation cover, equivariantly for H. -/
lemma naturalOrCover_of_central_cover (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (p : U →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 8) (eH g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) : IsEightNaturalOrCover ρ eH := by
  obtain ⟨f, hf, hfh, hpf⟩ := core_surjection_of_central_cover ρ eH K hK p hp hsur hker hgen
  apply TransvectionSections.naturalOrCover_of_core_surjection ρ eH f hfh hf
  intro hz
  have hzero : ∀ v : natural (Fin 8), v = 0 := by
    intro v
    obtain ⟨w, rfl⟩ := coreToNatural_surjective v
    rw [← hpf]
    simp [hz]
  have : Subsingleton (natural (Fin 8)) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have he := finrank_natural_even (Fin 8) (by decide)
  rw [Module.finrank_zero_of_subsingleton] at he
  norm_num at he
private lemma binary_line_fixed (ρ : Representation (ZMod 2) H U)
    (hdim : Module.finrank (ZMod 2) U ≤ 1) (g : H) (v : U) : ρ g v = v := by
  obtain ⟨w, hw⟩ := finrank_le_one_iff.mp hdim
  have hg : ρ g w = w := by
    obtain ⟨c, hc⟩ := hw (ρ g w)
    have hc' : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hc' with rfl | rfl
    · have hz : ρ g w = 0 := by simpa using hc.symm
      have hwz : w = 0 := by
        have := congrArg (ρ g⁻¹) hz
        simpa [← Module.End.mul_apply, ← map_mul] using this
      simp [hwz]
    · simpa using hc.symm
  obtain ⟨c, rfl⟩ := hw v
  rw [map_smul, hg]

/-- The kernel of a perfect central cover of the six-dimensional natural
module has dimension at most one and is fixed by the whole symmetric group. -/
lemma central_cover_kernel_control (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (p : U →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 8) (eH g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    Module.finrank (ZMod 2) p.ker ≤ 1 ∧ p.ker ≤ fixedSpace ρ ⊤ := by
  obtain ⟨f, hf, _, _⟩ := core_surjection_of_central_cover ρ eH K hK p hp hsur hker hgen
  have hdim := LinearMap.finrank_le_finrank_of_surjective (f := f) hf
  rw [finrank_core, Fintype.card_fin] at hdim
  have hnull := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsur, finrank_top,
    finrank_natural_even (Fin 8) (by decide), Fintype.card_fin] at hnull
  have hkdim : Module.finrank (ZMod 2) p.ker ≤ 1 := by omega
  let S : Subrepresentation ρ := ⟨p.ker, by
    intro g v hv
    change p (ρ g v) = 0
    rw [hp, show p v = 0 from hv, map_zero]⟩
  refine ⟨hkdim, ?_⟩
  intro v hv g
  exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hkdim g.val ⟨v, hv⟩)

/-- Construct the literal commutator model from a central-cover map on that
subrepresentation. No abstract isomorphism replaces its inclusion. -/
lemma commutator_model_of_central_cover (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (J : Subrepresentation ρ)
    (hJ : J.toSubmodule = subspaceCommutator ρ ⊤ K)
    (p : J.toSubmodule →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ g u, p (J.toRepresentation g u) = naturalRepresentation (Fin 8) (eH g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace J.toRepresentation K)
    (hgen : subspaceCommutator J.toRepresentation ⊤ K = ⊤) :
    IsCommutatorNaturalOrCover ρ K eH :=
  ⟨J, hJ, naturalOrCover_of_central_cover J.toRepresentation eH K hK p hp hsur hker hgen⟩

omit [FiniteDimensional (ZMod 2) U] in
private lemma invariant_map_eq_zero (ρ : Representation (ZMod 2) H U) (K : Subgroup H)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) (f : U →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ k ∈ K, ∀ u, f (ρ k u) = f u) : f = 0 := by
  have hle : subspaceCommutator ρ ⊤ K ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, u, _, rfl⟩
    change f (ρ k u - u) = 0
    rw [map_sub, hf k hk, sub_self]
  rw [hgen] at hle
  ext u
  exact hle (Submodule.mem_top : u ∈ ⊤)

omit [FiniteDimensional (ZMod 2) U] in
/-- The full permutation module has a nonzero trivial quotient, and so
cannot be the commutator-generated module in the extension step. -/
lemma not_full_of_generated (ρ : Representation (ZMod 2) H U) (K : Subgroup H)
    (eH : H ≃* Perm) (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    ¬ ∃ e : U ≃ₗ[ZMod 2] Full (Fin 8),
      ∀ g u, e (ρ g u) = representation (Fin 8) (eH g) (e u) := by
  rintro ⟨e, he⟩
  let f := (augmentation (Fin 8)).comp e.toLinearMap
  have hf : f = 0 := invariant_map_eq_zero ρ K hgen f (by
    intro k _ u
    change augmentation (Fin 8) (e (ρ k u)) = augmentation (Fin 8) (e u)
    rw [he, augmentation_permute])
  have h := LinearMap.congr_fun hf (e.symm (Pi.single 0 1))
  norm_num [f, augmentation] at h

omit [FiniteDimensional (ZMod 2) U] in
/-- In even degree augmentation descends to the deleted module. Its nonzero
trivial quotient excludes Deleted from a commutator-generated extension. -/
lemma not_deleted_of_generated (ρ : Representation (ZMod 2) H U) (K : Subgroup H)
    (eH : H ≃* Perm) (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    ¬ ∃ e : U ≃ₗ[ZMod 2] Deleted (Fin 8),
      ∀ g u, e (ρ g u) = deletedRepresentation (Fin 8) (eH g) (e u) := by
  rintro ⟨e, he⟩
  let a : Deleted (Fin 8) →ₗ[ZMod 2] ZMod 2 :=
    (constants (Fin 8)).liftQ (augmentation (Fin 8))
      ((constants_le_core_iff (Fin 8)).mpr (by decide))
  have ha (g : Perm) (v : Deleted (Fin 8)) :
      a (deletedRepresentation (Fin 8) g v) = a v := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact augmentation_permute (Fin 8) g v
  let f := a.comp e.toLinearMap
  have hf : f = 0 := invariant_map_eq_zero ρ K hgen f (by
    intro k _ u
    change a (e (ρ k u)) = a (e u)
    rw [he, ha])
  have h := LinearMap.congr_fun hf (e.symm ((constants (Fin 8)).mkQ (Pi.single 0 1)))
  norm_num [f, a, augmentation] at h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions
